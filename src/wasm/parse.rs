//! Wasm binary parsing via wasmparser.

use crate::forward::SymMachine;
use crate::goal::MachineState;
use crate::semantics::SemOp;
use crate::wasm::segment::StraightSegment;
use std::fs;
use std::path::Path;
use wasmparser::{FuncType, Operator, Parser, Payload, ValType};

#[derive(Clone, Debug)]
pub struct WasmModuleInfo {
    pub segments: Vec<StraightSegment>,
}

pub fn parse_wasm_file(path: &Path) -> Result<WasmModuleInfo, String> {
    let bytes = fs::read(path).map_err(|e| format!("read {}: {e}", path.display()))?;
    parse_wasm_bytes(&bytes)
}

pub fn parse_wasm_bytes(bytes: &[u8]) -> Result<WasmModuleInfo, String> {
    let mut types: Vec<FuncType> = Vec::new();
    let mut function_type_indices: Vec<u32> = Vec::new();
    let mut segments = Vec::new();
    let mut func_index = 0u32;

    for payload in Parser::new(0).parse_all(bytes) {
        let payload = payload.map_err(|e| format!("wasm parse error: {e}"))?;
        match payload {
            Payload::TypeSection(reader) => {
                for group in reader {
                    let group = group.map_err(|e| format!("type section: {e}"))?;
                    for subty in group.types() {
                        types.push(subty.composite_type.unwrap_func().clone());
                    }
                }
            }
            Payload::FunctionSection(reader) => {
                function_type_indices = reader
                    .into_iter()
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|e| format!("function section: {e}"))?;
            }
            Payload::CodeSectionEntry(body) => {
                let type_idx = function_type_indices
                    .get(func_index as usize)
                    .copied()
                    .ok_or_else(|| format!("missing type for func {func_index}"))?;
                let func_type = types
                    .get(type_idx as usize)
                    .ok_or_else(|| format!("missing type {type_idx}"))?;
                let num_params = func_type.params().len() as u32;
                let total_locals = num_params + count_declared_locals(&body)?;
                extract_from_body(func_index, num_params, total_locals, &body, &mut segments)?;
                func_index += 1;
            }
            _ => {}
        }
    }

    Ok(WasmModuleInfo { segments })
}

fn count_declared_locals(body: &wasmparser::FunctionBody<'_>) -> Result<u32, String> {
    let mut extra = 0u32;
    for entry in body
        .get_locals_reader()
        .map_err(|e| format!("locals reader: {e}"))?
    {
        let (count, ty) = entry.map_err(|e| format!("locals entry: {e}"))?;
        if ty != ValType::I32 {
            return Err(format!("only i32 locals supported, got {ty:?}"));
        }
        extra = extra.saturating_add(count);
    }
    Ok(extra)
}

fn extract_from_body(
    func_index: u32,
    num_params: u32,
    total_locals: u32,
    body: &wasmparser::FunctionBody<'_>,
    out: &mut Vec<StraightSegment>,
) -> Result<(), String> {
    let mut machine = SymMachine::function_entry(num_params, total_locals);
    let mut ops = Vec::new();
    let mut segment_init = machine.to_init_state();
    let mut segment_index = 0usize;
    let mut collecting = true;
    let mut skip_depth = 0u32;

    let op_reader = body
        .get_operators_reader()
        .map_err(|e| format!("func {func_index} operators: {e}"))?;
    let operators = op_reader
        .into_iter()
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| format!("func {func_index} operator: {e}"))?;

    for op in operators {
        if skip_depth > 0 {
            if matches!(op, Operator::End) {
                skip_depth -= 1;
            } else if matches!(op, Operator::Loop { .. }) {
                skip_depth += 1;
            }
            continue;
        }

        match classify_operator(&op) {
            OpClass::Supported(sem) => {
                if !collecting {
                    continue;
                }
                machine
                    .exec(&sem)
                    .map_err(|e| format!("func {func_index} forward exec {sem:?}: {e:?}"))?;
                ops.push(sem);
            }
            OpClass::Structural => {}
            OpClass::PopStack => {
                if !collecting {
                    continue;
                }
                machine
                    .pop()
                    .map_err(|e| format!("func {func_index} drop: {e:?}"))?;
            }
            OpClass::BreakSegment => {
                flush_segment(
                    func_index,
                    &mut segment_index,
                    &mut ops,
                    &segment_init,
                    &machine,
                    out,
                );
                collecting = match &op {
                    Operator::Return => false,
                    Operator::Br { .. } => false,
                    Operator::BrIf { .. } => {
                        machine.pop().map_err(|e| format!("br_if pop: {e:?}"))?;
                        segment_init = machine.to_init_state();
                        true
                    }
                    Operator::If { .. } => {
                        machine.pop().map_err(|e| format!("if pop: {e:?}"))?;
                        segment_init = machine.to_init_state();
                        true
                    }
                    _ => false,
                };
            }
            OpClass::SkipLoopBody => {
                flush_segment(
                    func_index,
                    &mut segment_index,
                    &mut ops,
                    &segment_init,
                    &machine,
                    out,
                );
                skip_depth = 1;
                segment_init = machine.to_init_state();
                collecting = true;
            }
            OpClass::Unsupported => {
                flush_segment(
                    func_index,
                    &mut segment_index,
                    &mut ops,
                    &segment_init,
                    &machine,
                    out,
                );
                collecting = false;
            }
        }
    }

    if collecting {
        flush_segment(
            func_index,
            &mut segment_index,
            &mut ops,
            &segment_init,
            &machine,
            out,
        );
    }

    Ok(())
}

fn flush_segment(
    func_index: u32,
    segment_index: &mut usize,
    ops: &mut Vec<SemOp>,
    init: &MachineState,
    machine: &SymMachine,
    out: &mut Vec<StraightSegment>,
) {
    if ops.is_empty() {
        return;
    }
    let fin = machine.to_fin_state();
    if !init.validate_bounds() || !fin.validate_bounds() {
        ops.clear();
        return;
    }
    out.push(StraightSegment {
        func_index,
        segment_index: *segment_index,
        ops: ops.clone(),
        init: init.clone(),
        fin,
    });
    *segment_index += 1;
    ops.clear();
}

enum OpClass {
    Supported(SemOp),
    Structural,
    PopStack,
    BreakSegment,
    SkipLoopBody,
    Unsupported,
}

fn classify_operator(op: &Operator<'_>) -> OpClass {
    match op {
        Operator::I32Const { value } => OpClass::Supported(SemOp::I32Const(*value)),
        Operator::I32Add => OpClass::Supported(SemOp::I32Add),
        Operator::I32Mul => OpClass::Supported(SemOp::I32Mul),
        Operator::I32DivU => OpClass::Supported(SemOp::I32DivU),
        Operator::I32DivS => OpClass::Supported(SemOp::I32DivS),
        Operator::I32Shl => OpClass::Supported(SemOp::I32Shl),
        Operator::LocalGet { local_index } => {
            OpClass::Supported(SemOp::LocalGet(*local_index))
        }
        Operator::LocalSet { local_index } => {
            OpClass::Supported(SemOp::LocalSet(*local_index))
        }
        Operator::LocalTee { local_index } => {
            OpClass::Supported(SemOp::LocalTee(*local_index))
        }
        Operator::Drop => OpClass::PopStack,
        Operator::Nop | Operator::End | Operator::Block { .. } | Operator::Else => {
            OpClass::Structural
        }
        Operator::Loop { .. } => OpClass::SkipLoopBody,
        Operator::Br { .. } | Operator::BrIf { .. } | Operator::BrTable { .. } => {
            OpClass::BreakSegment
        }
        Operator::Return | Operator::If { .. } => OpClass::BreakSegment,
        Operator::Call { .. }
        | Operator::CallIndirect { .. }
        | Operator::Unreachable
        | Operator::Select => OpClass::Unsupported,
        _ => OpClass::Unsupported,
    }
}

pub fn extract_segments(info: &WasmModuleInfo) -> &[StraightSegment] {
    &info.segments
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::search::format_ops;

    fn wat_to_wasm(wat: &str) -> Vec<u8> {
        wat::parse_str(wat).expect("wat parse")
    }

    #[test]
    fn straight_line_function_yields_one_segment() {
        let wasm = wat_to_wasm(
            r#"(module
                (func (param i32) (result i32)
                  local.get 0
                  i32.const 1
                  i32.add
                  i32.const 4
                  i32.mul
                )
            )"#,
        );
        let info = parse_wasm_bytes(&wasm).expect("parse");
        assert_eq!(info.segments.len(), 1);
        assert_eq!(info.segments[0].ops.len(), 5);
    }

    #[test]
    fn loop_splits_segments() {
        let wasm = wat_to_wasm(
            r#"(module
                (func (param i32) (result i32)
                  local.get 0
                  i32.const 1
                  i32.add
                  (loop (result i32)
                    local.get 0
                    i32.const 1
                    i32.add
                    br_if 0 (local.get 0)
                  )
                  i32.const 0
                )
            )"#,
        );
        let info = parse_wasm_bytes(&wasm).expect("parse");
        assert_eq!(info.segments.len(), 2, "segments: {:?}", info.segments.iter().map(|s| format_ops(&s.ops)).collect::<Vec<_>>());
        assert_eq!(info.segments[0].ops.len(), 3);
        assert_eq!(info.segments[1].ops.len(), 1);
    }

    #[test]
    fn br_ends_segment_before_branch() {
        let wasm = wat_to_wasm(
            r#"(module
                (func (param i32)
                  local.get 0
                  i32.const 1
                  i32.add
                  br 0
                  i32.const 0
                  drop
                )
            )"#,
        );
        let info = parse_wasm_bytes(&wasm).expect("parse");
        assert_eq!(info.segments.len(), 1);
        assert_eq!(info.segments[0].ops.len(), 3);
    }
}
