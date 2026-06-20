//! Wasm binary parsing via wasmparser.

use crate::semantics::SemOp;
use crate::sym::{ForwardError, SymMachine, SymState};
use crate::wasm::{SegmentBounds, StraightSegment};
use crate::wasm::stack_analysis::{operator_stack_effect, stack_bounds_ops, stack_bounds_operators};
use std::collections::HashSet;
use std::fs;
use std::io::{self, Write};
use std::path::Path;
use wasmparser::{FuncType, Operator, Parser, Payload, ValType};

#[derive(Clone, Debug)]
pub struct WasmModuleInfo {
    pub segments: Vec<StraightSegment>,
    pub warnings: Vec<String>,
}

pub fn parse_wasm_file(path: &Path) -> Result<WasmModuleInfo, String> {
    let bytes = read_wasm_bytes(path)?;
    parse_wasm_bytes(&bytes)
}

fn read_wasm_bytes(path: &Path) -> Result<Vec<u8>, String> {
    let ext = path.extension().and_then(|e| e.to_str());
    if ext == Some("wat") {
        let text = fs::read_to_string(path).map_err(|e| format!("read {}: {e}", path.display()))?;
        wat::parse_str(&text).map_err(|e| format!("parse wat {}: {e}", path.display()))
    } else {
        fs::read(path).map_err(|e| format!("read {}: {e}", path.display()))
    }
}

pub fn parse_wasm_bytes(bytes: &[u8]) -> Result<WasmModuleInfo, String> {
    let mut types: Vec<FuncType> = Vec::new();
    let mut function_type_indices: Vec<u32> = Vec::new();
    let mut segments = Vec::new();
    let mut warnings = Vec::new();
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
                let declared = count_declared_locals(&body)?;
                let total_locals = num_params + declared;
                extract_from_body(
                    func_index,
                    num_params,
                    total_locals,
                    &body,
                    &mut segments,
                    &mut warnings,
                )?;
                func_index += 1;
            }
            _ => {}
        }
    }

    Ok(WasmModuleInfo { segments, warnings })
}

pub fn print_input_summary(path: &Path, info: &WasmModuleInfo) {
    let total_instr: usize = info.segments.iter().map(|s| s.original_len()).sum();
    let funcs: HashSet<_> = info.segments.iter().map(|s| s.func_index).collect();
    println!("=== Input: {} ===", path.display());
    println!("  functions with segments: {}", funcs.len());
    println!("  straight-line segments: {}", info.segments.len());
    println!("  total instructions: {total_instr}");
    if !info.warnings.is_empty() {
        println!("  parse warnings: {}", info.warnings.len());
    }
    println!();
    let _ = io::stdout().flush();
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

fn is_block_begin(op: &Operator<'_>) -> bool {
    matches!(
        op,
        Operator::Block { .. }
            | Operator::Loop { .. }
            | Operator::If { .. }
            | Operator::Else
            | Operator::Br { .. }
            | Operator::BrIf { .. }
            | Operator::BrTable { .. }
            | Operator::CallIndirect { .. }
    )
}

fn is_block_end(op: &Operator<'_>) -> bool {
    matches!(op, Operator::End | Operator::Unreachable | Operator::Return)
}

fn blocks_from_operators<'a>(ops: &'a [Operator<'a>]) -> Vec<Vec<Operator<'a>>> {
    let mut blocks = Vec::new();
    let mut current = Vec::new();
    for op in ops {
        if is_block_begin(op) {
            blocks.push(current);
            current = vec![op.clone()];
        } else if is_block_end(op) {
            current.push(op.clone());
            blocks.push(current);
            current = Vec::new();
        } else {
            current.push(op.clone());
        }
    }
    if !current.is_empty() {
        blocks.push(current);
    }
    blocks
}

fn filter_optimizable_ops<'a>(block: &'a [Operator<'a>]) -> Vec<Operator<'a>> {
    block
        .iter()
        .filter(|op| !is_block_begin(op) && !is_block_end(op))
        .cloned()
        .collect()
}

fn extract_from_body(
    func_index: u32,
    num_params: u32,
    total_locals: u32,
    body: &wasmparser::FunctionBody<'_>,
    out: &mut Vec<StraightSegment>,
    warnings: &mut Vec<String>,
) -> Result<(), String> {
    let op_reader = body
        .get_operators_reader()
        .map_err(|e| format!("func {func_index} operators: {e}"))?;
    let operators = op_reader
        .into_iter()
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| format!("func {func_index} operator: {e}"))?;

    let (_, func_max_stack) = stack_bounds_operators(&operators);
    let bounds_template = SegmentBounds::new(total_locals, func_max_stack);

    let mut segment_index = 0usize;
    for block in blocks_from_operators(&operators) {
        let optimizable = filter_optimizable_ops(&block);
        if optimizable.is_empty() {
            continue;
        }
        extract_from_ops(
            func_index,
            num_params,
            total_locals,
            bounds_template,
            &optimizable,
            &mut segment_index,
            out,
            warnings,
        );
    }

    Ok(())
}

fn extract_from_ops(
    func_index: u32,
    num_params: u32,
    total_locals: u32,
    bounds_template: SegmentBounds,
    ops: &[Operator<'_>],
    segment_index: &mut usize,
    out: &mut Vec<StraightSegment>,
    warnings: &mut Vec<String>,
) {
    let (_, block_max_stack) = stack_bounds_operators(ops);
    let bounds = SegmentBounds::new(total_locals, block_max_stack.max(bounds_template.max_stack));
    let mut machine = SymMachine::function_entry(num_params, total_locals, bounds.max_stack);
    machine.begin_segment();

    let mut collected: Vec<SemOp> = Vec::new();
    let mut segment_init: SymState = machine.to_init_state();
    let mut collecting = true;

    for op in ops {
        match classify_operator(op) {
            OpClass::Supported(sem) => {
                if !collecting {
                    continue;
                }
                match machine.exec(&sem) {
                    Ok(()) => collected.push(sem),
                    Err(e) => {
                        let msg = format!(
                            "func {func_index} segment {segment_index} forward exec {sem:?}: {e:?}"
                        );
                        warnings.push(msg.clone());
                        eprintln!("warning: {msg}");
                        flush_segment(
                            func_index,
                            segment_index,
                            &mut collected,
                            &segment_init,
                            &machine,
                            bounds,
                            out,
                        );
                        collecting = false;
                    }
                }
            }
            OpClass::PopStack => {
                if !collecting {
                    continue;
                }
                if let Err(e) = machine.pop() {
                    warn_exec(func_index, *segment_index, "drop", e, warnings);
                    flush_and_stop(
                        func_index,
                        segment_index,
                        &mut collected,
                        &segment_init,
                        &mut machine,
                        bounds,
                        out,
                        warnings,
                        num_params,
                        total_locals,
                    );
                    collecting = false;
                }
            }
            OpClass::Boundary { pop, push } => {
                flush_segment(
                    func_index,
                    segment_index,
                    &mut collected,
                    &segment_init,
                    &machine,
                    bounds,
                    out,
                );
                if let Err(e) = machine.apply_boundary_stack(pop, push) {
                    warn_exec(func_index, *segment_index, "boundary", e, warnings);
                }
                machine.begin_segment();
                segment_init = machine.to_init_state();
                collecting = true;
            }
            OpClass::Unsupported => {
                flush_segment(
                    func_index,
                    segment_index,
                    &mut collected,
                    &segment_init,
                    &machine,
                    bounds,
                    out,
                );
                collecting = false;
            }
        }
    }

    if collecting {
        flush_segment(
            func_index,
            segment_index,
            &mut collected,
            &segment_init,
            &machine,
            bounds,
            out,
        );
    }
}

fn warn_exec(
    func_index: u32,
    segment_index: usize,
    op: &str,
    err: ForwardError,
    warnings: &mut Vec<String>,
) {
    let msg = format!("func {func_index} segment {segment_index} {op}: {err:?}");
    warnings.push(msg.clone());
    eprintln!("warning: {msg}");
}

fn flush_and_stop(
    func_index: u32,
    segment_index: &mut usize,
    ops: &mut Vec<SemOp>,
    init: &SymState,
    machine: &mut SymMachine,
    bounds: SegmentBounds,
    out: &mut Vec<StraightSegment>,
    _warnings: &mut Vec<String>,
    num_params: u32,
    total_locals: u32,
) {
    flush_segment(
        func_index,
        segment_index,
        ops,
        init,
        machine,
        bounds,
        out,
    );
    *machine = SymMachine::function_entry(num_params, total_locals, bounds.max_stack);
    machine.begin_segment();
}

fn flush_segment(
    func_index: u32,
    segment_index: &mut usize,
    ops: &mut Vec<SemOp>,
    init: &SymState,
    machine: &SymMachine,
    mut bounds: SegmentBounds,
    out: &mut Vec<StraightSegment>,
) {
    if ops.is_empty() {
        return;
    }
    let (_, max_stack) = stack_bounds_ops(ops);
    bounds.max_stack = bounds.max_stack.max(max_stack + 5);
    let fin = machine.to_fin_state();
    if !init.validate_bounds(&bounds) || !fin.validate_bounds(&bounds) {
        ops.clear();
        return;
    }
    out.push(StraightSegment {
        func_index,
        segment_index: *segment_index,
        ops: ops.clone(),
        init: init.clone(),
        fin,
        bounds,
    });
    *segment_index += 1;
    ops.clear();
}

enum OpClass {
    Supported(SemOp),
    PopStack,
    Boundary { pop: usize, push: usize },
    Unsupported,
}

fn classify_operator(op: &Operator<'_>) -> OpClass {
    if is_boundary(op) {
        let (pop, push) = boundary_stack_effect(op);
        return OpClass::Boundary { pop, push };
    }
    match op {
        Operator::I32Const { value } => OpClass::Supported(SemOp::I32Const(*value)),
        Operator::I32Add => OpClass::Supported(SemOp::I32Add),
        Operator::I32Sub => OpClass::Supported(SemOp::I32Sub),
        Operator::I32Mul => OpClass::Supported(SemOp::I32Mul),
        Operator::I32DivU => OpClass::Supported(SemOp::I32DivU),
        Operator::I32DivS => OpClass::Supported(SemOp::I32DivS),
        Operator::I32Shl => OpClass::Supported(SemOp::I32Shl),
        Operator::I32Eq => OpClass::Supported(SemOp::I32Eq),
        Operator::I32Ne => OpClass::Supported(SemOp::I32Ne),
        Operator::I32LtS => OpClass::Supported(SemOp::I32LtS),
        Operator::I32LeS => OpClass::Supported(SemOp::I32LeS),
        Operator::I32GtS => OpClass::Supported(SemOp::I32GtS),
        Operator::LocalGet { local_index } => OpClass::Supported(SemOp::LocalGet(*local_index)),
        Operator::LocalSet { local_index } => OpClass::Supported(SemOp::LocalSet(*local_index)),
        Operator::LocalTee { local_index } => OpClass::Supported(SemOp::LocalTee(*local_index)),
        Operator::Drop => OpClass::PopStack,
        Operator::Nop | Operator::Block { .. } | Operator::Else | Operator::End => {
            OpClass::Unsupported
        }
        Operator::Loop { .. }
        | Operator::Br { .. }
        | Operator::BrIf { .. }
        | Operator::BrTable { .. }
        | Operator::Return
        | Operator::If { .. }
        | Operator::Unreachable
        | Operator::Select => OpClass::Unsupported,
        _ => OpClass::Unsupported,
    }
}

fn is_boundary(op: &Operator<'_>) -> bool {
    matches!(
        op,
        Operator::I32Load { .. }
            | Operator::I32Load8S { .. }
            | Operator::I32Load8U { .. }
            | Operator::I32Load16S { .. }
            | Operator::I32Load16U { .. }
            | Operator::I32Store { .. }
            | Operator::I32Store8 { .. }
            | Operator::I32Store16 { .. }
            | Operator::GlobalGet { .. }
            | Operator::GlobalSet { .. }
            | Operator::Call { .. }
            | Operator::CallIndirect { .. }
    )
}

fn boundary_stack_effect(op: &Operator<'_>) -> (usize, usize) {
    operator_stack_effect(op).unwrap_or((0, 0))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::optimize::format_ops;

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
        assert!(
            info.segments.len() >= 2,
            "segments: {:?}",
            info.segments
                .iter()
                .map(|s| format_ops(&s.ops))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn br_splits_block_without_control_ops() {
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
        assert!(info.segments.len() >= 1);
        assert_eq!(info.segments[0].ops.len(), 3);
    }

    #[test]
    fn memory_splits_segment() {
        let wasm = wat_to_wasm(
            r#"(module
                (memory 1)
                (func (param i32)
                  local.get 0
                  i32.const 1
                  i32.add
                  i32.const 0
                  i32.store
                  local.get 0
                  i32.const 2
                  i32.add
                )
            )"#,
        );
        let info = parse_wasm_bytes(&wasm).expect("parse");
        assert_eq!(info.segments.len(), 2);
        assert_eq!(info.segments[0].ops.len(), 4);
        assert_eq!(info.segments[1].ops.len(), 3);
    }

    #[test]
    fn addition_chains_parses_without_abort() {
        let bytes = include_bytes!("../../examples/addition_chains_initial.wasm");
        let info = parse_wasm_bytes(bytes).expect("addition_chains must parse");
        assert!(!info.segments.is_empty(), "expected at least one segment");
    }

    #[test]
    fn reverse_uses_high_local_index() {
        let bytes = include_bytes!("../../examples/addition_chains_initial.wasm");
        let info = parse_wasm_bytes(bytes).expect("parse");
        let has_local_3 = info.segments.iter().any(|s| {
            s.ops
                .iter()
                .any(|op| matches!(op, SemOp::LocalSet(3) | SemOp::LocalTee(3)))
        });
        assert!(has_local_3, "expected segment using local 3");
    }
}
