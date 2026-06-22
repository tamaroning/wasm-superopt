//! Wasm binary parsing via wasmparser.

use crate::semantics::SemOp;
use crate::sym::{ForwardError, SymMachine, SymState};
use crate::wasm::deps::compute_dependencies;
use crate::wasm::segment::OpaqueMeta;
use crate::wasm::{SegmentBounds, StraightSegment};
use crate::wasm::stack_analysis::{stack_bounds_ops, stack_bounds_operators};
use std::collections::HashSet;
use std::fs;
use std::io::{self, Write};
use std::path::Path;
use wasmparser::{FuncType, Operator, Parser, Payload, TypeRef, ValType};

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

fn i32_param_count(ft: &FuncType) -> Result<u8, String> {
    let n = ft
        .params()
        .iter()
        .filter(|&&t| t == ValType::I32)
        .count();
    if n != ft.params().len() {
        return Err(format!(
            "only i32 params supported in calls, got {:?}",
            ft.params()
        ));
    }
    Ok(n as u8)
}

fn i32_result_count(ft: &FuncType) -> Result<u8, String> {
    let n = ft
        .results()
        .iter()
        .filter(|&&t| t == ValType::I32)
        .count();
    if n != ft.results().len() {
        return Err(format!(
            "only i32 results supported in calls, got {:?}",
            ft.results()
        ));
    }
    Ok(n as u8)
}

pub fn parse_wasm_bytes(bytes: &[u8]) -> Result<WasmModuleInfo, String> {
    let mut types: Vec<FuncType> = Vec::new();
    let mut module_func_types: Vec<FuncType> = Vec::new();
    let mut import_func_count = 0usize;
    let mut segments = Vec::new();
    let mut warnings = Vec::new();
    let mut code_func_index = 0u32;

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
            Payload::ImportSection(reader) => {
                for group in reader {
                    let group = group.map_err(|e| format!("import section: {e}"))?;
                    for import in group {
                        let (_offset, import) =
                            import.map_err(|e| format!("import entry: {e}"))?;
                        if let TypeRef::Func(type_idx) = import.ty {
                            let ft = types
                                .get(type_idx as usize)
                                .ok_or_else(|| format!("missing import type {type_idx}"))?
                                .clone();
                            module_func_types.push(ft);
                            import_func_count += 1;
                        }
                    }
                }
            }
            Payload::FunctionSection(reader) => {
                let function_type_indices: Vec<u32> = reader
                    .into_iter()
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|e| format!("function section: {e}"))?;
                for type_idx in function_type_indices {
                    let ft = types
                        .get(type_idx as usize)
                        .ok_or_else(|| format!("missing func type {type_idx}"))?
                        .clone();
                    module_func_types.push(ft);
                }
            }
            Payload::CodeSectionEntry(body) => {
                let module_func_index = import_func_count + code_func_index as usize;
                let func_type = module_func_types
                    .get(module_func_index)
                    .ok_or_else(|| format!("missing type for module func {module_func_index}"))?;
                let num_params = func_type.params().len() as u32;
                let declared = count_declared_locals(&body)?;
                let total_locals = num_params + declared;
                extract_from_body(
                    code_func_index,
                    num_params,
                    total_locals,
                    &module_func_types,
                    &body,
                    &mut segments,
                    &mut warnings,
                )?;
                code_func_index += 1;
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
    module_func_types: &[FuncType],
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
            module_func_types,
            &optimizable,
            &mut segment_index,
            out,
            warnings,
        );
    }

    Ok(())
}

struct OpClassCtx<'a> {
    module_func_types: &'a [FuncType],
    next_access_id: u32,
}

impl<'a> OpClassCtx<'a> {
    fn fresh_id(&mut self) -> u32 {
        let id = self.next_access_id;
        self.next_access_id += 1;
        id
    }
}

fn extract_from_ops(
    func_index: u32,
    num_params: u32,
    total_locals: u32,
    bounds_template: SegmentBounds,
    module_func_types: &[FuncType],
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
    let mut opaque_meta: Vec<OpaqueMeta> = Vec::new();
    let segment_init: SymState = machine.to_init_state();
    let mut collecting = true;
    let mut ctx = OpClassCtx {
        module_func_types,
        next_access_id: 0,
    };

    for op in ops {
        match classify_operator(op, &mut ctx) {
            OpClass::Supported(sem) => {
                if !collecting {
                    continue;
                }
                match machine.exec_with_meta(&sem) {
                    Ok(Some(meta)) => {
                        opaque_meta.push(meta);
                        collected.push(sem);
                    }
                    Ok(None) => collected.push(sem),
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
                            &mut opaque_meta,
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
                        &mut opaque_meta,
                        &segment_init,
                        &mut machine,
                        bounds,
                        out,
                        num_params,
                        total_locals,
                    );
                    collecting = false;
                }
            }
            OpClass::Unsupported => {
                flush_segment(
                    func_index,
                    segment_index,
                    &mut collected,
                    &mut opaque_meta,
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
            &mut opaque_meta,
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
    opaque_meta: &mut Vec<OpaqueMeta>,
    init: &SymState,
    machine: &mut SymMachine,
    bounds: SegmentBounds,
    out: &mut Vec<StraightSegment>,
    num_params: u32,
    total_locals: u32,
) {
    flush_segment(
        func_index,
        segment_index,
        ops,
        opaque_meta,
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
    opaque_meta: &mut Vec<OpaqueMeta>,
    init: &SymState,
    machine: &SymMachine,
    mut bounds: SegmentBounds,
    out: &mut Vec<StraightSegment>,
) {
    if ops.is_empty() {
        opaque_meta.clear();
        return;
    }
    let (_, max_stack) = stack_bounds_ops(ops);
    bounds.max_stack = bounds.max_stack.max(max_stack + 5);
    let fin = machine.to_fin_state();
    if !init.validate_bounds(&bounds) || !fin.validate_bounds(&bounds) {
        ops.clear();
        opaque_meta.clear();
        return;
    }
    let dependencies = compute_dependencies(ops, opaque_meta);
    out.push(StraightSegment {
        func_index,
        segment_index: *segment_index,
        split_part: None,
        ops: ops.clone(),
        init: init.clone(),
        fin,
        bounds,
        opaque_meta: opaque_meta.clone(),
        dependencies,
    });
    *segment_index += 1;
    ops.clear();
    opaque_meta.clear();
}

enum OpClass {
    Supported(SemOp),
    PopStack,
    Unsupported,
}

fn load_sem(id: u32, mem: u32, offset: u32) -> SemOp {
    SemOp::I32Load { id, mem, offset }
}

fn store_sem(id: u32, mem: u32, offset: u32) -> SemOp {
    SemOp::I32Store { id, mem, offset }
}

fn classify_operator(op: &Operator<'_>, ctx: &mut OpClassCtx<'_>) -> OpClass {
    match op {
        Operator::I32Const { value } => OpClass::Supported(SemOp::I32Const(*value)),
        Operator::I32Add => OpClass::Supported(SemOp::I32Add),
        Operator::I32Sub => OpClass::Supported(SemOp::I32Sub),
        Operator::I32Mul => OpClass::Supported(SemOp::I32Mul),
        Operator::I32DivU => OpClass::Supported(SemOp::I32DivU),
        Operator::I32DivS => OpClass::Supported(SemOp::I32DivS),
        Operator::I32RemU => OpClass::Supported(SemOp::I32RemU),
        Operator::I32RemS => OpClass::Supported(SemOp::I32RemS),
        Operator::I32Shl => OpClass::Supported(SemOp::I32Shl),
        Operator::I32And => OpClass::Supported(SemOp::I32And),
        Operator::I32Or => OpClass::Supported(SemOp::I32Or),
        Operator::I32Xor => OpClass::Supported(SemOp::I32Xor),
        Operator::I32ShrU => OpClass::Supported(SemOp::I32ShrU),
        Operator::I32ShrS => OpClass::Supported(SemOp::I32ShrS),
        Operator::I32Rotl => OpClass::Supported(SemOp::I32Rotl),
        Operator::I32Rotr => OpClass::Supported(SemOp::I32Rotr),
        Operator::I32Eq => OpClass::Supported(SemOp::I32Eq),
        Operator::I32Ne => OpClass::Supported(SemOp::I32Ne),
        Operator::I32LtS => OpClass::Supported(SemOp::I32LtS),
        Operator::I32LeS => OpClass::Supported(SemOp::I32LeS),
        Operator::I32GtS => OpClass::Supported(SemOp::I32GtS),
        Operator::I32Eqz => OpClass::Supported(SemOp::I32Eqz),
        Operator::I32Clz => OpClass::Supported(SemOp::I32Clz),
        Operator::I32Ctz => OpClass::Supported(SemOp::I32Ctz),
        Operator::I32Popcnt => OpClass::Supported(SemOp::I32Popcnt),
        Operator::LocalGet { local_index } => OpClass::Supported(SemOp::LocalGet(*local_index)),
        Operator::LocalSet { local_index } => OpClass::Supported(SemOp::LocalSet(*local_index)),
        Operator::LocalTee { local_index } => OpClass::Supported(SemOp::LocalTee(*local_index)),
        Operator::Drop => OpClass::PopStack,
        Operator::I32Load { memarg, .. }
        | Operator::I32Load8S { memarg, .. }
        | Operator::I32Load8U { memarg, .. }
        | Operator::I32Load16S { memarg, .. }
        | Operator::I32Load16U { memarg, .. } => {
            let id = ctx.fresh_id();
            OpClass::Supported(load_sem(id, memarg.memory, memarg.offset as u32))
        }
        Operator::I32Store { memarg, .. }
        | Operator::I32Store8 { memarg, .. }
        | Operator::I32Store16 { memarg, .. } => {
            let id = ctx.fresh_id();
            OpClass::Supported(store_sem(id, memarg.memory, memarg.offset as u32))
        }
        Operator::GlobalGet { global_index } => {
            let id = ctx.fresh_id();
            OpClass::Supported(SemOp::GlobalGet {
                id,
                global_index: *global_index,
            })
        }
        Operator::GlobalSet { global_index } => {
            let id = ctx.fresh_id();
            OpClass::Supported(SemOp::GlobalSet {
                id,
                global_index: *global_index,
            })
        }
        Operator::Call { function_index } => {
            let id = ctx.fresh_id();
            let ft = match ctx.module_func_types.get(*function_index as usize) {
                Some(ft) => ft,
                None => return OpClass::Unsupported,
            };
            let pops = match i32_param_count(ft) {
                Ok(n) => n,
                Err(_) => return OpClass::Unsupported,
            };
            let pushes = match i32_result_count(ft) {
                Ok(n) => n,
                Err(_) => return OpClass::Unsupported,
            };
            OpClass::Supported(SemOp::Call {
                id,
                func_index: *function_index,
                pops,
                pushes,
            })
        }
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
        | Operator::Select
        | Operator::CallIndirect { .. } => OpClass::Unsupported,
        _ => OpClass::Unsupported,
    }
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
    fn load_store_stays_in_one_segment() {
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
        assert_eq!(info.segments.len(), 1, "expected single segment");
        assert_eq!(info.segments[0].ops.len(), 8);
        assert!(!info.segments[0].opaque_meta.is_empty());
    }

    #[test]
    fn addition_chains_parses_without_abort() {
        let bytes = include_bytes!("../../examples/addition_chains_initial.wasm");
        let info = parse_wasm_bytes(bytes).expect("addition_chains must parse");
        assert!(!info.segments.is_empty(), "expected at least one segment");
    }

    #[test]
    fn addition_chains_segment_count_drops_after_opaque_merge() {
        let bytes = include_bytes!("../../examples/addition_chains_initial.wasm");
        let info = parse_wasm_bytes(bytes).expect("addition_chains must parse");
        assert!(
            info.segments.len() < 327,
            "Phase 1 split on every boundary produced 327; got {}",
            info.segments.len()
        );
        assert!(
            info.segments.len() <= 200,
            "expected merged opaque segments, got {}",
            info.segments.len()
        );
        let mixed = info.segments.iter().any(|s| {
            let has_load = s.ops.iter().any(|op| matches!(op, SemOp::I32Load { .. }));
            let has_store = s.ops.iter().any(|op| matches!(op, SemOp::I32Store { .. }));
            let has_arith = s
                .ops
                .iter()
                .any(|op| matches!(op, SemOp::I32Add | SemOp::I32Mul | SemOp::I32Sub));
            has_load && has_store && has_arith
        });
        assert!(mixed, "expected at least one load+store+arith segment");
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
