//! Whole-function extraction for local-allocation optimization.

use wasmparser::{FuncType, Operator, Parser, Payload, TypeRef, ValType};
use std::path::Path;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LocalValType {
    I32,
    I64,
    F32,
    F64,
}

impl LocalValType {
    pub fn from_val_type(ty: ValType) -> Result<Self, String> {
        match ty {
            ValType::I32 => Ok(Self::I32),
            ValType::I64 => Ok(Self::I64),
            ValType::F32 => Ok(Self::F32),
            ValType::F64 => Ok(Self::F64),
            other => Err(format!("unsupported local type {other:?}")),
        }
    }
}

/// One Wasm function body, flattened to owned instructions.
#[derive(Clone, Debug)]
pub struct WasmFunction {
    pub func_index: u32,
    pub num_params: u32,
    /// Local slot types: params first, then declared locals.
    pub local_types: Vec<LocalValType>,
    pub instrs: Vec<FuncInstr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FuncInstr {
    LocalGet(u32),
    LocalSet(u32),
    LocalTee(u32),
    /// Any other operator (including control flow).
    Other(OtherInstr),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OtherInstr {
    Nop,
    Block,
    Loop,
    If,
    Else,
    End,
    Br(u32),
    BrIf(u32),
    BrTable { targets: Vec<u32> },
    Return,
    Call { func_index: u32 },
    Unreachable,
    Generic,
}

#[derive(Clone, Debug)]
pub struct WasmModuleFunctions {
    pub functions: Vec<WasmFunction>,
    pub warnings: Vec<String>,
}

pub fn parse_wasm_functions(path: &Path) -> Result<WasmModuleFunctions, String> {
    let bytes = read_wasm_bytes(path)?;
    parse_wasm_functions_bytes(&bytes)
}

pub fn parse_wasm_functions_bytes(bytes: &[u8]) -> Result<WasmModuleFunctions, String> {
    let mut functions = Vec::new();
    let mut warnings = Vec::new();
    let mut code_func_index = 0u32;
    let mut import_func_count = 0usize;
    let mut types: Vec<FuncType> = Vec::new();
    let mut module_func_types: Vec<FuncType> = Vec::new();

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
                        let (_offset, import) = import.map_err(|e| format!("import entry: {e}"))?;
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
                match extract_function(module_func_index as u32, func_type, &body) {
                    Ok(func) => functions.push(func),
                    Err(e) => warnings.push(format!("func {module_func_index}: {e}")),
                }
                code_func_index += 1;
            }
            _ => {}
        }
    }

    Ok(WasmModuleFunctions {
        functions,
        warnings,
    })
}

fn read_wasm_bytes(path: &Path) -> Result<Vec<u8>, String> {
    let ext = path.extension().and_then(|e| e.to_str());
    if ext == Some("wat") {
        let text = std::fs::read_to_string(path)
            .map_err(|e| format!("read {}: {e}", path.display()))?;
        wat::parse_str(&text).map_err(|e| format!("parse wat {}: {e}", path.display()))
    } else {
        std::fs::read(path).map_err(|e| format!("read {}: {e}", path.display()))
    }
}

fn extract_function(
    func_index: u32,
    func_type: &FuncType,
    body: &wasmparser::FunctionBody<'_>,
) -> Result<WasmFunction, String> {
    let num_params = func_type.params().len() as u32;
    let mut local_types: Vec<LocalValType> = func_type
        .params()
        .iter()
        .copied()
        .map(LocalValType::from_val_type)
        .collect::<Result<_, _>>()?;

    for entry in body
        .get_locals_reader()
        .map_err(|e| format!("locals reader: {e}"))?
    {
        let (count, ty) = entry.map_err(|e| format!("locals entry: {e}"))?;
        let lt = LocalValType::from_val_type(ty)?;
        for _ in 0..count {
            local_types.push(lt);
        }
    }

    let op_reader = body
        .get_operators_reader()
        .map_err(|e| format!("operators: {e}"))?;
    let operators = op_reader
        .into_iter()
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| format!("operator: {e}"))?;

    let instrs = operators.iter().map(operator_to_instr).collect();

    Ok(WasmFunction {
        func_index,
        num_params,
        local_types,
        instrs,
    })
}

fn operator_to_instr(op: &Operator<'_>) -> FuncInstr {
    match op {
        Operator::LocalGet { local_index } => FuncInstr::LocalGet(*local_index),
        Operator::LocalSet { local_index } => FuncInstr::LocalSet(*local_index),
        Operator::LocalTee { local_index } => FuncInstr::LocalTee(*local_index),
        Operator::Nop => FuncInstr::Other(OtherInstr::Nop),
        Operator::Block { .. } => FuncInstr::Other(OtherInstr::Block),
        Operator::Loop { .. } => FuncInstr::Other(OtherInstr::Loop),
        Operator::If { .. } => FuncInstr::Other(OtherInstr::If),
        Operator::Else => FuncInstr::Other(OtherInstr::Else),
        Operator::End => FuncInstr::Other(OtherInstr::End),
        Operator::Br { relative_depth } => FuncInstr::Other(OtherInstr::Br(*relative_depth)),
        Operator::BrIf { relative_depth } => FuncInstr::Other(OtherInstr::BrIf(*relative_depth)),
        Operator::BrTable { targets } => FuncInstr::Other(OtherInstr::BrTable {
            targets: targets
                .targets()
                .collect::<Result<Vec<_>, _>>()
                .unwrap_or_default(),
        }),
        Operator::Return => FuncInstr::Other(OtherInstr::Return),
        Operator::Call { function_index } => FuncInstr::Other(OtherInstr::Call {
            func_index: *function_index,
        }),
        Operator::Unreachable => FuncInstr::Other(OtherInstr::Unreachable),
        _ => FuncInstr::Other(OtherInstr::Generic),
    }
}

impl WasmFunction {
    pub fn total_locals(&self) -> u32 {
        self.local_types.len() as u32
    }

    pub fn instr_count(&self) -> usize {
        self.instrs.len()
    }

    pub fn local_instr_count(&self) -> usize {
        self.instrs
            .iter()
            .filter(|i| matches!(i, FuncInstr::LocalGet(_) | FuncInstr::LocalSet(_) | FuncInstr::LocalTee(_)))
            .count()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_simple_function() {
        let wasm = wat::parse_str(
            r#"(module
                (func (param i32) (local i32)
                  local.get 0
                  local.set 1
                  local.get 1
                  i32.const 0
                  i32.add
                )
            )"#,
        )
        .unwrap();
        let m = parse_wasm_functions_bytes(&wasm).unwrap();
        assert_eq!(m.functions.len(), 1);
        let f = &m.functions[0];
        assert_eq!(f.total_locals(), 2);
        assert_eq!(f.instr_count(), 5);
    }
}
