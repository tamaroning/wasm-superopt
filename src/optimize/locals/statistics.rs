//! CSV export for `--opt-locals` benchmark analysis.

use super::FunctionOptResult;
use serde::Serialize;
use std::io;
use std::path::Path;

/// One row per optimized function (`locals_functions.csv`).
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct LocalsFunctionCsvRow {
    pub func_index: u32,
    pub status: String,
    pub skip_reason: String,
    pub instr_before: usize,
    pub instr_after: usize,
    pub instr_saved: usize,
    pub local_slots_before: usize,
    pub local_slots_after: usize,
    pub local_slots_saved: usize,
    pub copies_removed: usize,
    pub webs: usize,
    pub interferes: usize,
    pub bb_count: usize,
    pub h4_clauses: usize,
    pub solver_time_secs: f64,
}

pub fn locals_function_csv_rows(results: &[FunctionOptResult]) -> Vec<LocalsFunctionCsvRow> {
    results.iter().map(locals_function_csv_row).collect()
}

fn locals_function_csv_row(result: &FunctionOptResult) -> LocalsFunctionCsvRow {
    let instr_saved = result.instr_before.saturating_sub(result.instr_after);
    let local_slots_saved = result
        .local_slots_before
        .saturating_sub(result.local_slots_after);
    LocalsFunctionCsvRow {
        func_index: result.func_index,
        status: result.status_label().to_string(),
        skip_reason: result.skip_reason.clone().unwrap_or_default(),
        instr_before: result.instr_before,
        instr_after: result.instr_after,
        instr_saved,
        local_slots_before: result.local_slots_before,
        local_slots_after: result.local_slots_after,
        local_slots_saved,
        copies_removed: result.copies_removed,
        webs: result.webs,
        interferes: result.interferes,
        bb_count: result.bb_count,
        h4_clauses: result.h4_clauses(),
        solver_time_secs: result.solver_time_secs,
    }
}

pub fn write_locals_function_csv(path: &Path, rows: &[LocalsFunctionCsvRow]) -> io::Result<()> {
    let mut writer = csv::Writer::from_path(path)?;
    for row in rows {
        writer.serialize(row)?;
    }
    writer.flush()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::optimize::locals::FunctionOptResult;

    #[test]
    fn csv_row_derives_saved_counts() {
        let result = FunctionOptResult {
            func_index: 3,
            skipped: false,
            skip_reason: None,
            instr_before: 10,
            instr_after: 8,
            local_slots_before: 5,
            local_slots_after: 4,
            copies_removed: 1,
            webs: 6,
            interferes: 2,
            bb_count: 1,
            solver_time_secs: 0.5,
        };
        let row = locals_function_csv_row(&result);
        assert_eq!(row.instr_saved, 2);
        assert_eq!(row.local_slots_saved, 1);
        assert_eq!(row.status, "improved");
        assert_eq!(row.h4_clauses, 12);
    }
}
