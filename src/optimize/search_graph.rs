//! Record backward A* exploration and emit Graphviz DOT.

use super::inverse::SearchState;
use super::search::MemoKey;
use crate::semantics::SemOp;
use crate::sym::{LocalReq, SymState, ValueExpr};
use std::collections::HashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NodeKind {
    Root,
    Intermediate,
    Solution,
    MemoSkip,
}

#[derive(Clone, Debug)]
struct TraceNode {
    id: u32,
    label: String,
    cost: usize,
    kind: NodeKind,
}

#[derive(Clone, Debug)]
struct TraceEdge {
    from: u32,
    to: u32,
    op: String,
    pruned: bool,
}

/// Exploration DAG collected during A* (nodes keyed by memo-normalized state).
#[derive(Clone, Debug, Default)]
pub struct SearchTrace {
    key_to_id: HashMap<MemoKey, u32>,
    nodes: Vec<TraceNode>,
    edges: Vec<TraceEdge>,
    solution_id: Option<u32>,
    /// Node ids from fin (root) to init (solution), inclusive.
    solution_path: Option<Vec<u32>>,
}

impl SearchTrace {
    pub fn intern(
        &mut self,
        key: &MemoKey,
        state: &SearchState,
        cost: usize,
        kind: NodeKind,
    ) -> u32 {
        if let Some(&id) = self.key_to_id.get(key) {
            if kind == NodeKind::Solution || kind == NodeKind::Root {
                if let Some(node) = self.nodes.iter_mut().find(|n| n.id == id) {
                    node.kind = kind;
                    node.label = format_node_label(state, cost, kind);
                }
                if kind == NodeKind::Solution {
                    self.solution_id = Some(id);
                }
            }
            return id;
        }
        let id = self.nodes.len() as u32;
        let label = format_node_label(state, cost, kind);
        self.key_to_id.insert(key.clone(), id);
        self.nodes.push(TraceNode {
            id,
            label,
            cost,
            kind,
        });
        if kind == NodeKind::Solution {
            self.solution_id = Some(id);
        }
        id
    }

    pub fn add_edge(&mut self, from: u32, to: u32, op: &SemOp, pruned: bool) {
        if self
            .edges
            .iter()
            .any(|e| e.from == from && e.to == to && e.pruned == pruned)
        {
            return;
        }
        self.edges.push(TraceEdge {
            from,
            to,
            op: format!("← {op}"),
            pruned,
        });
    }

    pub fn node_id(&self, key: &MemoKey) -> Option<u32> {
        self.key_to_id.get(key).copied()
    }

    pub fn num_edges(&self) -> usize {
        self.edges.len()
    }

    pub fn mark_memo_skip(&mut self, id: u32) {
        if let Some(node) = self.nodes.iter_mut().find(|n| n.id == id) {
            if node.kind == NodeKind::Intermediate {
                node.kind = NodeKind::MemoSkip;
            }
        }
    }

    pub fn solution_node(&self) -> Option<u32> {
        self.solution_id
    }

    pub fn set_solution_path(&mut self, keys: &[MemoKey]) {
        let path: Vec<u32> = keys
            .iter()
            .filter_map(|k| self.key_to_id.get(k).copied())
            .collect();
        if path.len() == keys.len() {
            self.solution_path = Some(path);
        }
    }

    pub fn solution_path(&self) -> Option<&[u32]> {
        self.solution_path.as_deref()
    }

    fn solution_path_edges(&self) -> Vec<(u32, u32)> {
        let Some(path) = &self.solution_path else {
            return vec![];
        };
        path.windows(2)
            .map(|w| (w[0], w[1]))
            .collect()
    }

    pub fn to_dot(&self) -> String {
        let mut out = String::from(
            "digraph search {\n  rankdir=BT;\n  graph [dpi=300];\n  node [shape=box, fontname=\"Courier\", fontsize=9];\n  edge [fontname=\"Courier\", fontsize=8];\n",
        );
        let path_nodes: std::collections::HashSet<u32> = self
            .solution_path
            .as_ref()
            .map(|p| p.iter().copied().collect())
            .unwrap_or_default();
        let path_edges: std::collections::HashSet<(u32, u32)> =
            self.solution_path_edges().into_iter().collect();

        for node in &self.nodes {
            let on_path = path_nodes.contains(&node.id);
            let (fill, style) = if on_path {
                match node.kind {
                    NodeKind::Root => ("lightyellow", "filled,bold"),
                    NodeKind::Solution => ("lightgreen", "filled,bold"),
                    _ => ("mistyrose", "filled,bold"),
                }
            } else {
                match node.kind {
                    NodeKind::Root => ("lightyellow", "filled,bold"),
                    NodeKind::Solution => ("lightgreen", "filled,bold"),
                    NodeKind::MemoSkip => ("whitesmoke", "filled,dashed"),
                    NodeKind::Intermediate => ("white", "filled"),
                }
            };
            let extra = if on_path {
                ", color=red, penwidth=2.5"
            } else {
                ""
            };
            out.push_str(&format!(
                "  n{} [label=\"{}\", style=\"{}\", fillcolor=\"{}\"{extra}];\n",
                node.id,
                dot_escape(&node.label),
                style,
                fill,
            ));
        }
        for edge in &self.edges {
            let on_path = path_edges.contains(&(edge.from, edge.to));
            let suffix = if edge.pruned { " (memo)" } else { "" };
            let edge_attrs = if on_path {
                format!(
                    " [color=red, penwidth=2.5, label=\"{}{}\"]",
                    dot_escape(&edge.op),
                    suffix
                )
            } else if edge.pruned {
                format!(
                    " [style=dashed, color=gray, label=\"{}{}\"]",
                    dot_escape(&edge.op),
                    suffix
                )
            } else {
                format!(" [label=\"{}\"]", dot_escape(&edge.op))
            };
            out.push_str(&format!(
                "  n{} -> n{}{};\n",
                edge.from, edge.to, edge_attrs
            ));
        }
        out.push_str("}\n");
        out
    }
}

pub fn format_sym_state(state: &SymState) -> String {
    let stack = if state.stack.is_empty() {
        "[]".to_string()
    } else {
        format!(
            "[{}]",
            state
                .stack
                .iter()
                .map(format_expr_human)
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    if state.locals.is_empty() {
        return format!("⟨{stack}, {{}}⟩");
    }
    let locals = state
        .locals
        .iter()
        .map(|(&slot, req)| match req {
            LocalReq::DontCare => format!("{slot}:★"),
            LocalReq::Need(v) => format!("{slot}:{}", format_expr_human(v)),
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!("⟨{stack}, {{{locals}}}⟩")
}

fn format_node_label(state: &SearchState, cost: usize, kind: NodeKind) -> String {
    let state = format_sym_state(&state.goal);
    match kind {
        NodeKind::Root => format!("fin\ncost={cost}\n{state}"),
        NodeKind::Solution => format!("init\ncost={cost}\n{state}"),
        NodeKind::MemoSkip | NodeKind::Intermediate => format!("cost={cost}\n{state}"),
    }
}

fn format_expr_human(expr: &ValueExpr) -> String {
    expr.to_string().replace("?L0", "L")
}

fn dot_escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"").replace('\n', "\\n")
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::optimize::fixtures::{fin, init};
    use crate::optimize::search::{solve_astar_traced, SearchConfig};
    use crate::synthesis::test_synthesis_rewrites;
    use crate::wasm::{SegmentBounds, StraightSegment};

    fn example_segment() -> StraightSegment {
        let init = init();
        let fin = fin();
        StraightSegment {
            func_index: 0,
            num_params: 1,
            segment_index: 0,
            split_part: None,
            ops: vec![],
            init: init.clone(),
            fin: fin.clone(),
            bounds: SegmentBounds::new(1, 4),
            opaque_meta: vec![],
            dependencies: vec![],
            disasm_by_id: Default::default(),
        }
    }

    #[test]
    fn example_search_dot_has_nodes_and_solution() {
        let segment = example_segment();
        let rules = test_synthesis_rewrites();
        let mut trace = SearchTrace::default();
        let result = solve_astar_traced(
            &segment,
            &rules,
            &SearchConfig::default(),
            Some(&mut trace),
        );
        assert!(result.ops.is_some());
        let dot = trace.to_dot();
        assert!(dot.contains("digraph search"));
        assert!(dot.contains("fin"));
        assert!(dot.contains("init"));
        assert!(
            !dot.contains("\\\\n"),
            "newlines must not be double-escaped in DOT"
        );
        assert!(trace.solution_node().is_some());
        assert!(trace.num_edges() > 0);
        let path = trace.solution_path().expect("solution path");
        assert!(path.len() >= 2);
        assert_eq!(path.first().copied(), trace.nodes.iter().find(|n| n.kind == NodeKind::Root).map(|n| n.id));
        assert_eq!(path.last().copied(), trace.solution_node());
        let dot = trace.to_dot();
        assert!(dot.contains("color=red"));
    }
}
