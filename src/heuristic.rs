//! Admissible heuristics for backward A*.

use crate::canon::{CanonId, Canonizer};
use crate::goal::{all_subtree_exprs, LocalReq, MachineState, MAX_LOCAL_SLOT};
use std::collections::HashSet;

pub fn h_stack(g: &MachineState, init: &MachineState, canon: &mut Canonizer) -> usize {
    let mut k = 0usize;
    while k < g.stack.len().min(init.stack.len())
        && canon.canon(&g.stack[k]) == canon.canon(&init.stack[k])
    {
        k += 1;
    }
    g.stack.len().saturating_sub(k)
}

pub fn h_local(g: &MachineState, init: &MachineState, canon: &mut Canonizer) -> usize {
    let mut n = 0usize;
    for slot in 0..=MAX_LOCAL_SLOT {
        let cur = g.locals.get(&slot);
        let init_v = init.locals.get(&slot);
        let need = match cur {
            None | Some(LocalReq::DontCare) => false,
            Some(LocalReq::Need(v)) => match init_v {
                Some(LocalReq::Need(iv)) => canon.canon(v) != canon.canon(iv),
                _ => true,
            },
        };
        if need {
            n += 1;
        }
    }
    n
}

pub fn available_canon(init: &MachineState, canon: &mut Canonizer) -> HashSet<CanonId> {
    let mut set = HashSet::new();
    for e in &init.stack {
        for sub in all_subtree_exprs(e) {
            set.insert(canon.canon(&sub));
        }
    }
    for req in init.locals.values() {
        if let LocalReq::Need(e) = req {
            for sub in all_subtree_exprs(e) {
                set.insert(canon.canon(&sub));
            }
        }
    }
    set
}

pub fn h_node(g: &MachineState, init: &MachineState, canon: &mut Canonizer) -> usize {
    let avail = available_canon(init, canon);
    let mut need = HashSet::new();
    for e in &g.stack {
        for sub in all_subtree_exprs(e) {
            let c = canon.canon(&sub);
            if !avail.contains(&c) {
                need.insert(c);
            }
        }
    }
    for req in g.locals.values() {
        if let LocalReq::Need(e) = req {
            for sub in all_subtree_exprs(e) {
                let c = canon.canon(&sub);
                if !avail.contains(&c) {
                    need.insert(c);
                }
            }
        }
    }
    need.len()
}

pub fn h_goal(g: &MachineState, init: &MachineState, canon: &mut Canonizer) -> usize {
    h_stack(g, init, canon)
        .max(h_local(g, init, canon))
        .max(h_node(g, init, canon))
}
