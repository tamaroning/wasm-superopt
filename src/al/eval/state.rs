//! Concrete machine state (locals + linear memory).

pub const LOCAL_SLOTS: usize = 8;
pub const MEM_SLOTS: usize = 16;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcreteState {
    pub locals: [i32; LOCAL_SLOTS],
    pub memory: [i32; MEM_SLOTS],
}

impl ConcreteState {
    pub fn new(locals: [i32; LOCAL_SLOTS], memory: [i32; MEM_SLOTS]) -> Self {
        Self { locals, memory }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcreteResult {
    pub stack: Vec<i32>,
    pub state: ConcreteState,
    pub trap: bool,
}
