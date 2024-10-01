use std::collections::{HashMap, HashSet};

use bril_rs::*;

/// Returns the next non-label instruction starting from index `i` inclusive.
pub fn next_inst(mut i: usize, func: &Function) -> Option<usize> {
    while i < func.instrs.len() {
        match &func.instrs[i] {
            Code::Instruction(_) => return Some(i),
            _ => i += 1,
        }
    }
    None
}

/// Resolve labels to instruction offsets. Labels are resolved to the next
/// non-label instruction. If a label is the last instruction, it is not resolved.
pub fn resolve_labels(func: &Function) -> HashMap<String, usize> {
    let mut queue: Vec<String> = vec![];
    let mut map: HashMap<String, usize> = HashMap::new();
    for (i, code) in func.instrs.iter().enumerate() {
        match code {
            Code::Label { label } => queue.push(label.clone()),
            Code::Instruction(_) => {
                // resolve queued labels
                while let Some(label) = queue.pop() {
                    map.insert(label, i);
                }
            }
        }
    }
    map
}

pub fn collect_vars(func: &Function) -> HashSet<String> {
    let mut res: HashSet<String> = Default::default();
    for arg in &func.args {
        res.insert(arg.name.clone());
    }
    for code in &func.instrs {
        if let Code::Instruction(inst) = code {
            match inst {
                Instruction::Constant { dest, .. } | Instruction::Value { dest, .. } => {
                    res.insert(dest.clone());
                }
                _ => (),
            }
        }
    }
    res
}

pub type UFNode = u32;

pub struct UnionFind {
    nodes: Vec<UFNode>,
}

// TODO(altanh): path compression if it matters
impl UnionFind {
    pub fn new() -> UnionFind {
        UnionFind { nodes: vec![] }
    }

    pub fn make_node(&mut self) -> UFNode {
        let r = self.nodes.len() as UFNode;
        self.nodes.push(r);
        r
    }

    pub fn root(&self, mut n: UFNode) -> UFNode {
        assert!(n < self.nodes.len() as UFNode);
        while self.nodes[n as usize] != n {
            n = self.nodes[n as usize];
        }
        n
    }

    pub fn merge(&mut self, x: UFNode, y: UFNode) -> UFNode {
        let x = self.root(x);
        let y = self.root(y);
        let r = if x < y {
            self.nodes[y as usize] = x;
            x
        } else if y < x {
            self.nodes[x as usize] = y;
            y
        } else {
            // Already merged
            x
        };
        r
    }

    pub fn equiv(&self, x: UFNode, y: UFNode) -> bool {
        self.root(x) == self.root(y)
    }
}
