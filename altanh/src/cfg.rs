use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt::Display,
    io,
};

use bril_rs::{Code, EffectOps, Function, Instruction};

#[derive(Default, Clone, PartialEq, Eq)]
pub struct Block {
    /// Non-control instructions
    pub insts: Vec<Instruction>,
    /// Terminating control instruction, or None if fallthrough
    pub term: Option<Instruction>,
    /// Label, if present
    pub label: Option<String>,
}

impl Block {
    /// A block is empty iff it has no instructions, no terminator, and no label.
    pub fn is_empty(&self) -> bool {
        self.insts.is_empty() && self.term.is_none() && self.label.is_none()
    }

    /// A block is a stub iff it is just a label.
    pub fn is_stub(&self) -> bool {
        self.insts.is_empty() && self.term.is_none() && self.label.is_some()
    }

    pub fn from_function(func: &Function) -> Vec<Block> {
        let mut blocks: Vec<Block> = vec![];
        let mut current: Block = Default::default();
        for code in &func.instrs {
            match code {
                Code::Label { label, .. } => {
                    // Terminate current basic block (if non-empty)
                    if !current.is_empty() {
                        blocks.push(current);
                        current = Default::default();
                    }
                    current.label = Some(label.clone());
                }
                Code::Instruction(inst) => match inst {
                    Instruction::Effect {
                        op: EffectOps::Branch | EffectOps::Jump | EffectOps::Return,
                        ..
                    } => {
                        // Terminate current block
                        current.term = Some(inst.clone());
                        blocks.push(current);
                        current = Default::default();
                    }
                    _ => {
                        current.insts.push(inst.clone());
                    }
                },
            }
        }
        if !current.is_empty() {
            blocks.push(current);
        }
        blocks
    }

    pub fn emit(&self, out: &mut Vec<Code>) {
        if let Some(label) = &self.label {
            out.push(Code::Label {
                label: label.clone(),
            });
        }
        for inst in &self.insts {
            out.push(Code::Instruction(inst.clone()));
        }
        if let Some(term) = &self.term {
            out.push(Code::Instruction(term.clone()));
        }
    }
}

impl Display for Block {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(label) = &self.label {
            writeln!(f, "{label}:")?;
        }
        for inst in &self.insts {
            writeln!(f, "    {inst}")?;
        }
        if let Some(term) = &self.term {
            writeln!(f, "    [[ {term} ]]")?;
        }
        Ok(())
    }
}

fn resolve_labels(blocks: &Vec<Block>) -> HashMap<String, usize> {
    let mut res = HashMap::new();
    for (i, block) in blocks.iter().enumerate() {
        if let Some(label) = &block.label {
            res.insert(label.clone(), i);
        }
    }
    res
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Node {
    Entry,
    Exit,
    Block(usize),
}

impl From<usize> for Node {
    fn from(value: usize) -> Self {
        Node::Block(value)
    }
}

struct FlowBuilder {
    flow: HashMap<Node, HashSet<Node>>,
    flow_r: HashMap<Node, HashSet<Node>>,
}

pub struct CFG<'a> {
    pub flow: HashMap<Node, HashSet<Node>>,
    pub flow_r: HashMap<Node, HashSet<Node>>,
    pub func: &'a Function,
    pub label_map: HashMap<String, usize>,
    pub blocks: Vec<Block>,
}

impl FlowBuilder {
    pub fn flows<S, T>(&mut self, from: S, to: T)
    where
        S: Into<Node>,
        T: Into<Node>,
    {
        let from: Node = from.into();
        let to: Node = to.into();
        if let None = self.flow.get(&from) {
            self.flow.insert(from, HashSet::new());
            self.flow_r.insert(from, HashSet::new());
        }
        if let None = self.flow.get(&to) {
            self.flow.insert(to, HashSet::new());
            self.flow_r.insert(to, HashSet::new());
        }
        self.flow.get_mut(&from).unwrap().insert(to);
        self.flow_r.get_mut(&to).unwrap().insert(from);
    }
}

impl<'a> CFG<'a> {
    pub fn new(func: &'a Function) -> Self {
        let blocks = Block::from_function(func);
        let label_map = resolve_labels(&blocks);
        let mut fb = FlowBuilder {
            flow: HashMap::new(),
            flow_r: HashMap::new(),
        };

        fb.flows(Node::Entry, Node::Block(0));

        for (i, block) in blocks.iter().enumerate() {
            if let Some(term) = &block.term {
                match term {
                    Instruction::Effect {
                        labels,
                        op: EffectOps::Jump | EffectOps::Branch,
                        ..
                    } => {
                        for target in labels {
                            let target: Node = label_map
                                .get(target)
                                .cloned()
                                .map_or(Node::Exit, Node::Block);
                            fb.flows(Node::Block(i), target);
                        }
                    }
                    Instruction::Effect {
                        op: EffectOps::Return,
                        ..
                    } => fb.flows(Node::Block(i), Node::Exit),
                    _ => {
                        let next_block = if i + 1 == blocks.len() {
                            Node::Exit
                        } else {
                            Node::Block(i + 1)
                        };
                        fb.flows(Node::Block(i), next_block);
                    }
                }
            } else {
                let next_block = if i + 1 == blocks.len() {
                    Node::Exit
                } else {
                    Node::Block(i + 1)
                };
                fb.flows(Node::Block(i), next_block);
            }
        }

        CFG {
            flow: fb.flow,
            flow_r: fb.flow_r,
            func,
            label_map,
            blocks,
        }
    }

    pub fn preorder(&self, reverse: bool) -> Vec<Node> {
        let mut visited = HashSet::new();
        let mut order = vec![];
        let mut queue = VecDeque::new();
        let f = if reverse { &self.flow_r } else { &self.flow };
        let start = if reverse { Node::Exit } else { Node::Entry };
        queue.push_back(start);
        while let Some(node) = queue.pop_front() {
            if visited.contains(&node) {
                continue;
            }
            visited.insert(node);
            order.push(node);
            if let Some(neighbors) = f.get(&node) {
                for neighbor in neighbors {
                    queue.push_back(*neighbor);
                }
            }
        }
        order
    }

    pub fn resolve(&self, label: &str) -> Node {
        if let Some(index) = self.label_map.get(label) {
            Node::Block(*index)
        } else {
            Node::Exit
        }
    }

    pub fn dot<F>(&self, f: &mut F) -> io::Result<()>
    where
        F: io::Write,
    {
        let node_id = |x: Node| match x {
            Node::Entry => "entry".to_string(),
            Node::Exit => "exit".to_string(),
            Node::Block(index) => index.to_string(),
        };

        let node_label = |x: Node| match x {
            Node::Entry | Node::Exit => node_id(x),
            Node::Block(index) => self.blocks[index].to_string(),
        };

        writeln!(f, "digraph {{")?;

        for node in self.flow.keys() {
            let label = node_label(*node);
            // Escape the newlines in the label
            let label = label.replace("\n", "\\l");
            // Use rectangles for blocks, and left-align text.
            if let Node::Block(_) = node {
                writeln!(
                    f,
                    "  {} [label=\"{}\", shape=box, align=left];",
                    node_id(*node),
                    label
                )?;
            } else {
                writeln!(f, "  {} [label=\"{}\"];", node_id(*node), label)?;
            }
        }

        for (src, dsts) in &self.flow {
            for dst in dsts {
                writeln!(f, "  {} -> {};", node_id(*src), node_id(*dst))?;
            }
        }

        writeln!(f, "}}")
    }

    // TODO(altanh): CFG simplification by merging basic blocks
}

/*#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Node {
    Entry,
    Exit,
    Inst(usize),
}

impl From<usize> for Node {
    fn from(value: usize) -> Self {
        Node::Inst(value)
    }
}

pub struct ControlFlowGraph<'a> {
    pub flow: HashMap<Node, HashSet<Node>>,
    pub flow_r: HashMap<Node, HashSet<Node>>,
    pub func: &'a Function,
    pub labels: HashMap<String, usize>,
}

impl<'a> ControlFlowGraph<'a> {
    pub fn new(func: &'a Function) -> Self {
        let mut cfg = ControlFlowGraph {
            flow: HashMap::new(),
            flow_r: HashMap::new(),
            func,
            labels: resolve_labels(func),
        };

        // Find the first instruction
        let first_inst: Node = next_inst(0, func).map_or(Node::Exit, Node::Inst);

        cfg.flows(Node::Entry, first_inst);

        for (i, inst) in func.instrs.iter().enumerate() {
            if let Code::Instruction(inst) = inst {
                match inst {
                    Instruction::Effect {
                        labels,
                        op: EffectOps::Jump | EffectOps::Branch,
                        ..
                    } => {
                        for target in labels {
                            let target: Node = if cfg.labels.contains_key(target) {
                                cfg.labels[target].into()
                            } else {
                                Node::Exit
                            };
                            cfg.flows(i, target);
                        }
                    }
                    Instruction::Effect {
                        op: EffectOps::Return,
                        ..
                    } => cfg.flows(i, Node::Exit),
                    _ => {
                        let next_inst: Node = next_inst(i + 1, func).map_or(Node::Exit, Node::Inst);
                        cfg.flows(i, next_inst);
                    }
                }
            }
        }

        cfg
    }

    pub fn flows<S, T>(&mut self, from: S, to: T)
    where
        S: Into<Node>,
        T: Into<Node>,
    {
        let from: Node = from.into();
        let to: Node = to.into();
        if let None = self.flow.get(&from) {
            self.flow.insert(from, HashSet::new());
            self.flow_r.insert(from, HashSet::new());
        }
        if let None = self.flow.get(&to) {
            self.flow.insert(to, HashSet::new());
            self.flow_r.insert(to, HashSet::new());
        }
        self.flow.get_mut(&from).unwrap().insert(to);
        self.flow_r.get_mut(&to).unwrap().insert(from);
    }

    pub fn dot<F>(&self, f: &mut F) -> io::Result<()>
    where
        F: io::Write,
    {
        let node_id = |x: Node| match x {
            Node::Entry => "entry".to_string(),
            Node::Exit => "exit".to_string(),
            Node::Inst(index) => index.to_string(),
        };

        let node_label = |x: Node| match x {
            Node::Entry | Node::Exit => node_id(x),
            Node::Inst(index) => self.func.instrs[index].to_string(),
        };

        writeln!(f, "digraph {{")?;

        for node in self.flow.keys() {
            writeln!(f, "  {} [label=\"{}\"];", node_id(*node), node_label(*node))?;
        }

        for (src, dsts) in &self.flow {
            for dst in dsts {
                writeln!(f, "  {} -> {};", node_id(*src), node_id(*dst))?;
            }
        }

        writeln!(f, "}}")
    }

    pub fn resolve(&self, label: &str) -> Node {
        if let Some(index) = self.labels.get(label) {
            Node::Inst(*index)
        } else {
            Node::Exit
        }
    }
}*/
