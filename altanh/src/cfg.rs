use core::panic;
use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt::Display,
    io,
};

use bril_rs::{Argument, Code, EffectOps, Function, Instruction, Type};

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Block {
    /// Non-control instructions
    pub insts: Vec<Instruction>,
    /// Terminating control instruction, or None if fallthrough
    pub term: Option<Instruction>,
    /// Label, if present
    pub label: Option<String>,
}

impl Block {
    pub fn new(insts: Vec<Instruction>, term: Option<Instruction>, label: Option<String>) -> Self {
        let block = Block { insts, term, label };
        block.validate();
        block
    }

    pub fn new_flat(mut insts: Vec<Instruction>, label: Option<String>) -> Self {
        let term = match insts.last() {
            Some(Instruction::Effect {
                op: EffectOps::Branch | EffectOps::Jump | EffectOps::Return,
                ..
            }) => Some(insts.pop().unwrap()),
            _ => None,
        };
        let block = Block { insts, term, label };
        block.validate();
        block
    }

    pub fn validate(&self) {
        // Check that there are no control instructions in insts
        for inst in &self.insts {
            match inst {
                Instruction::Effect {
                    op: EffectOps::Branch | EffectOps::Jump | EffectOps::Return,
                    ..
                } => panic!("Control instruction in insts: {} in\n{}", inst, self),
                _ => (),
            }
        }
        // Check that the terminator is a control instruction
        if let Some(term) = &self.term {
            match term {
                Instruction::Effect {
                    op: EffectOps::Branch | EffectOps::Jump | EffectOps::Return,
                    ..
                } => {}
                _ => panic!("Non-control terminator: {} in\n{}", term, self),
            }
        }
    }

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
                        op: EffectOps::Branch,
                        labels,
                        ..
                    } if labels[0] == labels[1] => {
                        // Normalize br x L L => jmp L
                        current.term = Some(Instruction::Effect {
                            args: vec![],
                            funcs: vec![],
                            labels: vec![labels[0].clone()],
                            op: EffectOps::Jump,
                        });
                        blocks.push(current);
                        current = Default::default();
                    }
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
            writeln!(f, "    # terminator")?;
            writeln!(f, "    {term}")?;
        } else {
            writeln!(f, "    # fallthrough")?;
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

#[derive(Debug, Clone)]
pub enum Guard {
    IfTrue(String),
    IfFalse(String),
    Always,
}

struct FlowBuilder<'a> {
    flow: &'a mut HashMap<Node, HashSet<Node>>,
    flow_r: &'a mut HashMap<Node, HashSet<Node>>,
    guards: &'a mut HashMap<(Node, Node), Guard>,
}

pub struct FunctionInfo {
    pub args: Vec<Argument>,
    pub name: String,
    pub return_type: Option<Type>,
}

impl FunctionInfo {
    pub fn new(func: &Function) -> Self {
        FunctionInfo {
            args: func.args.clone(),
            name: func.name.clone(),
            return_type: func.return_type.clone(),
        }
    }
}

pub struct CFG {
    pub flow: HashMap<Node, HashSet<Node>>,
    pub flow_r: HashMap<Node, HashSet<Node>>,
    pub guards: HashMap<(Node, Node), Guard>,
    pub func_info: FunctionInfo,
    pub label_map: HashMap<String, usize>,
    pub blocks: Vec<Block>,
    label_counter: usize,
}

impl<'a> FlowBuilder<'a> {
    pub fn flows<S, T>(&mut self, from: S, to: T, guard: Guard)
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
        self.guards.insert((from, to), guard);
    }

    pub fn unflows<S, T>(&mut self, from: S, to: T)
    where
        S: Into<Node>,
        T: Into<Node>,
    {
        let from: Node = from.into();
        let to: Node = to.into();
        if let Some(s) = self.flow.get_mut(&from) {
            s.remove(&to);
        }
        if let Some(s) = self.flow_r.get_mut(&to) {
            s.remove(&from);
        }
        self.guards.remove(&(from, to));
    }
}

impl CFG {
    pub fn new(func: &Function) -> Self {
        let blocks = Block::from_function(func);
        let label_map = resolve_labels(&blocks);
        let mut flow = HashMap::new();
        let mut flow_r = HashMap::new();
        let mut guards = HashMap::new();
        let mut fb = FlowBuilder {
            flow: &mut flow,
            flow_r: &mut flow_r,
            guards: &mut guards,
        };

        fb.flows(Node::Entry, Node::Block(0), Guard::Always);

        for (i, block) in blocks.iter().enumerate() {
            let this_node = Node::Block(i);
            if let Some(term) = &block.term {
                match term {
                    Instruction::Effect {
                        labels,
                        args,
                        op: EffectOps::Branch,
                        ..
                    } => {
                        let cond = args[0].clone();
                        let then_node = label_map
                            .get(&labels[0])
                            .map(|j| Node::Block(*j))
                            .expect(format!("Label not found: {}", &labels[0]).as_str());
                        let else_node = label_map
                            .get(&labels[1])
                            .map(|j| Node::Block(*j))
                            .expect(format!("Label not found: {}", &labels[1]).as_str());
                        fb.flows(this_node, then_node, Guard::IfTrue(cond.clone()));
                        fb.flows(this_node, else_node, Guard::IfFalse(cond));
                    }
                    Instruction::Effect {
                        labels,
                        op: EffectOps::Jump,
                        ..
                    } => {
                        let target_node = label_map
                            .get(&labels[0])
                            .map(|j| Node::Block(*j))
                            .expect(format!("Label not found: {}", &labels[0]).as_str());
                        fb.flows(this_node, target_node, Guard::Always);
                    }
                    Instruction::Effect {
                        op: EffectOps::Return,
                        ..
                    } => fb.flows(this_node, Node::Exit, Guard::Always),
                    _ => unreachable!(),
                }
            } else {
                let next_node = if i + 1 == blocks.len() {
                    Node::Exit
                } else {
                    Node::Block(i + 1)
                };
                fb.flows(this_node, next_node, Guard::Always);
            }
        }

        let mut res = CFG {
            flow,
            flow_r,
            guards,
            func_info: FunctionInfo::new(func),
            label_map,
            blocks,
            label_counter: 0,
        };
        res.split_critical_edges();
        res
    }

    pub fn resolve(&self, label: &str) -> Node {
        if let Some(index) = self.label_map.get(label) {
            Node::Block(*index)
        } else {
            panic!("Label not found: {}", label);
        }
    }

    pub fn get(&self, node: Node) -> Option<&Block> {
        if let Node::Block(i) = node {
            Some(&self.blocks[i])
        } else {
            None
        }
    }

    pub fn get_mut(&mut self, node: Node) -> Option<&mut Block> {
        if let Node::Block(i) = node {
            Some(&mut self.blocks[i])
        } else {
            None
        }
    }

    fn _get(&mut self, node: Node) -> &mut Block {
        if let Node::Block(i) = node {
            &mut self.blocks[i]
        } else {
            panic!("cannot get entry or exit nodes!");
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
            Node::Block(index) => format!("# block {index}\n{}", &self.blocks[index]),
            _ => unreachable!(),
        };

        writeln!(f, "digraph {{")?;

        for node in self.flow.keys() {
            // Set the rank of entry to source and exit to sink
            match node {
                Node::Entry => {
                    writeln!(
                        f,
                        "  {{ rank=source; {} [label=\"entry\"]; }}",
                        node_id(*node)
                    )?;
                }
                Node::Exit => {
                    writeln!(f, "  {{ rank=sink; {} [label=\"exit\"]; }}", node_id(*node))?;
                }
                _ => {
                    let label = node_label(*node);
                    // Escape the newlines in the label
                    let label = label.replace("\n", "\\l");
                    writeln!(f, "  {} [label=\"{}\", shape=box];", node_id(*node), label)?;
                }
            }
        }

        for (src, dsts) in &self.flow {
            for dst in dsts {
                let guard = match &self.guards[&(*src, *dst)] {
                    Guard::Always => "1".to_string(),
                    Guard::IfTrue(x) => x.clone(),
                    Guard::IfFalse(x) => format!("!{x}"),
                };
                writeln!(
                    f,
                    "  {} -> {} [label=\"{}\"];",
                    node_id(*src),
                    node_id(*dst),
                    guard
                )?;
            }
        }

        writeln!(f, "}}")
    }

    // TODO(altanh): CFG simplification by merging basic blocks
}

impl CFG {
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

    // TODO(altanh): switch to iterative traversal if this ever blows the stack
    pub fn postorder(&self, reverse: bool) -> VecDeque<Node> {
        fn visit(
            node: Node,
            cfg: &CFG,
            reverse: bool,
            result: &mut VecDeque<Node>,
            visited: &mut HashSet<Node>,
        ) {
            if visited.contains(&node) {
                return;
            }
            visited.insert(node);
            if let Some(succs) = cfg.flow.get(&node) {
                for succ in succs {
                    visit(*succ, cfg, reverse, result, visited);
                }
            }
            if reverse {
                result.push_front(node);
            } else {
                result.push_back(node);
            }
        }
        let mut result: VecDeque<Node> = Default::default();
        let mut visited: HashSet<Node> = Default::default();
        visit(Node::Entry, self, reverse, &mut result, &mut visited);
        result
    }

    /// Returns the dom-tree of the CFG: a map from each node to its immediate
    /// dominator. This algorithm is from "A Simple, Fast Dominance Algorithm" by
    /// Cooper, Harvey, and Kennedy.
    pub fn dom_tree(&self) -> HashMap<Node, Node> {
        fn intersect(
            b1: Node,
            b2: Node,
            doms: &HashMap<Node, Node>,
            rpo_number: &HashMap<Node, usize>,
        ) -> Node {
            let mut f1 = b1;
            let mut f2 = b2;
            while f1 != f2 {
                while rpo_number[&f1] > rpo_number[&f2] {
                    f1 = doms[&f1];
                }
                while rpo_number[&f2] > rpo_number[&f1] {
                    f2 = doms[&f2];
                }
            }
            f1
        }
        let rpo = self.postorder(true);
        let rpo_number: HashMap<Node, usize> =
            rpo.iter().enumerate().map(|(i, n)| (*n, i)).collect();
        let mut doms: HashMap<Node, Node> = HashMap::new();
        doms.insert(Node::Entry, Node::Entry);
        let mut changed = true;
        while changed {
            changed = false;
            for n in &rpo {
                if *n == Node::Entry {
                    continue;
                }
                // Get list of processed predecessor nodes
                let ps: Vec<Node> = self.flow_r[n]
                    .iter()
                    .filter(|p| doms.contains_key(p))
                    .cloned()
                    .collect();
                // Fold using intersect
                let new_idom = ps[1..]
                    .iter()
                    .fold(ps[0], |b1, b2| intersect(b1, *b2, &doms, &rpo_number));
                if !doms.contains_key(n) || doms[n] != new_idom {
                    doms.insert(*n, new_idom);
                    changed = true;
                }
            }
        }
        doms
    }
}

/// True iff a dominates b.
pub fn dominates(a: Node, mut b: Node, dom_tree: &HashMap<Node, Node>) -> bool {
    loop {
        if a == b {
            return true;
        }
        if b == Node::Entry {
            return false;
        }
        if let Some(p) = dom_tree.get(&b) {
            b = *p;
        } else {
            // Unreachable node
            return false;
        }
    }
}

impl CFG {
    fn fresh_label(&mut self) -> String {
        loop {
            let label = format!("L{}", self.label_counter);
            self.label_counter += 1;
            if !self.label_map.contains_key(&label) {
                return label;
            }
        }
    }

    fn insert_block(&mut self) -> Node {
        // Insert a new block at the end, and patch the previous end in case it
        // fell through to exit
        if let Some(block) = self.blocks.last_mut() {
            if let None = block.term {
                block.term = Some(Instruction::Effect {
                    args: vec![],
                    funcs: vec![],
                    labels: vec![],
                    op: EffectOps::Return,
                });
            }
        }
        let label = self.fresh_label();
        self.blocks.push(Block {
            insts: vec![],
            term: None,
            label: Some(label),
        });
        Node::Block(self.blocks.len() - 1)
    }

    /// Split the edge (from -> to) by inserting an empty basic block between
    /// from and to
    pub fn split_edge(&mut self, (from, to): (Node, Node)) -> Node {
        assert!(self.flow[&from].contains(&to));
        assert!(!matches!(from, Node::Entry | Node::Exit));
        assert!(!matches!(to, Node::Entry | Node::Exit));
        let new = self.insert_block();
        let new_label = self._get(new).label.clone().unwrap();
        // First, ensure that `to` has a label
        if let None = self._get(to).label {
            self._get(to).label = Some(self.fresh_label());
        }
        let to_label = self._get(to).label.clone().unwrap();
        // Jump from the new block to `to`
        self._get(new).term = Some(Instruction::Effect {
            args: vec![],
            funcs: vec![],
            labels: vec![to_label.clone()],
            op: EffectOps::Jump,
        });
        // Fix `from` terminator. There are 3 cases:
        // 1. `from` falls through to `to`; insert a jump terminator for `from`
        //    and point it to the label of the new intermediate
        // 2. `from` jumps to `to`; replace the label
        // 3. `from` branches to `to`; replace the label for `to` in the branch
        match self._get(from).term.clone() {
            None
            | Some(Instruction::Effect {
                op: EffectOps::Jump,
                ..
            }) => {
                self._get(from).term = Some(Instruction::Effect {
                    args: vec![],
                    funcs: vec![],
                    labels: vec![new_label],
                    op: EffectOps::Jump,
                });
            }
            Some(Instruction::Effect {
                args,
                funcs,
                labels,
                op: EffectOps::Branch,
            }) => {
                let labels: Vec<String> = labels
                    .into_iter()
                    .map(|l| if l == to_label { new_label.clone() } else { l })
                    .collect();
                self._get(from).term = Some(Instruction::Effect {
                    args,
                    funcs,
                    labels,
                    op: EffectOps::Branch,
                });
            }
            _ => unreachable!(),
        }
        // Fix the flow graph
        let mut fb = FlowBuilder {
            flow: &mut self.flow,
            flow_r: &mut self.flow_r,
            guards: &mut self.guards,
        };
        fb.flows(from, new, fb.guards[&(from, to)].clone());
        fb.flows(new, to, Guard::Always);
        fb.unflows(from, to);
        new
    }

    pub fn split_critical_edges(&mut self) {
        // Collect critical edges. A critical edge is an edge (from, to) such
        // that from has multiple successors and to has multiple predecessors.
        let mut crit_edges: Vec<(Node, Node)> = vec![];
        for (from, tos) in self.flow.iter().filter(|(_, tos)| tos.len() > 1) {
            for to in tos.iter().filter(|to| self.flow_r[to].len() > 1) {
                crit_edges.push((*from, *to));
            }
        }
        for crit in crit_edges {
            self.split_edge(crit);
        }
    }

    pub fn lower(&self) -> Function {
        let mut instrs: Vec<Code> = vec![];
        for block in &self.blocks {
            block.emit(&mut instrs);
        }
        Function {
            args: self.func_info.args.clone(),
            instrs,
            name: self.func_info.name.clone(),
            return_type: self.func_info.return_type.clone(),
        }
    }
}
