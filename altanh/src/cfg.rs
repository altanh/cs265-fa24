use core::panic;
use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt::Display,
    io,
};

use bril_rs::{Argument, Code, EffectOps, Function, Instruction, Type};

pub struct Labels {
    pub labels: HashSet<String>,
    pub mapping: HashMap<String, Node>,
    counter: usize,
}

impl Labels {
    pub fn collect(code: &Vec<Code>) -> Labels {
        let mut labels: HashSet<String> = Default::default();
        for c in code {
            if let Code::Label { label } = c {
                labels.insert(label.clone());
            }
        }
        Labels {
            labels,
            mapping: Default::default(),
            counter: 0,
        }
    }

    pub fn fresh(&mut self) -> String {
        loop {
            let l = format!("L{}", self.counter);
            self.counter += 1;
            if !self.labels.contains(&l) {
                self.labels.insert(l.clone());
                return l;
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Block {
    /// Non-control instructions
    pub insts: Vec<Instruction>,
    /// Terminating control instruction
    pub term: Instruction,
    /// Label, if present
    pub label: String,
}

pub struct BlockBuilder {
    pub insts: Vec<Instruction>,
    pub label: Option<String>,
}

#[derive(Debug, Clone)]
pub enum Fallthrough {
    Next(String),
    Exit,
    None,
}

impl BlockBuilder {
    pub fn new(label: Option<String>) -> Self {
        BlockBuilder {
            insts: vec![],
            label,
        }
    }

    pub fn push(&mut self, inst: Instruction) {
        self.insts.push(inst);
    }

    pub fn complete(
        mut self,
        number: Option<usize>,
        fallthrough: Fallthrough,
        labels: &mut Labels,
    ) -> Block {
        let last = self.insts.last().cloned();
        let term = match (last, fallthrough) {
            (
                Some(
                    term @ Instruction::Effect {
                        op: EffectOps::Jump | EffectOps::Branch | EffectOps::Return,
                        ..
                    },
                ),
                _,
            ) => {
                self.insts.pop();
                term
            }
            (_, Fallthrough::Next(target)) => Instruction::Effect {
                args: vec![],
                funcs: vec![],
                labels: vec![target],
                op: EffectOps::Jump,
            },
            (_, Fallthrough::Exit) => Instruction::Effect {
                args: vec![],
                funcs: vec![],
                labels: vec![],
                op: EffectOps::Return,
            },
            _ => {
                unreachable!()
            }
        };
        let block = Block {
            insts: self.insts,
            term,
            label: self.label.unwrap_or_else(|| labels.fresh()),
        };
        block.validate();
        if let Some(number) = number {
            labels
                .mapping
                .insert(block.label.clone(), Node::Block(number));
        }
        block
    }

    pub fn is_empty(&self) -> bool {
        self.insts.is_empty() && self.label.is_none()
    }
}

impl Block {
    pub fn new(insts: Vec<Instruction>, term: Instruction, label: String) -> Self {
        let block = Block { insts, term, label };
        block.validate();
        block
    }

    pub fn new_flat(mut insts: Vec<Instruction>, label: String) -> Self {
        let term = match insts.last() {
            Some(Instruction::Effect {
                op: EffectOps::Branch | EffectOps::Jump | EffectOps::Return,
                ..
            }) => insts.pop().unwrap(),
            _ => panic!("blocks must end with a control instruction"),
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
        match &self.term {
            Instruction::Effect {
                op: EffectOps::Branch | EffectOps::Jump | EffectOps::Return,
                ..
            } => {}
            _ => panic!("Non-control terminator: {} in\n{}", &self.term, self),
        }
    }

    pub fn from_function(func: &Function) -> (Vec<Block>, Labels) {
        let mut labels: Labels = Labels::collect(&func.instrs);
        let mut blocks: Vec<Block> = vec![];
        let mut bb: BlockBuilder = BlockBuilder::new(None);
        for code in &func.instrs {
            match code {
                Code::Label { label, .. } => {
                    if !bb.is_empty() {
                        blocks.push(bb.complete(
                            blocks.len().into(),
                            Fallthrough::Next(label.clone()),
                            &mut labels,
                        ));
                    }
                    bb = BlockBuilder::new(Some(label.clone()));
                }
                Code::Instruction(inst) => match inst {
                    Instruction::Effect {
                        op: EffectOps::Branch,
                        labels: ls,
                        ..
                    } if ls[0] == ls[1] => {
                        // Normalize br x L L => jmp L
                        bb.push(Instruction::Effect {
                            args: vec![],
                            funcs: vec![],
                            labels: vec![ls[0].clone()],
                            op: EffectOps::Jump,
                        });
                        blocks.push(bb.complete(
                            blocks.len().into(),
                            Fallthrough::None,
                            &mut labels,
                        ));
                        bb = BlockBuilder::new(None);
                    }
                    Instruction::Effect {
                        op: EffectOps::Branch | EffectOps::Jump | EffectOps::Return,
                        ..
                    } => {
                        bb.push(inst.clone());
                        blocks.push(bb.complete(
                            blocks.len().into(),
                            Fallthrough::None,
                            &mut labels,
                        ));
                        bb = BlockBuilder::new(None);
                    }
                    _ => {
                        bb.push(inst.clone());
                    }
                },
            }
        }
        if !bb.is_empty() {
            blocks.push(bb.complete(blocks.len().into(), Fallthrough::Exit, &mut labels));
        }
        (blocks, labels)
    }

    pub fn emit(&self, out: &mut Vec<Code>) {
        out.push(Code::Label {
            label: self.label.clone(),
        });
        for inst in &self.insts {
            out.push(Code::Instruction(inst.clone()));
        }
        out.push(Code::Instruction(self.term.clone()));
    }
}

impl Display for Block {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, ".{}:", self.label)?;
        for inst in &self.insts {
            writeln!(f, "    {inst}")?;
        }
        writeln!(f, "    {}", self.term)?;
        Ok(())
    }
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

impl<'a> FlowBuilder<'a> {
    fn with(cfg: &'a mut CFG) -> Self {
        FlowBuilder {
            flow: &mut cfg.flow,
            flow_r: &mut cfg.flow_r,
            guards: &mut cfg.guards,
        }
    }
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
    pub labels: Labels,
    pub blocks: Vec<Block>,
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
        let (blocks, labels) = Block::from_function(func);
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
            match &block.term {
                Instruction::Effect {
                    labels: ls,
                    args,
                    op: EffectOps::Branch,
                    ..
                } => {
                    let cond = args[0].clone();
                    let then_node = labels
                        .mapping
                        .get(&ls[0])
                        .expect(format!("Label not found: {}", &ls[0]).as_str());
                    let else_node = labels
                        .mapping
                        .get(&ls[1])
                        .expect(format!("Label not found: {}", &ls[1]).as_str());
                    fb.flows(this_node, *then_node, Guard::IfTrue(cond.clone()));
                    fb.flows(this_node, *else_node, Guard::IfFalse(cond));
                }
                Instruction::Effect {
                    labels: ls,
                    op: EffectOps::Jump,
                    ..
                } => {
                    let target_node = labels
                        .mapping
                        .get(&ls[0])
                        .expect(format!("Label not found: {}", &ls[0]).as_str());
                    fb.flows(this_node, *target_node, Guard::Always);
                }
                Instruction::Effect {
                    op: EffectOps::Return,
                    ..
                } => fb.flows(this_node, Node::Exit, Guard::Always),
                _ => unreachable!(),
            }
        }

        let mut res = CFG {
            flow,
            flow_r,
            guards,
            func_info: FunctionInfo::new(func),
            labels,
            blocks,
        };
        res.split_critical_edges();
        res
    }

    pub fn resolve(&self, label: &str) -> Node {
        if let Some(node) = self.labels.mapping.get(label) {
            *node
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
    fn insert_block(&mut self) -> Node {
        let number = self.blocks.len();
        self.blocks.push(BlockBuilder::new(None).complete(
            number.into(),
            Fallthrough::Exit,
            &mut self.labels,
        ));
        let block = Node::Block(number);
        let mut fb = FlowBuilder::with(self);
        fb.flows(block, Node::Exit, Guard::Always);
        block
    }

    fn update_term(&mut self, node: Node, term: Instruction) {
        let transitions = match &term {
            Instruction::Effect {
                op: EffectOps::Return,
                ..
            } => vec![(Node::Exit, Guard::Always)],
            Instruction::Effect {
                op: EffectOps::Jump,
                labels,
                ..
            } => vec![(self.resolve(labels[0].as_str()), Guard::Always)],
            Instruction::Effect {
                op: EffectOps::Branch,
                args,
                labels,
                ..
            } => vec![
                (
                    self.resolve(labels[0].as_str()),
                    Guard::IfTrue(args[0].clone()),
                ),
                (
                    self.resolve(labels[1].as_str()),
                    Guard::IfFalse(args[0].clone()),
                ),
            ],
            _ => panic!("invalid terminator: {}", term),
        };
        // Remove existing transitions
        for s in self.flow[&node].clone() {
            let mut fb = FlowBuilder::with(self);
            fb.unflows(node, s);
        }
        // Insert new transitions
        for (s, g) in transitions {
            let mut fb = FlowBuilder::with(self);
            fb.flows(node, s, g);
        }
        // Update term
        self.get_mut(node).unwrap().term = term;
    }

    /// Split the edge (from -> to) by inserting an empty basic block between
    /// from and to
    pub fn split_edge(&mut self, (from, to): (Node, Node)) -> Node {
        assert!(self.flow[&from].contains(&to));
        assert!(!matches!(from, Node::Entry | Node::Exit));
        assert!(!matches!(to, Node::Entry | Node::Exit));
        let new = self.insert_block();
        let to_label = self._get(to).label.clone();
        // Jump from the new block to `to`
        self.update_term(
            new,
            Instruction::Effect {
                args: vec![],
                funcs: vec![],
                labels: vec![to_label.clone()],
                op: EffectOps::Jump,
            },
        );
        // Fix `from` terminator. There are 3 cases:
        // 1. `from` falls through to `to`; insert a jump terminator for `from`
        //    and point it to the label of the new intermediate
        // 2. `from` jumps to `to`; replace the label
        // 3. `from` branches to `to`; replace the label for `to` in the branch
        let new_label = self.get(new).unwrap().label.clone();
        match self.get(from).unwrap().term.clone() {
            Instruction::Effect {
                op: EffectOps::Jump,
                ..
            } => {
                self.update_term(
                    from,
                    Instruction::Effect {
                        args: vec![],
                        funcs: vec![],
                        labels: vec![new_label],
                        op: EffectOps::Jump,
                    },
                );
            }
            Instruction::Effect {
                args,
                funcs,
                labels,
                op: EffectOps::Branch,
            } => {
                let labels: Vec<String> = labels
                    .into_iter()
                    .map(|l| if l == to_label { new_label.clone() } else { l })
                    .collect();
                self.update_term(
                    from,
                    Instruction::Effect {
                        args,
                        funcs,
                        labels,
                        op: EffectOps::Branch,
                    },
                );
            }
            x => {
                dbg!(x);
                unreachable!();
            }
        }
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

/// Header -> Nodes in loop
pub type NaturalLoops = HashMap<(Node, Node), HashSet<Node>>;

impl CFG {
    pub fn natural_loops(&self) -> NaturalLoops {
        let dom_tree = self.dom_tree();
        // Identify back edges src -> dst s.t. dst dominates src
        let mut backedges: Vec<(Node, Node)> = vec![];
        for (&src, dsts) in &self.flow {
            for &dst in dsts {
                if dominates(dst, src, &dom_tree) {
                    backedges.push((src, dst));
                }
            }
        }
        // Find the nodes in each natural loop
        let mut loops: NaturalLoops = Default::default();
        for (tail, header) in backedges {
            // The nodes in the loop defined by (tail, header) are the predecessors
            // of tail that are also dominated by header
            let nodes = loops.entry((tail, header)).or_default();
            nodes.insert(header);
            let mut queue: VecDeque<Node> = Default::default();
            queue.push_back(tail);
            while let Some(node) = queue.pop_front() {
                if nodes.contains(&node) || !dominates(header, node, &dom_tree) {
                    continue;
                }
                nodes.insert(node);
                for &p in &self.flow_r[&node] {
                    queue.push_back(p);
                }
            }
        }
        loops
    }

    /// while C { B } => if C { do { B } while C }
    pub fn rotate_loops(&mut self) {
        // We only consider loops with headers that have one edge entering the
        // loop body and one edge exiting.
        let loops: Vec<((Node, Node), HashSet<Node>)> = self
            .natural_loops()
            .into_iter()
            .filter(|((_, header), nodes)| {
                if self.flow[&header].len() == 2 {
                    let mut out = self.flow[&header].iter().cloned();
                    let x = out.next().unwrap();
                    let y = out.next().unwrap();
                    match (nodes.contains(&x), nodes.contains(&y)) {
                        (true, false) | (false, true) => true,
                        _ => false,
                    }
                } else {
                    false
                }
            })
            .collect();
        for ((_, header), nodes) in loops {
            // 1. Duplicate header node
            let header_block = self.get(header).unwrap().clone();
            let header_copy = self.insert_block();
            self.get_mut(header_copy).unwrap().insts = header_block.insts;
            self.update_term(header_copy, header_block.term);
            // 2. Update non-loop predecessors of the original header to point
            //    to the new header.
            let old_label = header_block.label;
            let new_label = self.get(header_copy).unwrap().label.clone();
            for p in self.flow_r[&header].clone() {
                if nodes.contains(&p) {
                    continue;
                }
                if p == Node::Entry {
                    // Just directly update the entry flow
                    let mut fb = FlowBuilder::with(self);
                    fb.unflows(p, header);
                    fb.flows(p, header_copy, Guard::Always);
                } else {
                    let new_term = match &self.get(p).unwrap().term {
                        Instruction::Effect {
                            op: EffectOps::Jump,
                            ..
                        } => Instruction::Effect {
                            args: vec![],
                            funcs: vec![],
                            labels: vec![new_label.clone()],
                            op: EffectOps::Jump,
                        },
                        Instruction::Effect {
                            op: EffectOps::Branch,
                            args,
                            labels,
                            ..
                        } => {
                            let labels: Vec<String> = labels
                                .iter()
                                .map(|l| {
                                    if *l == old_label {
                                        new_label.clone()
                                    } else {
                                        l.clone()
                                    }
                                })
                                .collect();
                            Instruction::Effect {
                                args: args.clone(),
                                funcs: vec![],
                                labels,
                                op: EffectOps::Branch,
                            }
                        }
                        _ => unreachable!(),
                    };
                    self.update_term(p, new_term);
                }
            }
        }
        self.split_critical_edges();
    }
}

impl CFG {
    pub fn emit(&self) -> Function {
        let mut code: Vec<Code> = vec![];
        for block in &self.blocks {
            block.emit(&mut code);
        }
        Function {
            args: self.func_info.args.clone(),
            instrs: code,
            name: self.func_info.name.clone(),
            return_type: self.func_info.return_type.clone(),
        }
    }
}
