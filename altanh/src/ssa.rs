use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    io,
};

use bril_rs::{Code, EffectOps, Function, Instruction, Literal, ValueOps};

// TODO(altanh): intern
type Var = String;
type Location = Node;
type ValueNumber = usize;

type SymVar = (ValueNumber, Location);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Op {
    Builtin(ValueOps),
    Extern(String),
}
pub enum Expr {
    Const(Literal),
    Var(Var),
    Op(Op, Vec<Expr>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SymExpr {
    Const(Literal),
    Var(SymVar),
    Op(Op, Vec<ValueNumber>),
    Bot,
}

impl From<Literal> for Expr {
    fn from(lit: Literal) -> Self {
        Expr::Const(lit)
    }
}

impl From<Literal> for SymExpr {
    fn from(lit: Literal) -> Self {
        SymExpr::Const(lit)
    }
}

impl From<Var> for Expr {
    fn from(var: Var) -> Self {
        Expr::Var(var)
    }
}

impl From<SymVar> for SymExpr {
    fn from(var: SymVar) -> Self {
        SymExpr::Var(var)
    }
}

#[derive(Debug, Default)]
pub struct HashCons(HashMap<SymExpr, ValueNumber>, HashMap<ValueNumber, SymExpr>);

impl HashCons {
    /// Warning: this will always return a new value number!
    pub fn symbolic_var(&mut self, loc: Location) -> ValueNumber {
        let n = self.0.len();
        let v = SymExpr::Var((n, loc));
        self.0.insert(v.clone(), n);
        self.1.insert(n, v);
        n
    }

    pub fn intern(&mut self, se: SymExpr) -> ValueNumber {
        if let Some(n) = self.0.get(&se) {
            *n
        } else {
            let n = self.0.len();
            self.0.insert(se.clone(), n);
            self.1.insert(n, se);
            n
        }
    }

    pub fn transpose(&self) -> &HashMap<ValueNumber, SymExpr> {
        &self.1
    }

    pub fn dot<F>(&self, f: &mut F, g: &GlobalPhi) -> io::Result<()>
    where
        F: io::Write,
    {
        writeln!(f, "digraph {{")?;
        for (se, n) in &self.0 {
            let s = match se {
                SymExpr::Const(lit) => format!("{n} = {:?}", lit),
                // SymExpr::Var((n, loc)) => format!("{}@{:?}", n, loc),
                SymExpr::Var((_, loc)) => format!("X{n} @ {loc:?}"),
                SymExpr::Op(Op::Builtin(op), _) => {
                    format!("{n} = {:?}", op)
                }
                SymExpr::Op(Op::Extern(func), _) => {
                    format!("{n} = {}", func)
                }
                SymExpr::Bot => "⊥".to_string(),
            };
            writeln!(f, "  {} [label=\"{}\"];", n, s)?;
        }
        for (_, phi) in &g.phis {
            for (vars, val) in phi {
                for v in vars {
                    writeln!(f, "  {} -> {};", val, v.1)?;
                }
            }
        }
        for (se, n) in &self.0 {
            if let SymExpr::Op(_, args) = se {
                for arg in args {
                    // Write dotted edge
                    writeln!(f, "  {} -> {} [style=dotted];", n, arg)?;
                }
            }
        }
        writeln!(f, "}}")
    }
}

/// TODO(altanh): functional map
pub type AStore = HashMap<Var, ValueNumber>;

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

fn eval_symbolic(e: &Expr, ctx: &AStore, hc: &mut HashCons) -> ValueNumber {
    match e {
        Expr::Const(lit) => hc.intern(lit.clone().into()),
        // TODO(altanh): fix this?
        Expr::Var(x) => ctx.get(x).unwrap().clone(),
        // TODO(altanh): principled constant folding / rewriting
        Expr::Op(Op::Builtin(ValueOps::Id), args) => {
            let arg = eval_symbolic(&args[0], ctx, hc);
            arg
        }
        Expr::Op(op, args) => {
            let args: Vec<ValueNumber> = args.iter().map(|e| eval_symbolic(e, ctx, hc)).collect();
            hc.intern(SymExpr::Op(op.clone(), args))
        }
    }
}

fn step_symbolic(i: &Instruction, ctx: &mut AStore, hc: &mut HashCons) {
    match i {
        Instruction::Constant { dest, value, .. } => {
            ctx.insert(dest.clone(), hc.intern(value.clone().into()));
        }
        Instruction::Value {
            dest,
            op: ValueOps::Call,
            args,
            funcs,
            ..
        } => {
            ctx.insert(
                dest.clone(),
                eval_symbolic(
                    &Expr::Op(
                        Op::Extern(funcs[0].clone()),
                        args.iter().map(|x| Expr::Var(x.clone())).collect(),
                    ),
                    &ctx,
                    hc,
                ),
            );
        }
        Instruction::Value { args, dest, op, .. } => {
            ctx.insert(
                dest.clone(),
                eval_symbolic(
                    &Expr::Op(
                        Op::Builtin(op.clone()),
                        args.iter().map(|x| Expr::Var(x.clone())).collect(),
                    ),
                    &ctx,
                    hc,
                ),
            );
        }
        _ => (),
    }
}

type PhiArgs = Vec<(Node, ValueNumber)>;
type Phi = HashMap<PhiArgs, ValueNumber>;

#[derive(Debug, Default)]
pub struct GlobalPhi {
    pub phis: HashMap<Node, Phi>,
    symvars: HashMap<(Vec<Var>, Location), ValueNumber>,
}

impl Display for GlobalPhi {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (node, phi) in &self.phis {
            writeln!(f, "{:?}:", node)?;
            for (vars, val) in phi {
                writeln!(f, "    {:?} -> {}", vars, val)?;
            }
        }
        Ok(())
    }
}

impl GlobalPhi {
    fn clear(&mut self, at: Node) {
        self.phis.remove(&at);
    }

    fn entry(&mut self, node: Node) -> &mut Phi {
        self.phis.entry(node).or_insert(Default::default())
    }

    // TODO(altanh): according to the paper, this way of doing it is completely
    // unnecessary; it should be achievable without tracking the set of
    // equivalent variables. However, without this I am unable to get a
    // terminating analysis. Skill issue.
    fn insert_phis(
        &mut self,
        loc: Location,
        store: HashMap<String, PhiArgs>,
        hc: &mut HashCons,
    ) -> AStore {
        self.clear(loc);
        // Collect all variables with the same phi arguments
        let mut vars: HashMap<PhiArgs, Vec<String>> = HashMap::new();
        for (k, args) in &store {
            vars.entry(args.clone())
                .or_insert_with(Vec::new)
                .push(k.clone());
        }
        // Create symbolic variables for each set of equal variables and update
        // phi entries
        let mut result: AStore = Default::default();
        for (args, vars) in vars {
            let val = match args.len() {
                0 => hc.intern(SymExpr::Bot),
                1 => args[0].1,
                _ => {
                    let val = *self
                        .symvars
                        .entry((vars.clone(), loc))
                        .or_insert_with(|| hc.symbolic_var(loc));
                    // TODO(altanh): is this valid?
                    // Filter out recursive uses in the phi arguments
                    let args: PhiArgs = args.into_iter().filter(|(_, v)| *v != val).collect();
                    match args.len() {
                        0 => hc.intern(SymExpr::Bot),
                        1 => args[0].1,
                        _ => {
                            self.entry(loc).insert(args, val);
                            val
                        }
                    }
                }
            };
            for var in vars {
                result.insert(var, val);
            }
        }
        result
    }
}

impl Display for HashCons {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Print the map in transposed form
        for (k, v) in &self.0 {
            writeln!(f, "{}: {:?}", v, k)?;
        }
        Ok(())
    }
}

fn join(
    stores: Vec<(Node, &Option<AStore>)>,
    loc: Location,
    phis: &mut GlobalPhi,
    hc: &mut HashCons,
) -> Option<AStore> {
    // Filter out undefined stores
    let mut stores: Vec<(Node, &AStore)> = stores
        .into_iter()
        .filter_map(|(n, a)| Some((n, a.as_ref()?)))
        .collect();
    // Sort the stores by source node for consistency
    stores.sort_by_key(|(n, _)| *n);
    if stores.is_empty() {
        None
    } else {
        // Merge the stores: each variable is mapped to the list of value
        // numbers it takes on at the join point. We track the source node as
        // well to prevent incorrect phi function equalities.
        let mut result: HashMap<String, (PhiArgs, HashSet<ValueNumber>)> = HashMap::new();
        for (n, s) in stores {
            for (x, e) in s {
                let entry = result
                    .entry(x.clone())
                    .or_insert_with(|| (vec![], HashSet::new()));
                // Skip undefined values. Warning: this assumes that the
                // value number for undefined is always 0. Also skip if the
                // value number is already present.
                if *e == 0 || entry.1.contains(e) {
                    continue;
                }
                entry.0.push((n, *e));
                entry.1.insert(*e);
            }
        }
        Some(phis.insert_phis(
            loc,
            result.into_iter().map(|(k, (v, _))| (k, v)).collect(),
            hc,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::collect_vars;
    use std::collections::{HashMap, VecDeque};

    #[test]
    fn ssa_blocks() {
        let prog = bril_rs::load_program();
        for func in &prog.functions {
            let cfg = CFG::new(func);

            // Write the CFG to a file
            let mut file = std::fs::File::create(format!("dot/{}.dot", func.name)).unwrap();
            cfg.dot(&mut file).unwrap();
        }
    }

    #[test]
    fn ssa_basic() {
        let prog = bril_rs::load_program();
        for func in &prog.functions {
            let cfg = super::CFG::new(func);
            let mut hc: HashCons = Default::default();
            let mut phis: GlobalPhi = Default::default();

            hc.intern(SymExpr::Bot);

            // Initial abstract store: every variable is mapped to its own
            // unique value number at the entry block.
            let vars = collect_vars(func);
            let mut initial: AStore = HashMap::new();
            for var in &vars {
                if func.args.iter().any(|arg| arg.name == *var) {
                    initial.insert(var.clone(), hc.symbolic_var(Node::Entry));
                } else {
                    initial.insert(var.clone(), hc.intern(SymExpr::Bot));
                }
            }

            let mut abs: HashMap<Node, Option<AStore>> = HashMap::new();
            for node in cfg.flow.keys() {
                abs.insert(*node, None);
            }
            abs.insert(Node::Entry, Some(initial));

            // Initialize worklist with preorder traversal of the CFG
            // let mut stack: Vec<Node> = vec![Node::Entry];
            let mut queue: VecDeque<Node> = VecDeque::new();
            queue.push_back(Node::Entry);
            let mut visited: HashSet<Node> = HashSet::new();
            let mut worklist: VecDeque<Node> = VecDeque::new();
            while let Some(node) = queue.pop_front() {
                if visited.contains(&node) {
                    continue;
                }
                visited.insert(node);
                worklist.push_back(node);
                if let Some(succs) = cfg.flow.get(&node) {
                    for succ in succs {
                        queue.push_back(*succ);
                    }
                }
            }
            println!("worklist: {:?}", worklist);
            // let mut worklist: Vec<Node> = cfg.flow.keys().cloned().collect();

            let mut iter = 0;
            while let Some(n) = worklist.pop_front() {
                println!("iter {iter} at {n:?}: ");
                if let Node::Block(i) = n {
                    // assert!(cfg.flow_r[&n].len() <= 1);
                    // let mut astore = abs[&n].clone();
                    let ps: Vec<(Node, &Option<AStore>)> =
                        cfg.flow_r[&n].iter().map(|m| (*m, &abs[m])).collect();
                    let astore = join(ps, n, &mut phis, &mut hc);
                    // let astore = abs[cfg.flow_r[&n].iter().next().unwrap()].clone();
                    if let Some(mut astore) = astore {
                        // Symbolically execute the block
                        for inst in &cfg.blocks[i].insts {
                            step_symbolic(inst, &mut astore, &mut hc);
                        }
                        // If something changed, push successors
                        let astore = Some(astore);
                        if astore != abs[&n] {
                            // Print the diff
                            println!("update at {:?}", n);
                            if let Some(astore) = &astore {
                                let ch = hc.transpose();
                                for (var, val) in astore {
                                    println!(
                                        "    {}: {} -> {:?}",
                                        var,
                                        if let Some(a) = &abs[&n] {
                                            format!("{:?}", ch[a.get(var).unwrap()])
                                        } else {
                                            "⊥".to_string()
                                        },
                                        ch[val]
                                    );
                                }
                            }
                            abs.insert(n, astore.clone());
                            for succ in &cfg.flow[&n] {
                                worklist.push_back(*succ);
                            }
                        }
                    } else {
                        continue;
                    }
                } else {
                    // Always push successors for entry and exit nodes
                    for succ in &cfg.flow[&n] {
                        worklist.push_back(*succ);
                    }
                }
                iter += 1;
            }

            // Print the abstract store at each block
            let ch = hc.transpose();
            for (node, store) in &abs {
                let node_name = match node {
                    Node::Block(i) => cfg.blocks[*i]
                        .label
                        .clone()
                        .unwrap_or_else(|| i.to_string()),
                    _ => format!("{:?}", node),
                };
                println!("{node_name}:");
                if let Some(store) = store {
                    for (var, val) in store {
                        println!("    {}: {:?}", var, ch[val]);
                    }
                } else {
                    println!("    ⊥");
                }
            }

            // Print the hashcons
            println!("{}", hc);
            // Dot
            let mut file = std::fs::File::create(format!("dot/{}_hc.dot", func.name)).unwrap();
            hc.dot(&mut file, &phis).unwrap();

            // Print the phis
            println!("{}", phis);
        }
    }
}
