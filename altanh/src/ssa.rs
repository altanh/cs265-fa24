use std::{
    collections::{BTreeSet, HashMap, HashSet},
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
pub struct HashCons(HashMap<SymExpr, ValueNumber>);

impl HashCons {
    /// Warning: this will always return a new value number!
    pub fn symbolic_var(&mut self, loc: Location) -> ValueNumber {
        let n = self.0.len();
        self.0.insert(SymExpr::Var((n, loc)), n);
        n
    }

    pub fn intern(&mut self, se: SymExpr) -> ValueNumber {
        if let Some(n) = self.0.get(&se) {
            *n
        } else {
            let n = self.0.len();
            self.0.insert(se, n);
            n
        }
    }

    pub fn transpose(&self) -> HashMap<ValueNumber, SymExpr> {
        self.0.iter().map(|(k, v)| (*v, k.clone())).collect()
    }

    pub fn dot<F>(&self, f: &mut F, g: &GlobalPhi) -> io::Result<()>
    where
        F: io::Write,
    {
        writeln!(f, "digraph {{")?;
        for (se, n) in &self.0 {
            writeln!(f, "  {} [label=\"{:?}\"];", n, se)?;
        }
        for (_, phi) in &g.phis {
            for (vars, val) in phi {
                for v in vars {
                    writeln!(f, "  {} -> {};", val, v)?;
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

// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
// pub enum Lifted<T> {
//     Value(T),
//     Bot,
// }

type Lifted<T> = Option<T>;

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
                            let target: Node = label_map.get(target).cloned().unwrap().into();
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
            let label = label.replace("\n", "\\n");
            writeln!(f, "  {} [label=\"{}\"];", node_id(*node), label)?;
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

type Phi = HashMap<Vec<ValueNumber>, ValueNumber>;
// type GlobalPhi = HashMap<Node, Phi>;

#[derive(Debug, Default)]
struct GlobalPhi {
    pub phis: HashMap<Node, Phi>,
    vars: HashMap<(Node, Var), ValueNumber>,
}

impl Display for GlobalPhi {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (node, phi) in &self.phis {
            writeln!(f, "{:?}:", node)?;
            for (vars, val) in phi {
                writeln!(f, "    {:?} -> {}", vars, val)?;
            }
        }
        for ((node, var), val) in &self.vars {
            let n = match node {
                Node::Block(n) => n,
                _ => unreachable!(),
            };
            writeln!(f, "({}, {}): {}", n, var, val)?;
        }
        Ok(())
    }
}

impl GlobalPhi {
    fn entry(&mut self, node: Node) -> &mut Phi {
        self.phis.entry(node).or_insert(Default::default())
    }

    fn phi(&mut self, v: Vec<ValueNumber>, node: Node, var: Var, hc: &mut HashCons) -> ValueNumber {
        if let Some(&val) = self.entry(node).get(&v) {
            // Insert the variable
            self.vars.insert((node, var), val);
            val
        } else if let Some(&val) = self.vars.get(&(node, var.clone())) {
            // Remove all entries in self.phis[node] that have val as the value
            let mut to_remove: Vec<Vec<ValueNumber>> = vec![];
            for (vars, v) in self.entry(node) {
                if *v == val {
                    to_remove.push(vars.clone());
                }
            }
            for vars in to_remove {
                self.entry(node).remove(&vars);
            }
            // Update the entry
            self.entry(node).insert(v, val);
            val
        } else {
            let val = hc.symbolic_var(node);
            self.vars.insert((node, var), val);
            self.entry(node).insert(v, val);
            val
        }
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
    stores: Vec<(Node, &Lifted<AStore>)>,
    at: Location,
    g: &mut GlobalPhi,
    hc: &mut HashCons,
) -> Lifted<AStore> {
    // Filter out non-bot stores
    let mut stores: Vec<(Node, &AStore)> = stores
        .iter()
        .filter_map(|a| {
            if let (n, Lifted::Some(a)) = a {
                Some((*n, a))
            } else {
                None
            }
        })
        .collect();
    if stores.is_empty() {
        Lifted::None
    } else {
        // Merge the stores key-wise; keep merged value numbers in sorted order
        stores.sort_by(|a, b| a.0.cmp(&b.0));
        let mut stores: Vec<&AStore> = stores.into_iter().map(|(_, a)| a).collect();
        let mut result: HashMap<String, Vec<ValueNumber>> = stores
            .pop()
            .unwrap()
            .into_iter()
            .map(|(k, v)| (k.clone(), vec![*v]))
            .collect();
        for s in stores {
            for (x, e) in s {
                match result.get_mut(x) {
                    None => {
                        result.insert(x.clone(), vec![*e]);
                    }
                    Some(v) => {
                        v.push(*e);
                    }
                }
            }
        }
        // Insert phi variables
        Lifted::Some(
            result
                .into_iter()
                .map(|(k, v)| {
                    // Remove duplicates but keep the order
                    let mut seen: HashSet<ValueNumber> = HashSet::new();
                    let v: Vec<ValueNumber> = v
                        .into_iter()
                        .filter(|x| seen.insert(*x) && *x > 0)
                        .collect();
                    if v.is_empty() {
                        (k, hc.intern(SymExpr::Bot))
                    } else if v.len() == 1 {
                        (k, v.into_iter().next().unwrap())
                    } else {
                        // let v = phi
                        //     .entry(v.into_iter().collect())
                        //     // .or_insert(hc.symbolic_var(at));
                        let var = g.phi(v.clone(), at, k.clone(), hc);
                        println!("phi({:?}, {:?}, {:?}) = {:?}", v, at, k, var);
                        (k, var)
                    }
                })
                .collect(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::collect_vars;
    use std::collections::HashMap;

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

            let mut abs: HashMap<Node, Lifted<AStore>> = HashMap::new();
            for node in cfg.flow.keys() {
                abs.insert(*node, Lifted::None);
            }
            abs.insert(Node::Entry, Lifted::Some(initial));

            // Initialize worklist with preorder traversal of the CFG
            // let mut stack: Vec<Node> = vec![Node::Entry];
            // let mut visited: HashSet<Node> = HashSet::new();
            // let mut worklist: Vec<Node> = vec![];
            // while let Some(node) = stack.pop() {
            //     if visited.contains(&node) {
            //         continue;
            //     }
            //     visited.insert(node);
            //     worklist.push(node);
            //     if let Some(succs) = cfg.flow.get(&node) {
            //         for succ in succs {
            //             stack.push(*succ);
            //         }
            //     }
            // }
            let mut worklist: Vec<Node> = cfg.flow.keys().cloned().collect();

            let mut iter = 0;
            while let Some(n) = worklist.pop() {
                println!("iter {iter} at {n:?}: ");
                if let Node::Block(i) = n {
                    // assert!(cfg.flow_r[&n].len() <= 1);
                    // let mut astore = abs[&n].clone();
                    let ps: Vec<(Node, &Lifted<AStore>)> =
                        cfg.flow_r[&n].iter().map(|m| (*m, &abs[m])).collect();
                    let astore = join(ps, n, &mut phis, &mut hc);
                    // let astore = abs[cfg.flow_r[&n].iter().next().unwrap()].clone();
                    if let Lifted::Some(mut astore) = astore {
                        // Symbolically execute the block
                        for inst in &cfg.blocks[i].insts {
                            step_symbolic(inst, &mut astore, &mut hc);
                        }
                        // If something changed, push successors
                        let astore = Lifted::Some(astore);
                        if astore != abs[&n] {
                            // Print the diff
                            println!("update at {:?}", n);
                            if let Lifted::Some(astore) = &astore {
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
                                worklist.push(*succ);
                            }
                        }
                    } else {
                        continue;
                    }
                } else {
                    // Always push successors for entry and exit nodes
                    for succ in &cfg.flow[&n] {
                        worklist.push(*succ);
                    }
                }
                iter += 1;
                // if iter > 15 {
                //     break;
                // }
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
                if let Lifted::Some(store) = store {
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
