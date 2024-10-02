use bril_rs::{Code, EffectOps, Function, Instruction, Literal, ValueOps};

use crate::cfg::{ControlFlowGraph, Node};
/// Monotone framework
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::Debug;
use std::hash::Hash;

pub enum Direction {
    Forward,
    Backward,
}

// Associate each CFG node with a lattice value, and monotone transfer function.

pub trait Semilattice
where
    Self: PartialEq + Sized + Clone,
{
    fn join(&self, other: &Self) -> Self;
    fn bot(&self) -> Self;
    // fn top(&self) -> Self;

    fn leq(&self, other: &Self) -> bool {
        // a <= b iff a ⊔ b = b
        let join = self.join(other);
        join == *other
    }
}

#[derive(Clone)]
struct IntersectionSemilattice<'a, T> {
    universe: &'a HashSet<T>,
    set: HashSet<T>,
}

impl<T> Semilattice for HashSet<T>
where
    T: Eq + Hash + Clone,
{
    fn join(&self, other: &Self) -> Self {
        self.union(other).cloned().collect()
    }

    fn bot(&self) -> Self {
        HashSet::new()
    }

    fn leq(&self, other: &Self) -> bool {
        // assert!(self.universe == other.universe);
        // self.set.is_subset(&other.set)
        self.is_subset(other)
    }
}

impl<'a, T> PartialEq for IntersectionSemilattice<'a, T>
where
    T: Eq + Hash,
{
    fn eq(&self, other: &Self) -> bool {
        self.set == other.set
    }
}

impl<'a, T> Semilattice for IntersectionSemilattice<'a, T>
where
    T: Eq + Hash + Clone,
{
    fn bot(&self) -> Self {
        Self {
            universe: self.universe,
            set: self.universe.clone(),
        }
    }
    fn join(&self, other: &Self) -> Self {
        Self {
            universe: self.universe,
            set: self.set.intersection(&other.set).cloned().collect(),
        }
    }
    fn leq(&self, other: &Self) -> bool {
        self.set.is_superset(&other.set)
    }
}

impl<S, T> Semilattice for (S, T)
where
    S: Semilattice,
    T: Semilattice,
{
    fn bot(&self) -> Self {
        (self.0.bot(), self.1.bot())
    }

    fn join(&self, other: &Self) -> Self {
        (self.0.join(&other.0), self.1.join(&other.1))
    }

    fn leq(&self, other: &Self) -> bool {
        self.0.leq(&other.0) && self.1.leq(&other.1)
    }
}

/// Missing keys are treated as bottom.
impl<K, V> Semilattice for HashMap<K, V>
where
    K: Clone + Eq + Hash,
    V: Semilattice,
{
    fn bot(&self) -> Self {
        HashMap::new()
    }

    fn join(&self, other: &Self) -> Self {
        let mut result = self.clone();
        for (k, v) in other.iter() {
            result
                .entry(k.clone())
                .and_modify(|v2| *v2 = v2.join(v))
                .or_insert_with(|| v.clone());
        }
        result
    }

    fn leq(&self, other: &Self) -> bool {
        self.iter()
            .all(|(k, v)| other.get(k).map_or(false, |v2| v.leq(v2)))
    }
}

/// 1. Lattice
/// 2. Initial value for initial node (i.e. entry or exit)
/// 3. Monotone transfer function for each node
pub struct MonotoneFramework<T, F> {
    pub direction: Direction,
    pub initial_value: T,
    pub transfer: F,
}

impl<T, F> MonotoneFramework<T, F>
where
    T: Semilattice + Debug,
    F: Fn(Node, &T) -> T,
{
    pub fn run(&self, cfg: &ControlFlowGraph) -> HashMap<Node, T> {
        let (flow, flow_r, initial) = match self.direction {
            Direction::Forward => (&cfg.flow, &cfg.flow_r, Node::Entry),
            Direction::Backward => (&cfg.flow_r, &cfg.flow, Node::Exit),
        };
        let mut values: HashMap<Node, T> = HashMap::new();
        for node in flow.keys() {
            values.insert(*node, self.initial_value.bot());
        }
        values.insert(initial, self.initial_value.clone());

        // Initialize worklist with preorder traversal
        let mut worklist: VecDeque<Node> = VecDeque::new();
        {
            let mut visited: HashSet<Node> = HashSet::new();
            let mut queue: VecDeque<Node> = VecDeque::new();
            queue.push_back(initial);
            while let Some(node) = queue.pop_front() {
                if visited.contains(&node) {
                    continue;
                }
                visited.insert(node);
                worklist.push_back(node);
                for next in &flow[&node] {
                    queue.push_back(*next);
                }
            }
        }

        // Iterate until convergence (pull-based)
        while let Some(node) = worklist.pop_front() {
            let old = &values[&node];
            // Fold over predecessors
            let joined = flow_r[&node]
                .iter()
                .map(|pred| &values[pred])
                .fold(self.initial_value.bot(), |acc, x| acc.join(&x));
            let new = (self.transfer)(node, &joined);
            // match node {
            //     Node::Inst(j) => eprintln!("-- {}", &cfg.func.instrs[j]),
            //     _ => eprintln!("-- {node:?}"),
            // }
            // eprintln!("  old: {old:?}");
            // eprintln!("  new: {new:?}");
            if !new.leq(old) {
                values.insert(node, new);
                for next in &flow[&node] {
                    worklist.push_back(*next);
                }
            }
        }
        values
    }
}

// pub fn live_variables(func: &Function) -> HashMap<Node, HashSet<String>> {
//     type L = HashSet<String>;
//     let direction = Direction::Backward;
//     let initial_value: L = HashSet::new();
//     // TODO: optimize using bitvectors
//     let transfer = |x: Node, l: &L| -> L {
//         match x {
//             Node::Entry => l.clone(),
//             Node::Exit => l.bot(),
//             Node::Inst(offset) => {
//                 use Instruction::*;
//                 if let Code::Instruction(inst) = &func.instrs[offset] {
//                     match inst {
//                         Constant { dest, .. } => {
//                             let mut l = l.clone();
//                             l.remove(dest);
//                             l
//                         }
//                         Value { dest, args, .. } => {
//                             let mut l = l.clone();
//                             l.remove(dest);
//                             let gen: HashSet<String> = args.iter().cloned().collect();
//                             l.union(&gen).cloned().collect()
//                         }
//                         Effect { args, .. } => {
//                             let gen: HashSet<String> = args.iter().cloned().collect();
//                             l.union(&gen).cloned().collect()
//                         }
//                     }
//                 } else {
//                     unreachable!();
//                 }
//             }
//         }
//     };
//     let analysis = MonotoneFramework {
//         direction,
//         initial_value,
//         transfer,
//     };
//     let cfg = ControlFlowGraph::new(func);
//     analysis.run(&cfg)
// }

/// Observable variables.
/// A variable is observable after an instruction if it is used by some
/// effectful instruction after that instruction.
pub fn observable_variables(func: &Function) -> HashMap<Node, HashSet<String>> {
    type L = HashSet<String>;
    let direction = Direction::Backward;
    let initial_value: L = HashSet::new();
    let transfer = |x: Node, l: &L| -> L {
        match x {
            Node::Entry => l.bot(),
            Node::Exit => l.bot(),
            Node::Inst(offset) => {
                use Instruction::*;
                if let Code::Instruction(inst) = &func.instrs[offset] {
                    match inst {
                        Constant { dest, .. } => {
                            let mut l = l.clone();
                            l.remove(dest);
                            l
                        }
                        Value { dest, args, .. } => {
                            // if dest is in l, then all args are observable
                            let mut l = l.clone();
                            if l.contains(dest) {
                                l.remove(dest);
                                let gen: HashSet<String> = args.iter().cloned().collect();
                                l.union(&gen).cloned().collect()
                            } else {
                                l
                            }
                        }
                        Effect { args, .. } => {
                            let gen = args.iter().cloned().collect();
                            l.union(&gen).cloned().collect()
                        }
                    }
                } else {
                    unreachable!();
                }
            }
        }
    };
    let analysis = MonotoneFramework {
        direction,
        initial_value,
        transfer,
    };
    let cfg = ControlFlowGraph::new(func);
    analysis.run(&cfg)
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ConstantLattice {
    Bot,
    Top,
    Int(i64),
    Bool(bool),
}

impl Semilattice for ConstantLattice {
    fn join(&self, other: &Self) -> Self {
        use ConstantLattice::*;
        match (self, other) {
            (Bot, _) => *other,
            (_, Bot) => *self,
            (Top, _) => Top,
            (_, Top) => Top,
            (Int(x), Int(y)) => {
                if x == y {
                    Int(*x)
                } else {
                    Top
                }
            }
            (Bool(x), Bool(y)) => {
                if x == y {
                    Bool(*x)
                } else {
                    Top
                }
            }
            _ => unreachable!("trying to join incompatible constant types, this is a type error"),
        }
    }

    fn bot(&self) -> Self {
        ConstantLattice::Bot
    }

    fn leq(&self, other: &Self) -> bool {
        use ConstantLattice::*;
        match (self, other) {
            (Bot, _) => true,
            (_, Top) => true,
            (Int(x), Int(y)) => x == y,
            (Bool(x), Bool(y)) => x == y,
            _ => false,
        }
    }
}

#[allow(unreachable_patterns)]
impl From<Literal> for ConstantLattice {
    fn from(lit: Literal) -> Self {
        use ConstantLattice::*;
        match lit {
            Literal::Int(x) => Int(x),
            Literal::Bool(x) => Bool(x),
            _ => unimplemented!(),
        }
    }
}

type ConditionalConstantLattice = (HashMap<String, ConstantLattice>, HashSet<Node>);

fn const_eval(env: &HashMap<String, ConstantLattice>, inst: &Instruction) -> ConstantLattice {
    use ConstantLattice::*;
    use Instruction::*;
    match inst {
        Constant { value, .. } => value.clone().into(),
        Value { op, args, .. } => {
            use ValueOps::*;
            let args: Vec<ConstantLattice> = args.iter().map(|arg| env[arg]).collect();
            // check that no arguments are bot
            if args.iter().any(|arg| arg == &Bot) {
                panic!("undefined value in instruction {}", inst);
            }
            match op {
                Add => match (&args[0], &args[1]) {
                    (Int(x), Int(y)) => Int(x + y),
                    _ => Top,
                },
                Sub => match (&args[0], &args[1]) {
                    (Int(x), Int(y)) => Int(x - y),
                    _ => Top,
                },
                Mul => match (&args[0], &args[1]) {
                    (Int(x), Int(y)) => Int(x * y),
                    _ => Top,
                },
                Div => match (&args[0], &args[1]) {
                    (Int(x), Int(y)) => Int(x / y),
                    _ => Top,
                },
                Eq => match (&args[0], &args[1]) {
                    (Int(x), Int(y)) => Bool(x == y),
                    _ => Top,
                },
                Lt => match (&args[0], &args[1]) {
                    (Int(x), Int(y)) => Bool(x < y),
                    _ => Top,
                },
                Gt => match (&args[0], &args[1]) {
                    (Int(x), Int(y)) => Bool(x > y),
                    _ => Top,
                },
                Le => match (&args[0], &args[1]) {
                    (Int(x), Int(y)) => Bool(x <= y),
                    _ => Top,
                },
                Ge => match (&args[0], &args[1]) {
                    (Int(x), Int(y)) => Bool(x >= y),
                    _ => Top,
                },
                Not => match &args[0] {
                    Bool(x) => Bool(!x),
                    _ => Top,
                },
                And => match (&args[0], &args[1]) {
                    (Bool(false), _) | (_, Bool(false)) => Bool(false),
                    (Bool(true), Bool(true)) => Bool(true),
                    _ => Top,
                },
                Or => match (&args[0], &args[1]) {
                    (Bool(true), _) | (_, Bool(true)) => Bool(true),
                    (Bool(false), Bool(false)) => Bool(false),
                    _ => Top,
                },
                Call => Top,
                Id => args[0].clone(),
            }
        }
        _ => unreachable!("not an expression"),
    }
}

pub fn conditional_constant(func: &Function) -> HashMap<Node, ConditionalConstantLattice> {
    let cfg = ControlFlowGraph::new(func);
    let direction = Direction::Forward;
    let initial_value = {
        let mut initial_env: HashMap<String, ConstantLattice> = HashMap::new();
        // Function arguments get top
        for arg in &func.args {
            initial_env.insert(arg.name.clone(), ConstantLattice::Top);
        }
        let initial_reachable: HashSet<Node> = cfg.flow[&Node::Entry].iter().cloned().collect();
        (initial_env, initial_reachable)
    };
    let transfer = |x: Node, l: &ConditionalConstantLattice| -> ConditionalConstantLattice {
        let (env, reachable) = l;
        if reachable.contains(&x) {
            match x {
                Node::Entry => l.clone(),
                Node::Exit => l.bot(),
                Node::Inst(offset) => {
                    use Instruction::*;
                    if let Code::Instruction(inst) = &func.instrs[offset] {
                        match inst {
                            Constant { dest, .. } | Value { dest, .. } => {
                                let c = const_eval(env, inst);
                                let mut next_env = env.clone();
                                next_env.insert(dest.clone(), c);
                                let mut r = reachable.clone();
                                // insert successor
                                for next in &cfg.flow[&x] {
                                    r.insert(*next);
                                }
                                (next_env, r)
                            }
                            Effect {
                                op: EffectOps::Jump,
                                labels,
                                ..
                            } => {
                                let mut r = reachable.clone();
                                for label in labels {
                                    r.insert(cfg.resolve(label));
                                }
                                (env.clone(), r)
                            }
                            Effect {
                                op: EffectOps::Branch,
                                labels,
                                args,
                                ..
                            } => {
                                // Look up the value of the condition; if it
                                // hasn't been defined, then we are in undefined behavior.
                                let cond =
                                    env.get(&args[0]).cloned().unwrap_or(ConstantLattice::Bot);
                                let mut r = reachable.clone();
                                match cond {
                                    ConstantLattice::Bool(true) => {
                                        r.insert(cfg.resolve(&labels[0]));
                                    }
                                    ConstantLattice::Bool(false) => {
                                        r.insert(cfg.resolve(&labels[1]));
                                    }
                                    ConstantLattice::Top => {
                                        r.insert(cfg.resolve(&labels[0]));
                                        r.insert(cfg.resolve(&labels[1]));
                                    }
                                    ConstantLattice::Bot => (),
                                    _ => panic!("condition is not a boolean"),
                                }
                                (env.clone(), r)
                            }
                            _ => {
                                let mut r = reachable.clone();
                                for next in &cfg.flow[&x] {
                                    r.insert(*next);
                                }
                                (env.clone(), r)
                            }
                        }
                    } else {
                        unreachable!();
                    }
                }
            }
        } else {
            l.clone()
        }
    };
    let analysis = MonotoneFramework {
        direction,
        initial_value,
        transfer,
    };
    analysis.run(&cfg)
}
