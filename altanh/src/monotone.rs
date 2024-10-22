use bril_rs::{EffectOps, Instruction, Literal, ValueOps};

use crate::cfg::{Block, Node, CFG};
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

    fn leq(&self, other: &Self) -> bool {
        // a <= b iff a ⊔ b = b
        let join = self.join(other);
        join == *other
    }
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

pub type AbstractStore<T> = HashMap<String, T>;

pub struct AnalysisResult<T> {
    pub value_in: HashMap<Node, T>,
    pub value_out: HashMap<Node, T>,
}

impl<T> AnalysisResult<T>
where
    T: Semilattice,
{
    pub fn new(
        bot: &T,
        flow_r: &HashMap<Node, HashSet<Node>>,
        value_out: HashMap<Node, T>,
    ) -> Self {
        let mut value_in = HashMap::new();
        // For each node, join the predecessors to get its in-value
        for node in value_out.keys() {
            let in_value = flow_r[node]
                .iter()
                .map(|pred| &value_out[pred])
                .fold(bot.clone(), |acc, x| acc.join(x));
            value_in.insert(*node, in_value);
        }
        AnalysisResult {
            value_in,
            value_out,
        }
    }
}

/// 1. Lattice
/// 2. Initial value for initial node (i.e. entry or exit)
/// 3. Monotone transfer function for each instruction

pub trait MonotoneAnalysis<T>
where
    T: Semilattice,
{
    fn direction(&self) -> Direction;
    fn initial_value(&self) -> T;
    fn transfer(&self, inst: &Instruction, loc: Node, value: &mut T);

    fn block_transfer(&self, block: &Block, loc: Node, value_in: &mut T) {
        match self.direction() {
            Direction::Forward => {
                for inst in &block.insts {
                    self.transfer(inst, loc, value_in);
                }
                if let Some(term) = &block.term {
                    self.transfer(term, loc, value_in);
                }
            }
            Direction::Backward => {
                if let Some(term) = &block.term {
                    self.transfer(term, loc, value_in);
                }
                for inst in block.insts.iter().rev() {
                    self.transfer(inst, loc, value_in);
                }
            }
        }
    }

    fn run(&self, cfg: &CFG) -> AnalysisResult<T>
    where
        T: Debug,
    {
        let (flow, flow_r, initial) = match self.direction() {
            Direction::Forward => (&cfg.flow, &cfg.flow_r, Node::Entry),
            Direction::Backward => (&cfg.flow_r, &cfg.flow, Node::Exit),
        };
        let mut values: HashMap<Node, T> = HashMap::new();
        for node in flow.keys() {
            values.insert(*node, self.initial_value().bot());
        }
        values.insert(initial, self.initial_value());

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
            if node == initial {
                continue;
            }
            let old = &values[&node];
            // Fold over predecessors
            let mut new = flow_r[&node]
                .iter()
                .map(|pred| &values[pred])
                .fold(self.initial_value().bot(), |acc, x| acc.join(&x));
            if let Node::Block(index) = node {
                self.block_transfer(&cfg.blocks[index], node, &mut new);
            }
            // eprintln!("node: {:?}, old: {:?}, new: {:?}", node, old, new);
            if !new.leq(old) {
                values.insert(node, new);
                for next in &flow[&node] {
                    worklist.push_back(*next);
                }
            }
        }

        AnalysisResult::new(&self.initial_value().bot(), flow_r, values)
    }

    /// Apply a function to each instruction in a block, in the order specified
    /// by the direction. The function is applied before the transfer function
    /// is executed.
    fn for_each_before<F>(&self, block: &Block, loc: Node, value_in: &mut T, mut f: F)
    where
        F: FnMut(&Instruction, &T),
    {
        match self.direction() {
            Direction::Forward => {
                for inst in &block.insts {
                    f(inst, value_in);
                    self.transfer(inst, loc, value_in);
                }
                if let Some(term) = &block.term {
                    f(term, value_in);
                    self.transfer(term, loc, value_in);
                }
            }
            Direction::Backward => {
                if let Some(term) = &block.term {
                    f(term, value_in);
                    self.transfer(term, loc, value_in);
                }
                for inst in block.insts.iter().rev() {
                    f(inst, value_in);
                    self.transfer(inst, loc, value_in);
                }
            }
        }
    }

    /// Apply a function to each instruction in a block, in the order specified
    /// by the direction. The function is applied after the transfer function is
    /// executed.
    fn for_each_after<F>(&self, block: &Block, loc: Node, value_in: &mut T, mut f: F)
    where
        F: FnMut(&Instruction, &T),
    {
        match self.direction() {
            Direction::Forward => {
                for inst in &block.insts {
                    self.transfer(inst, loc, value_in);
                    f(inst, value_in);
                }
                if let Some(term) = &block.term {
                    self.transfer(term, loc, value_in);
                    f(term, value_in);
                }
            }
            Direction::Backward => {
                if let Some(term) = &block.term {
                    self.transfer(term, loc, value_in);
                    f(term, value_in);
                }
                for inst in block.insts.iter().rev() {
                    self.transfer(inst, loc, value_in);
                    f(inst, value_in);
                }
            }
        }
    }
}

pub struct LiveVariables;

impl MonotoneAnalysis<HashSet<String>> for LiveVariables {
    fn direction(&self) -> Direction {
        Direction::Backward
    }

    fn initial_value(&self) -> HashSet<String> {
        HashSet::new()
    }

    fn transfer(&self, inst: &Instruction, _loc: Node, xs: &mut HashSet<String>) {
        use Instruction::*;
        match inst {
            Constant { dest, .. } => {
                xs.remove(dest);
            }
            Value { dest, args, .. } => {
                xs.remove(dest);
                xs.extend(args.iter().cloned());
            }
            Effect { args, .. } => {
                xs.extend(args.iter().cloned());
            }
        }
    }
}

pub fn live_variables(cfg: &CFG) -> AnalysisResult<HashSet<String>> {
    LiveVariables.run(cfg)
}

/// Observable variables.
/// A variable is observable after an instruction if it is used by some
/// effectful instruction after that instruction.
pub struct ObservableVariables;

impl MonotoneAnalysis<HashSet<String>> for ObservableVariables {
    fn direction(&self) -> Direction {
        Direction::Backward
    }

    fn initial_value(&self) -> HashSet<String> {
        HashSet::new()
    }

    fn transfer(&self, inst: &Instruction, _loc: Node, xs: &mut HashSet<String>) {
        use Instruction::*;
        match inst {
            Constant { dest, .. } => {
                xs.remove(dest);
            }
            // Calls may have side effects; for now, be conservative.
            Value {
                dest,
                op: ValueOps::Call,
                args,
                ..
            } => {
                xs.extend(args.iter().cloned());
                xs.remove(dest);
            }
            // Pure operations
            Value { dest, args, .. } => {
                if xs.contains(dest) {
                    xs.remove(dest);
                    xs.extend(args.iter().cloned());
                }
            }
            Effect { args, .. } => {
                xs.extend(args.iter().cloned());
            }
        }
    }
}

pub fn observable_variables(cfg: &CFG) -> AnalysisResult<HashSet<String>> {
    ObservableVariables.run(cfg)
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

// type ConditionalConstantLattice = (HashMap<String, ConstantLattice>,
// HashSet<Node>);
type ConditionalConstantLattice = (AbstractStore<ConstantLattice>, HashSet<Node>);

fn const_eval(env: &HashMap<String, ConstantLattice>, inst: &Instruction) -> ConstantLattice {
    use ConstantLattice::*;
    use Instruction::*;
    match inst {
        Constant { value, .. } => value.clone().into(),
        Value { op, args, .. } => {
            use ValueOps::*;
            let args: Vec<ConstantLattice> = args
                .iter()
                .map(|arg| env.get(arg).cloned().unwrap_or(ConstantLattice::Bot))
                .collect();
            if args.iter().any(|arg| arg == &Bot) {
                eprintln!("WARNING: undefined behavior detected at instruction: [{inst}]");
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

pub struct ConditionalConstant<'a> {
    pub cfg: &'a CFG,
}

impl<'a> MonotoneAnalysis<ConditionalConstantLattice> for ConditionalConstant<'a> {
    fn direction(&self) -> Direction {
        Direction::Forward
    }

    fn initial_value(&self) -> ConditionalConstantLattice {
        // Function parameters get top
        let initial_env = self
            .cfg
            .func_info
            .args
            .iter()
            .map(|arg| (arg.name.clone(), ConstantLattice::Top))
            .collect();
        let initial_reachable: HashSet<Node> =
            self.cfg.flow[&Node::Entry].iter().cloned().collect();
        (initial_env, initial_reachable)
    }

    fn block_transfer(&self, block: &Block, loc: Node, value_in: &mut ConditionalConstantLattice) {
        // Only process the block if it is reachable
        if value_in.1.contains(&loc) {
            for inst in &block.insts {
                self.transfer(inst, loc, value_in);
            }
            match &block.term {
                Some(term) => self.transfer(term, loc, value_in),
                None => {
                    // If no terminator, then all successors are reachable
                    for next in &self.cfg.flow[&loc] {
                        value_in.1.insert(*next);
                    }
                }
            }
        }
    }

    // TODO(altanh): separate transfer function for terminators?

    fn transfer(&self, inst: &Instruction, _loc: Node, value: &mut ConditionalConstantLattice) {
        let (env, reachable) = value;
        match inst {
            Instruction::Constant { dest, .. } | Instruction::Value { dest, .. } => {
                let c = const_eval(env, inst);
                env.insert(dest.clone(), c);
            }
            Instruction::Effect {
                op: EffectOps::Branch,
                labels,
                args,
                ..
            } => {
                // Look up the value of the condition; if it hasn't been defined, then we are in undefined behavior.
                let cond = env.get(&args[0]).cloned().unwrap_or(ConstantLattice::Bot);
                match cond {
                    ConstantLattice::Bool(true) => {
                        reachable.insert(self.cfg.resolve(&labels[0]));
                    }
                    ConstantLattice::Bool(false) => {
                        reachable.insert(self.cfg.resolve(&labels[1]));
                    }
                    ConstantLattice::Top => {
                        reachable.insert(self.cfg.resolve(&labels[0]));
                        reachable.insert(self.cfg.resolve(&labels[1]));
                    }
                    ConstantLattice::Bot => {
                        eprintln!("WARNING: undefined behavior detected at instruction: [{inst}]");
                        // Be conservative
                        reachable.insert(self.cfg.resolve(&labels[0]));
                        reachable.insert(self.cfg.resolve(&labels[1]));
                    }
                    _ => panic!("condition is not a boolean"),
                }
            }
            Instruction::Effect {
                op: EffectOps::Jump,
                labels,
                ..
            } => {
                reachable.insert(self.cfg.resolve(&labels[0]));
            }
            _ => (),
        }
    }
}
