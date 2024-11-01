use std::{
    collections::{HashMap, HashSet},
    fmt::{Debug, Display},
    hash::Hash,
    io,
};

use crate::{
    cfg::{dominates, BlockBuilder, Fallthrough},
    util::{complete_adj, is_commutative, is_effectful, op_type, scc, topological_order},
};
use crate::{
    cfg::{Block, Guard, Node, CFG},
    util::op_arity,
};
use bril_rs::{
    Argument, Code, ConstOps, EffectOps, Function, Instruction, Literal, Type, ValueOps,
};

// TODO(altanh): intern
type Var = String;
type Location = Node;
type InstructionLocation = (Node, usize);
type ValueNumber = usize;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SymExpr {
    Const(Literal),
    Param(Argument),
    // Phi(xs, l, t) := {x | x ∈ xs} @ l : t
    Phi(Vec<String>, Location),
    Effect(InstructionLocation),
    Op(ValueOps, Vec<ValueNumber>),
    Bot,
}

#[derive(Debug)]
pub struct HashCons {
    e2v: HashMap<SymExpr, ValueNumber>,
    v2e: HashMap<ValueNumber, SymExpr>,
    v2t: HashMap<ValueNumber, Type>,
}

impl Default for HashCons {
    fn default() -> Self {
        let mut hc = HashCons {
            e2v: Default::default(),
            v2e: Default::default(),
            v2t: Default::default(),
        };
        hc.intern(SymExpr::Bot, None);
        hc
    }
}

impl HashCons {
    pub fn param(&mut self, var: Argument) -> ValueNumber {
        let ty = var.arg_type.clone();
        self.intern(SymExpr::Param(var), Some(ty))
    }

    pub fn phi(&mut self, xs: Vec<String>, loc: Location, ty: Type) -> ValueNumber {
        self.intern(SymExpr::Phi(xs, loc), Some(ty))
    }

    pub fn effect(&mut self, loc: InstructionLocation, ty: Option<Type>) -> ValueNumber {
        self.intern(SymExpr::Effect(loc), ty)
    }

    pub fn constant(&mut self, lit: Literal) -> ValueNumber {
        let ty = lit.get_type();
        self.intern(SymExpr::Const(lit), Some(ty))
    }

    pub fn bot(&self) -> ValueNumber {
        self.e2v[&SymExpr::Bot]
    }

    // Sorts arguments to commutative operators such that constants come first,
    // otherwise ordered by value number.
    pub fn canonicalize(&mut self, se: &SymExpr) -> Option<SymExpr> {
        match se {
            SymExpr::Op(op, args) if is_commutative(op) => {
                let mut args: Vec<(usize, usize)> = args
                    .iter()
                    .map(|v| match &self.v2e[&v] {
                        SymExpr::Const(_) => (0, *v),
                        _ => (1, *v),
                    })
                    .collect();
                args.sort();
                Some(SymExpr::Op(
                    op.clone(),
                    args.into_iter().map(|(_, v)| v).collect(),
                ))
            }
            _ => None,
        }
    }

    pub fn fold(&mut self, se: &SymExpr) -> Option<ValueNumber> {
        use ValueOps::*;
        match se {
            SymExpr::Op(op, args) => {
                let op_type = op_type(op)?;
                let op_arity = op_arity(op)?;
                match (op_type, op_arity) {
                    (Type::Int, _) => {
                        let x = &self.v2e[&args[0]];
                        let y = &self.v2e[&args[1]];
                        match (x, y) {
                            (SymExpr::Const(Literal::Int(x)), SymExpr::Const(Literal::Int(y))) => {
                                let r = match op {
                                    Add => x + y,
                                    Sub => x - y,
                                    Mul => x * y,
                                    Div => x / y,
                                    _ => unreachable!(),
                                };
                                Some(self.constant(Literal::Int(r)))
                            }
                            // x - x => 0
                            _ if args[0] == args[1] && *op == Sub => {
                                Some(self.constant(Literal::Int(0)))
                            }
                            // 0 + x => 0
                            (SymExpr::Const(Literal::Int(0)), _) if *op == Add => Some(args[1]),
                            // 0 * x => 0
                            (SymExpr::Const(Literal::Int(0)), _) if *op == Mul => {
                                Some(self.constant(Literal::Int(0)))
                            }
                            // 1 * x => x
                            (SymExpr::Const(Literal::Int(1)), _) if *op == Mul => Some(args[1]),
                            _ => None,
                        }
                    }
                    (Type::Bool, 2) => {
                        let x = &self.v2e[&args[0]];
                        let y = &self.v2e[&args[1]];
                        match (x, y) {
                            (
                                SymExpr::Const(Literal::Bool(x)),
                                SymExpr::Const(Literal::Bool(y)),
                            ) => {
                                let r = match op {
                                    And => *x && *y,
                                    Or => *x || *y,
                                    _ => unreachable!(),
                                };
                                Some(self.constant(Literal::Bool(r)))
                            }
                            (SymExpr::Const(Literal::Int(x)), SymExpr::Const(Literal::Int(y))) => {
                                let r = match op {
                                    Le => x <= y,
                                    Lt => x < y,
                                    Ge => x >= y,
                                    Gt => x > y,
                                    Eq => x == y,
                                    _ => unreachable!(),
                                };
                                Some(self.constant(Literal::Bool(r)))
                            }
                            (SymExpr::Const(Literal::Bool(false)), _) if *op == ValueOps::And => {
                                Some(self.constant(Literal::Bool(false)))
                            }
                            (SymExpr::Const(Literal::Bool(true)), _) if *op == ValueOps::Or => {
                                Some(self.constant(Literal::Bool(true)))
                            }
                            _ if args[0] == args[1] && *op == ValueOps::Eq => {
                                Some(self.constant(Literal::Bool(true)))
                            }
                            _ => None,
                        }
                    }
                    (Type::Bool, 1) => {
                        let x = &self.v2e[&args[0]];
                        match x {
                            SymExpr::Const(Literal::Bool(x)) => {
                                assert!(matches!(op, ValueOps::Not));
                                Some(self.constant(Literal::Bool(!x)))
                            }
                            _ => None,
                        }
                    }
                    _ => unreachable!(),
                }
            }
            _ => None,
        }
    }

    pub fn intern(&mut self, se: SymExpr, ty: Option<Type>) -> ValueNumber {
        if let Some(n) = self.e2v.get(&se) {
            *n
        } else {
            let sec = self.canonicalize(&se);
            let sec = if let Some(sec) = &sec { sec } else { &se };
            if let Some(v) = self.fold(sec) {
                self.e2v.insert(se, v);
                // Don't update the v2e mapping; keep the folded symbolic
                // expression as the canonical representative
                return v;
            }
            let n = self.v2e.len();
            self.e2v.insert(se.clone(), n);
            self.v2e.insert(n, se);
            if let Some(ty) = ty {
                self.v2t.insert(n, ty);
            }
            n
        }
    }

    pub fn lookup(&self, se: &SymExpr) -> Option<ValueNumber> {
        self.e2v.get(se).cloned()
    }

    pub fn rev_lookup(&self, v: &ValueNumber) -> Option<&SymExpr> {
        self.v2e.get(&v)
    }

    pub fn dot<F>(&self, f: &mut F, g: &GlobalValueGraph) -> io::Result<()>
    where
        F: io::Write,
    {
        writeln!(f, "digraph {{")?;
        for (se, n) in &self.e2v {
            let s = match se {
                SymExpr::Const(lit) => format!("{:?}", lit),
                // SymExpr::Var((n, loc)) => format!("{}@{:?}", n, loc),
                SymExpr::Param(var) => format!("{var}"),
                SymExpr::Phi(xs, loc) => {
                    let xs = xs.join(",");
                    format!("ϕ{{{xs}}} @ {loc:?}")
                }
                SymExpr::Effect((n, i)) => format!("effect @{n:?}.{i}"),
                SymExpr::Op(op, _) => {
                    format!("{:?}", op)
                }
                SymExpr::Bot => "⊥".to_string(),
            };
            writeln!(f, "  {} [label=\"{}: {}\"];", n, n, s)?;
        }
        // Write phi edges
        for (phi, args) in &g.phis {
            for (i, v) in args.iter().enumerate() {
                writeln!(f, "  {} -> {} [label=\".{}\"];", v.1, phi, i)?;
            }
        }
        // Write dataflow edges
        for (se, n) in &self.e2v {
            let maybe_args = match se {
                SymExpr::Op(_, args) => Some(args),
                SymExpr::Effect(iloc) => Some(g.effects.get(iloc).unwrap()),
                _ => None,
            };
            if let Some(args) = maybe_args {
                for (i, arg) in args.iter().enumerate() {
                    writeln!(f, "  {arg} -> {n} [label=\".{i}\", style=dotted]")?;
                }
            }
        }
        writeln!(f, "}}")
    }
}

/// TODO(altanh): functional map
pub type AStore = HashMap<Var, ValueNumber>;

fn eval_symbolic(op: ValueOps, args: Vec<ValueNumber>, ty: Type, hc: &mut HashCons) -> ValueNumber {
    assert!(!is_effectful(&op));
    match op {
        ValueOps::Id => args[0],
        _ => hc.intern(SymExpr::Op(op, args), Some(ty)),
    }
}

fn step_symbolic(
    i: &Instruction,
    iloc: InstructionLocation,
    gvg: &mut GlobalValueGraph,
    ctx: &mut AStore,
    hc: &mut HashCons,
) {
    match i {
        Instruction::Constant { dest, value, .. } => {
            ctx.insert(dest.clone(), hc.constant(value.clone()));
        }
        // Effectful operations
        Instruction::Value {
            dest,
            op,
            args,
            op_type,
            ..
        } if is_effectful(op) => {
            let args: Vec<ValueNumber> = args
                .iter()
                .map(|x| ctx.get(x).cloned().unwrap_or_else(|| hc.bot()))
                .collect();
            let call = hc.effect(iloc, op_type.clone().into());
            gvg.effects.insert(iloc, args);
            ctx.insert(dest.clone(), call);
        }
        Instruction::Effect { args, .. } => {
            let args: Vec<ValueNumber> = args
                .iter()
                .map(|x| ctx.get(x).cloned().unwrap_or_else(|| hc.bot()))
                .collect();
            let _effect = hc.effect(iloc, None);
            gvg.effects.insert(iloc, args);
        }
        // Pure operations
        Instruction::Value {
            args,
            dest,
            op,
            op_type,
            ..
        } => {
            let args: Vec<ValueNumber> = args
                .iter()
                .map(|x| ctx.get(x).cloned().unwrap_or_else(|| hc.bot()))
                .collect();
            ctx.insert(
                dest.clone(),
                eval_symbolic(op.clone(), args, op_type.clone(), hc),
            );
        }
    }
}

type PhiArgs = Vec<(Node, ValueNumber)>;

#[derive(Debug, Default)]
pub struct GlobalValueGraph {
    pub phis: HashMap<ValueNumber, PhiArgs>,
    pub effects: HashMap<InstructionLocation, Vec<ValueNumber>>,
}

impl GlobalValueGraph {
    // TODO(altanh): this is broken as is - it causes nontermination of the
    // analysis when running `totient.bril`. I think we might need to globally
    // propagate the phi simplfication eclass-union style? Tricky.
    // -------------------------------------------------------------------------
    // See "Simple and Efficient Construction of Static Single Assignment
    // Form" by Braun et al. for details.
    // fn simplify_trivial(&self, phi: ValueNumber, args: &PhiArgs, hc: &mut HashCons) -> ValueNumber {
    //     // If there are 2 unique value numbers, one of which is phi, then
    //     // return the other one. If all arguments are phi, return bot. Otherwise
    //     // return phi.
    //     let mut vals: HashSet<ValueNumber> = args.iter().map(|(_, v)| *v).collect();
    //     if vals.len() == 2 && vals.contains(&phi) {
    //         vals.remove(&phi);
    //         let val = vals.into_iter().next().unwrap();
    //         val
    //     } else if vals.len() == 1 && vals.contains(&phi) {
    //         hc.bot()
    //     } else {
    //         phi
    //     }
    // }

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
        // Collect all variables with the same phi arguments
        let mut vars: HashMap<PhiArgs, Vec<String>> = HashMap::new();
        for (k, args) in store {
            vars.entry(args).or_insert_with(Vec::new).push(k);
        }
        // Create symbolic variables for each set of equal variables and update
        // phi entries
        let mut result: AStore = Default::default();
        for (args, mut vars) in vars {
            let val = match args.len() {
                0 => unreachable!(),
                1 => args[0].1,
                _ => {
                    vars.sort();
                    let val = hc.phi(vars.clone(), loc, hc.v2t[&args[0].1].clone());
                    self.phis.insert(val, args);
                    val
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
        let mut v2es: HashMap<ValueNumber, HashSet<&SymExpr>> = HashMap::new();
        for (k, v) in &self.e2v {
            v2es.entry(*v).or_default().insert(k);
        }
        // Print in order
        for i in 0..self.v2e.len() {
            if !v2es.contains_key(&i) {
                writeln!(f, "{i}: dead")?;
                continue;
            }
            writeln!(f, "{i}: {:?}", &v2es[&i])?;
        }
        Ok(())
    }
}

struct SSA {
    cfg: CFG,
    hc: HashCons,
    gvg: GlobalValueGraph,
    abs: HashMap<Node, Option<AStore>>,
}

impl SSA {
    fn is_reachable(&self, node: &Node) -> bool {
        self.abs[node].is_some()
    }
}

fn join(
    mut stores: Vec<(Node, &AStore)>,
    loc: Location,
    gvg: &mut GlobalValueGraph,
    hc: &mut HashCons,
) -> Option<AStore> {
    // Sort the stores by source node for consistency
    stores.sort_by_key(|(n, _)| *n);
    if stores.is_empty() {
        // No predecessors are reachable, so neither are we
        None
    } else {
        // Merge the stores: each variable is mapped to the list of value
        // numbers it takes on at the join point. We track the source node as
        // well to prevent incorrect phi function equalities.
        let mut result: HashMap<String, (PhiArgs, HashSet<ValueNumber>)> = HashMap::new();
        for (n, s) in stores {
            for (x, e) in s {
                // Skip undefined values.
                if *e == hc.bot() {
                    continue;
                }
                let entry = result
                    .entry(x.clone())
                    .or_insert_with(|| (vec![], HashSet::new()));
                entry.0.push((n, *e));
                entry.1.insert(*e);
            }
        }
        // Collapse fully duplicate entries
        let result: HashMap<String, PhiArgs> = result
            .into_iter()
            .map(|(k, (args, vals))| {
                if vals.len() == 1 {
                    (k, vec![args[0]])
                } else {
                    (k, args)
                }
            })
            .collect();
        Some(gvg.insert_phis(loc, result, hc))
    }
}

fn scope(se: &SymExpr, dom_tree: &HashMap<Node, Node>, hc: &HashCons) -> Node {
    fn dom_min(n: Node, m: Node, dom_tree: &HashMap<Node, Node>) -> Option<Node> {
        match (n, m) {
            (Node::Entry, m) => Some(m),
            (n, Node::Entry) => Some(n),
            (n, m) => {
                // Walk to root from n
                let mut f = n;
                while f != Node::Entry {
                    if f == m {
                        return Some(n);
                    }
                    f = dom_tree[&f];
                }
                // Walk to root from m
                f = m;
                while f != Node::Entry {
                    if f == n {
                        return Some(m);
                    }
                    f = dom_tree[&f];
                }
                // Neither node dominates the other
                None
            }
        }
    }

    match se {
        SymExpr::Bot => Node::Entry,
        SymExpr::Effect((l, _)) => *l,
        SymExpr::Const(_) => Node::Entry,
        SymExpr::Op(_, args) => {
            let mut arg_scopes: Vec<Node> = args
                .iter()
                .map(|v| {
                    let se = &hc.rev_lookup(v).unwrap();
                    scope(se, dom_tree, hc)
                })
                .collect();
            let mut min = arg_scopes.pop().unwrap();
            for s in arg_scopes {
                min = dom_min(min, s, dom_tree).unwrap();
            }
            min
        }
        SymExpr::Param(_) => Node::Entry,
        SymExpr::Phi(_, l) => *l,
    }
}

fn pond_of_nodes(
    node: Node,
    vs: &HashSet<ValueNumber>,
    cfg: &CFG,
    ssa: &SSA,
) -> HashMap<ValueNumber, HashSet<ValueNumber>> {
    let mut pond: HashMap<ValueNumber, HashSet<ValueNumber>> = Default::default();
    // Insert value dependency edges
    for &v in vs {
        pond.entry(v).or_default();
        match &ssa.hc.v2e[&v] {
            SymExpr::Effect(iloc) => {
                for u in &ssa.gvg.effects[iloc] {
                    if vs.contains(u) {
                        pond.entry(*u).or_default().insert(v);
                    }
                }
            }
            SymExpr::Op(_, args) => {
                for u in args {
                    if vs.contains(u) {
                        pond.entry(*u).or_default().insert(v);
                    }
                }
            }
            _ => (),
        }
    }
    if let Some(block) = cfg.get(node) {
        // Insert control dependency edges
        let mut maybe_last: Option<ValueNumber> = None;
        for (i, inst) in block.insts.iter().enumerate() {
            let maybe_this = match inst {
                // Instruction::Value {
                //     op: ValueOps::Call, ..
                // }
                // | Instruction::Effect { .. } => {
                //     let e = SymExpr::Effect((node, i));
                //     ssa.hc.lookup(&e)
                // }
                Instruction::Value { op, .. } if is_effectful(op) => {
                    let e = SymExpr::Effect((node, i));
                    ssa.hc.lookup(&e)
                }
                Instruction::Effect { .. } => {
                    let e = SymExpr::Effect((node, i));
                    ssa.hc.lookup(&e)
                }
                _ => None,
            };
            if let Some(this) = maybe_this {
                pond.entry(this).or_default();
                if let Some(last) = maybe_last {
                    pond.entry(last).or_default().insert(this);
                }
                maybe_last = Some(this);
            }
        }
    }
    pond
}

#[derive(Default)]
struct TCMemo {
    tc: HashMap<ValueNumber, HashSet<ValueNumber>>,
}

impl TCMemo {
    fn get(&mut self, v: ValueNumber, ssa: &SSA) -> &HashSet<ValueNumber> {
        if self.tc.contains_key(&v) {
            return &self.tc[&v];
        }
        let mut deps: HashSet<ValueNumber> = HashSet::new();
        match &ssa.hc.v2e[&v] {
            SymExpr::Op(_, args) => {
                for &arg in args {
                    let arg_deps = self.get(arg, ssa);
                    deps.insert(arg);
                    deps.extend(arg_deps);
                }
            }
            SymExpr::Effect(iloc) => {
                for &arg in &ssa.gvg.effects[iloc] {
                    let arg_deps = self.get(arg, ssa);
                    deps.insert(arg);
                    deps.extend(arg_deps);
                }
            }
            _ => (),
        };
        self.tc.insert(v, deps);
        &self.tc[&v]
    }
}

fn initialize_abs<F, A>(cfg: &CFG, init: F) -> HashMap<Node, A>
where
    F: Fn(Node) -> A,
{
    let mut abs: HashMap<Node, A> = HashMap::new();
    abs.insert(Node::Entry, init(Node::Entry));
    for i in 0..cfg.blocks.len() {
        let node = Node::Block(i);
        abs.insert(node, init(node));
    }
    abs.insert(Node::Exit, init(Node::Exit));
    abs
}

fn used_values(cfg: &CFG, ssa: &SSA) -> HashMap<Node, HashSet<ValueNumber>> {
    let mut tc: TCMemo = Default::default();
    // Collect the gen sets at each node
    let mut gen: HashMap<Node, HashSet<ValueNumber>> = HashMap::new();
    gen.insert(Node::Entry, HashSet::new());
    gen.insert(Node::Exit, HashSet::new());
    // All dependencies of effects in the block
    for &(node, i) in ssa.gvg.effects.keys() {
        let v = ssa.hc.e2v[&SymExpr::Effect((node, i))];
        let entry = gen.entry(node).or_default();
        entry.insert(v);
        entry.extend(tc.get(v, ssa));
    }
    // As well as dependencies of block terminators, if they are reachable
    for (i, block) in cfg.blocks.iter().enumerate() {
        let node = Node::Block(i);
        let entry = gen.entry(node).or_default();
        if !ssa.is_reachable(&node) {
            continue;
        }
        let node_abs = ssa.abs[&node].as_ref().unwrap();
        match &block.term {
            Instruction::Effect { args, .. } => {
                for &arg in args.iter().map(|x| node_abs.get(x).unwrap()) {
                    entry.insert(arg);
                    entry.extend(tc.get(arg, ssa));
                }
            }
            _ => unreachable!(),
        }
    }
    // Transitive closure of phi dependencies...
    let mut changed = true;
    while changed {
        changed = false;
        // All live phis also generate uses at their predecessors!
        let live_phis: HashSet<ValueNumber> = gen
            .values()
            .cloned()
            .flatten()
            .filter(|v| matches!(&ssa.hc.v2e[v], SymExpr::Phi(_, _)))
            .collect();
        for phi in live_phis {
            let SymExpr::Phi(_, loc) = &ssa.hc.v2e[&phi] else {
                unreachable!()
            };
            gen.entry(*loc).or_default().insert(phi);
            for &(pred, v) in &ssa.gvg.phis[&phi] {
                let entry = gen.entry(pred).or_default();
                changed |= entry.insert(v);
                entry.extend(tc.get(v, ssa));
            }
        }
    }
    gen
}

// v is available at p if all paths into p use v
fn available(
    used: &HashMap<Node, HashSet<ValueNumber>>,
    cfg: &CFG,
    ssa: &SSA,
) -> HashMap<Node, HashSet<ValueNumber>> {
    // abs[n] |-> None means all values are available at n
    let mut abs: HashMap<Node, Option<HashSet<ValueNumber>>> = initialize_abs(cfg, |n| match n {
        Node::Entry => Some(used[&Node::Entry].clone()),
        _ => None,
    });
    let join = |a: Option<HashSet<ValueNumber>>, b: &Option<HashSet<ValueNumber>>| match (a, b) {
        (None, b) => b.clone(),
        (a, None) => a,
        (Some(a), Some(b)) => Some(a.intersection(b).cloned().collect()),
    };
    let mut av: HashMap<Node, Option<HashSet<ValueNumber>>> = HashMap::new();
    av.insert(Node::Entry, Some(HashSet::new()));
    let mut worklist = cfg.postorder(true);
    while let Some(node) = worklist.pop_front() {
        if node == Node::Entry {
            continue;
        }
        let old = &abs[&node];
        let mut new = if cfg.flow_r[&node].is_empty() {
            // No predecessors, no incoming available values
            Some(HashSet::new())
        } else {
            let mut it = cfg.flow_r[&node].iter().map(|n| &abs[n]);
            let mut new = it.next().unwrap().clone();
            while let Some(s) = it.next() {
                new = join(new, s);
            }
            new
        };
        av.insert(node, new.clone());
        new = match new {
            None => None,
            Some(mut new) => {
                if let Some(u) = used.get(&node) {
                    new.extend(u);
                }
                Some(new)
            }
        };
        if new != *old {
            abs.insert(node, new);
            for &next in &cfg.flow_r[&node] {
                worklist.push_back(next);
            }
        }
    }
    // Replace the None placeholders with all expressions
    av.into_iter()
        .map(|(k, v)| match v {
            None => (k, ssa.hc.v2e.keys().cloned().collect()),
            Some(v) => (k, v),
        })
        .collect()
}

// v is very busy at p if all paths from p to exit use v
fn very_busy(
    used: &HashMap<Node, HashSet<ValueNumber>>,
    cfg: &CFG,
) -> HashMap<Node, HashSet<ValueNumber>> {
    let mut abs: HashMap<Node, HashSet<ValueNumber>> = initialize_abs(cfg, |_| HashSet::new());
    let mut vb: HashMap<Node, HashSet<ValueNumber>> = HashMap::new();
    let mut worklist = cfg.postorder(false);
    while let Some(node) = worklist.pop_front() {
        if node == Node::Exit {
            continue;
        }
        let old = &abs[&node];
        assert!(cfg.flow[&node].len() > 0);
        let mut it = cfg.flow[&node].iter().map(|n| &abs[n]);
        let mut new = it.next().unwrap().clone();
        while let Some(s) = it.next() {
            new = new.intersection(s).cloned().collect();
        }
        vb.insert(node, new.clone());
        new.extend(&used[&node]);
        if new != *old {
            abs.insert(node, new);
            for &next in &cfg.flow_r[&node] {
                worklist.push_back(next);
            }
        }
    }
    vb
}

#[derive(Default)]
struct ScopeMemo(HashMap<ValueNumber, Node>);
impl ScopeMemo {
    fn get(&mut self, v: ValueNumber, dom_tree: &HashMap<Node, Node>, hc: &HashCons) -> Node {
        if let Some(n) = self.0.get(&v) {
            *n
        } else {
            let n = scope(&hc.v2e[&v], dom_tree, hc);
            self.0.insert(v, n);
            n
        }
    }
}

fn earliest(
    av: &HashMap<Node, HashSet<ValueNumber>>,
    vb: &HashMap<Node, HashSet<ValueNumber>>,
    dom_tree: &HashMap<Node, Node>,
    hc: &HashCons,
    scopes: &mut ScopeMemo,
) -> HashMap<Node, HashSet<ValueNumber>> {
    let mut ea = HashMap::new();
    for (&node, v) in vb {
        if let Some(a) = av.get(&node) {
            // Filter out values that are out of scope (which should just be
            // phis and effects)
            let diff: HashSet<ValueNumber> = v
                .difference(a)
                .cloned()
                .filter(|v| {
                    let vn = scopes.get(*v, dom_tree, hc);
                    dominates(vn, node, dom_tree)
                })
                .collect();
            ea.insert(node, diff);
        } else {
            ea.insert(node, v.clone());
        }
    }
    ea
}

fn merge_sets<V>(
    a: &HashMap<Node, HashSet<V>>,
    b: &HashMap<Node, HashSet<V>>,
) -> HashMap<Node, HashSet<V>>
where
    V: Eq + Hash + Clone,
{
    let (larger, smaller) = if a.len() > b.len() { (a, b) } else { (b, a) };
    let mut result = larger.clone();
    for (k, v) in smaller {
        let entry = result.entry(*k).or_default();
        entry.extend(v.iter().cloned());
    }
    result
}

fn diff_sets<V>(
    a: &HashMap<Node, HashSet<V>>,
    b: &HashMap<Node, HashSet<V>>,
) -> HashMap<Node, HashSet<V>>
where
    V: Eq + Hash + Clone,
{
    let mut result = a.clone();
    for (k, v) in b {
        if let Some(u) = result.get_mut(k) {
            for v in v {
                u.remove(v);
            }
        } else {
            result.insert(*k, HashSet::new());
        }
    }
    result
}

#[allow(dead_code)]
fn print_map<V>(len: usize, map: &HashMap<Node, HashSet<V>>)
where
    V: Debug,
{
    if map.contains_key(&Node::Entry) {
        eprintln!("Entry: {:?}", &map[&Node::Entry]);
    } else {
        eprintln!("Entry: none");
    }
    for i in 0..len {
        eprintln!("Block {i}: {:?}", &map[&Node::Block(i)]);
    }
    if map.contains_key(&Node::Exit) {
        eprintln!("Exit: {:?}", &map[&Node::Exit]);
    } else {
        eprintln!("Exit: none");
    }
}

impl SSA {
    pub fn v2s(&self, v: &ValueNumber) -> String {
        match &self.hc.v2e[v] {
            SymExpr::Bot => "__undefined".to_string(),
            SymExpr::Phi(_, _) => format!("__phi{v}"),
            SymExpr::Param(p) => p.name.clone(),
            _ => format!("__v{v}"),
        }
    }
}

fn lower(ssa: &mut SSA, destruct_phis: bool) -> Vec<Block> {
    type Blocks = HashMap<Node, Block>;
    // eprintln!("{}", ssa.hc);
    fn lower_node(
        node: Node,
        ssa: &mut SSA,
        to_compute: &HashSet<ValueNumber>,
        destruct_phis: bool,
        blocks: &mut Blocks,
    ) {
        // Don't lower unreachable blocks
        if !ssa.is_reachable(&node) {
            eprintln!("{node:?} is dead, skipping lowering...");
            return;
        }
        let node_abs = ssa.abs[&node].as_ref().unwrap();
        let pond = pond_of_nodes(node, to_compute, &ssa.cfg, ssa);
        let order = topological_order(&pond);
        // Lower values in order
        let mut bb = BlockBuilder::new(ssa.cfg.get(node).map(|b| b.label.clone()));
        if !destruct_phis {
            // Emit phi instructions
            for phi in order.iter().filter(|v| ssa.gvg.phis.contains_key(v)) {
                let SymExpr::Phi(_, loc) = &ssa.hc.v2e[phi] else {
                    unreachable!()
                };
                if *loc != node {
                    continue;
                }
                let (labels, args): (Vec<String>, Vec<String>) = ssa.gvg.phis[phi]
                    .iter()
                    .map(|(n, v)| {
                        (
                            ssa.cfg.get(*n).map_or_else(
                                || blocks[&Node::Entry].label.clone(),
                                |b| b.label.clone(),
                            ),
                            ssa.v2s(v),
                        )
                    })
                    .unzip();
                bb.push(Instruction::Value {
                    args,
                    dest: ssa.v2s(phi),
                    funcs: vec![],
                    labels,
                    op: ValueOps::Phi,
                    op_type: ssa.hc.v2t[phi].clone(),
                });
            }
        }
        for v in order.into_iter().filter(|v| !ssa.gvg.phis.contains_key(v)) {
            let dest = ssa.v2s(&v);
            match &ssa.hc.v2e[&v] {
                SymExpr::Const(c) => {
                    bb.push(Instruction::Constant {
                        dest,
                        op: ConstOps::Const,
                        const_type: c.get_type(),
                        value: c.clone(),
                    });
                }
                SymExpr::Op(op, args) => {
                    let args: Vec<String> = args.iter().map(|v| ssa.v2s(v)).collect();
                    bb.push(Instruction::Value {
                        args: args,
                        dest,
                        funcs: vec![],
                        labels: vec![],
                        op: op.clone(),
                        op_type: ssa.hc.v2t[&v].clone(),
                    });
                }
                SymExpr::Effect(iloc) => {
                    let args: Vec<String> =
                        ssa.gvg.effects[iloc].iter().map(|v| ssa.v2s(v)).collect();
                    // Fetch original instruction
                    let orig = &ssa.cfg.get(iloc.0).unwrap().insts[iloc.1];
                    match orig {
                        Instruction::Value {
                            op, funcs, op_type, ..
                        } => {
                            bb.push(Instruction::Value {
                                op: op.clone(),
                                args,
                                dest,
                                funcs: funcs.clone(),
                                labels: vec![],
                                op_type: op_type.clone(),
                            });
                        }
                        Instruction::Effect { funcs, op, .. } => {
                            bb.push(Instruction::Effect {
                                args,
                                funcs: funcs.clone(),
                                labels: vec![],
                                op: op.clone(),
                            });
                        }
                        _ => unreachable!(),
                    }
                }
                SymExpr::Phi(_, _) => {
                    // We don't do anything here. Rather, once everything else
                    // is lowered, we go over all phi definitions and insert
                    // moves as needed (if destructing).
                    unreachable!()
                }
                SymExpr::Param(_) => {}
                SymExpr::Bot => (),
            }
        }
        match node {
            Node::Entry => {
                // Get unique target of entry
                let next = ssa.cfg.flow[&Node::Entry].iter().next().cloned().unwrap();
                let next_label = ssa.cfg.get(next).unwrap().label.clone();
                blocks.insert(
                    node,
                    bb.complete(None, Fallthrough::Next(next_label), &mut ssa.cfg.labels),
                );
            }
            Node::Block(_) => {
                let term = ssa.cfg.get(node).unwrap().term.clone();
                let term = match &term {
                    Instruction::Effect {
                        args,
                        labels,
                        op: EffectOps::Branch,
                        ..
                    } => {
                        // br true then else => jmp then
                        // br false then else => jmp else
                        let cond = node_abs[&args[0]];
                        match &ssa.hc.v2e[&cond] {
                            SymExpr::Const(Literal::Bool(true)) => Instruction::Effect {
                                args: vec![],
                                funcs: vec![],
                                labels: vec![labels[0].clone()],
                                op: EffectOps::Jump,
                            },
                            SymExpr::Const(Literal::Bool(false)) => Instruction::Effect {
                                args: vec![],
                                funcs: vec![],
                                labels: vec![labels[1].clone()],
                                op: EffectOps::Jump,
                            },
                            _ => Instruction::Effect {
                                args: vec![ssa.v2s(&cond)],
                                funcs: vec![],
                                labels: labels.clone(),
                                op: EffectOps::Branch,
                            },
                        }
                    }
                    Instruction::Effect {
                        args,
                        funcs,
                        labels,
                        op,
                    } => {
                        let args: Vec<String> = args
                            .iter()
                            .map(|x| node_abs[x])
                            .map(|v| ssa.v2s(&v))
                            .collect();
                        Instruction::Effect {
                            args,
                            funcs: funcs.clone(),
                            labels: labels.clone(),
                            op: op.clone(),
                        }
                    }
                    _ => unreachable!(),
                };
                bb.push(term);
                blocks.insert(
                    node,
                    bb.complete(None, Fallthrough::None, &mut ssa.cfg.labels),
                );
            }
            _ => (),
        }
    }

    let dom_tree = ssa.cfg.dom_tree();
    let mut scopes = ScopeMemo::default();

    let used = used_values(&ssa.cfg, ssa);
    let live = {
        let mut live: HashSet<ValueNumber> = HashSet::new();
        for s in used.values() {
            live.extend(s);
        }
        live
    };
    let vb = very_busy(&used, &ssa.cfg);
    let av = available(&used, &ssa.cfg, ssa);
    let pre = earliest(&av, &vb, &dom_tree, &ssa.hc, &mut scopes);
    let used_pre = merge_sets(&used, &pre);
    let av_pre = available(&used_pre, &ssa.cfg, ssa);
    let to_compute = diff_sets(&used_pre, &av_pre);

    // let len = ssa.cfg.blocks.len();
    // eprintln!("USED");
    // print_map(len, &used);
    // eprintln!("VB");
    // print_map(len, &vb);
    // eprintln!("AV");
    // print_map(len, &av);
    // eprintln!("PRE");
    // print_map(len, &pre);
    // eprintln!("USED PRE");
    // print_map(len, &used_pre);
    // eprintln!("AV PRE");
    // print_map(len, &av_pre);
    // eprintln!("TO COMPUTE");
    // print_map(len, &to_compute);

    let mut blocks: Blocks = Default::default();
    let mut res: Vec<Block> = vec![];

    // Lower all the blocks
    lower_node(
        Node::Entry,
        ssa,
        &to_compute[&Node::Entry],
        destruct_phis,
        &mut blocks,
    );
    for i in 0..ssa.cfg.blocks.len() {
        let node = Node::Block(i);
        lower_node(node, ssa, &to_compute[&node], destruct_phis, &mut blocks);
    }

    if destruct_phis {
        // phi_move[n][phi] = v means at n, we want a move `phi = id v`.
        let mut phi_moves: HashMap<Node, HashMap<ValueNumber, HashSet<ValueNumber>>> =
            HashMap::new();
        for (phi, phi_args) in &ssa.gvg.phis {
            if !live.contains(phi) {
                continue;
            }
            for &(pred, arg_val) in phi_args {
                phi_moves
                    .entry(pred)
                    .or_default()
                    .entry(*phi)
                    .or_default()
                    .insert(arg_val);
            }
        }

        // Lower the parallel phi moves
        for (node, phi_adj) in phi_moves.iter_mut() {
            complete_adj(phi_adj);
            let block = blocks.get_mut(node).unwrap();
            // Compute SCC DAG
            let (dag, sccs) = scc(phi_adj);
            // Linearize DAG
            let order = topological_order(&dag);
            // Process each component
            for root in order {
                if sccs[&root].len() == 1 {
                    if let Some(arg_val) = phi_adj[&root].iter().next() {
                        // No cycle; just emit the move
                        block.insts.push(Instruction::Value {
                            args: vec![ssa.v2s(arg_val)],
                            dest: format!("__phi{root}"),
                            funcs: vec![],
                            labels: vec![],
                            op: ValueOps::Id,
                            op_type: ssa.hc.v2t[&root].clone(),
                        });
                    }
                } else {
                    // NB: since every edge x -> y is a phi move x := y, and there
                    // are never two moves for the same phi, it follows that every
                    // node has a single successor. Thus, all SCCs in this graph are
                    // simple cycles and can be traversed by following the edges
                    // from the root node.

                    // Introduce a temporary to break the cycle
                    let temp = format!("__temp{root}");
                    block.insts.push(Instruction::Value {
                        args: vec![ssa.v2s(&root)],
                        dest: temp.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::Id,
                        op_type: ssa.hc.v2t[&root].clone(),
                    });
                    // Do the moves
                    let mut cur = root;
                    loop {
                        let arg_val = phi_adj[&cur].iter().next().unwrap();
                        block.insts.push(Instruction::Value {
                            args: vec![ssa.v2s(arg_val)],
                            dest: format!("__phi{cur}"),
                            funcs: vec![],
                            labels: vec![],
                            op: ValueOps::Id,
                            op_type: ssa.hc.v2t[&cur].clone(),
                        });
                        if *arg_val == root {
                            break;
                        }
                        cur = *arg_val;
                    }
                    // Tie the knot
                    block.insts.push(Instruction::Value {
                        args: vec![temp],
                        dest: format!("__phi{cur}"),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::Id,
                        op_type: ssa.hc.v2t[&cur].clone(),
                    });
                }
            }
        }
    }

    res.push(blocks.get(&Node::Entry).unwrap().clone());
    for i in 0..ssa.cfg.blocks.len() {
        let node = Node::Block(i);
        if ssa.abs[&node].is_none() {
            continue;
        }
        res.push(blocks.get(&node).unwrap().clone());
    }
    res
}

#[allow(dead_code)]
fn diff_abs(old: &Option<AStore>, new: &Option<AStore>) {
    if let Some(new) = new {
        for (k, v) in new {
            let o = if let Some(old) = old {
                old.get(k)
                    .cloned()
                    .map_or_else(|| "⊥".to_string(), |v| v.to_string())
            } else {
                "⊥".to_string()
            };
            eprintln!("{k}: {o} -> {v}");
        }
    }
}

pub fn gvn_gcm_cc_dce(func: &Function) -> Function {
    let cfg = CFG::new(func);
    let mut hc: HashCons = Default::default();
    let mut gvg: GlobalValueGraph = Default::default();

    // Initial abstract store: parameters are mapped to their symbolic
    // values, all other variables are (implicitly) mapped to ⊥.
    let mut initial: AStore = HashMap::new();
    for arg in &func.args {
        initial.insert(arg.name.clone(), hc.param(arg.clone()));
    }

    let mut abs: HashMap<Node, Option<AStore>> = HashMap::new();
    for node in cfg.flow.keys() {
        abs.insert(*node, None);
    }
    abs.insert(Node::Entry, Some(initial));

    // Initalize worklist with reverse postorder traversal of the CFG
    let mut worklist = cfg.postorder(true);
    while let Some(n) = worklist.pop_front() {
        if let Node::Block(i) = n {
            let ps: Vec<(Node, &AStore)> = cfg.flow_r[&n]
                .iter()
                .filter_map(|m| {
                    // Filter out predecessors that are either
                    // unreachable, or have falsified guards on the
                    // transition m --guard-> m
                    let a = abs[m].as_ref()?;
                    match &cfg.guards[&(*m, n)] {
                        Guard::IfTrue(x) => {
                            // If the guard variable is undefined, we
                            // can go sicko mode
                            let v = a.get(x)?;
                            match &hc.v2e[v] {
                                SymExpr::Const(Literal::Bool(false)) => None,
                                _ => Some((*m, a)),
                            }
                        }
                        Guard::IfFalse(x) => {
                            let v = a.get(x)?;
                            match &hc.v2e[v] {
                                SymExpr::Const(Literal::Bool(true)) => None,
                                _ => Some((*m, a)),
                            }
                        }
                        Guard::Always => Some((*m, a)),
                    }
                })
                .collect();
            let astore = join(ps, n, &mut gvg, &mut hc);
            if let Some(mut astore) = astore {
                // Symbolically execute the block
                for (j, inst) in cfg.blocks[i].insts.iter().enumerate() {
                    let iloc = (n, j);
                    step_symbolic(inst, iloc, &mut gvg, &mut astore, &mut hc);
                }
                // If something changed, push successors
                let astore = Some(astore);
                if astore != abs[&n] {
                    // eprintln!("UPDATE AT {n:?}");
                    // diff_abs(&astore, &abs[&n]);
                    abs.insert(n, astore);
                    for succ in &cfg.flow[&n] {
                        worklist.push_back(*succ);
                    }
                }
            } else {
                // Unreachable node
                continue;
            }
        } else {
            // Always push successors for entry
            for succ in &cfg.flow[&n] {
                worklist.push_back(*succ);
            }
        }
    }

    // Write hashcons to dot
    {
        // Make sure the directory exists
        std::fs::create_dir_all("dot").unwrap();
        let path = format!("dot/hc_{}.dot", &func.name);
        let mut file = std::fs::File::create(path).unwrap();
        hc.dot(&mut file, &gvg).unwrap();
    }

    let mut ssa = SSA { cfg, hc, gvg, abs };
    let res = lower(&mut ssa, true);
    let mut instrs: Vec<Code> = vec![];
    for block in res {
        block.emit(&mut instrs);
    }
    Function {
        args: func.args.clone(),
        instrs,
        name: func.name.clone(),
        return_type: func.return_type.clone(),
    }
}

#[cfg(test)]
mod tests {
    use bril_rs::{Code, Function};

    use super::*;
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
}
