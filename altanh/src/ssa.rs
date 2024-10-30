use std::{
    collections::{HashMap, HashSet},
    fmt::{Debug, Display},
    hash::Hash,
    io,
};

use crate::{
    cfg::dominates,
    util::{complete_adj, op_commutative, op_type, scc, topological_order, UFNode, UnionFind},
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

pub enum Expr {
    Const(Literal),
    Var(Var),
    Op(ValueOps, Vec<Expr>),
}

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

type EClassData = (Option<SymExpr>, Option<Type>);
type EClass = UFNode;

pub struct EGraph {
    uf: UnionFind,
    /// e-node -> e-class mapping
    n2c: HashMap<SymExpr, EClass>,
    data: HashMap<EClass, EClassData>,
}

impl EGraph {
    fn new() -> Self {
        EGraph {
            uf: Default::default(),
            n2c: Default::default(),
            data: Default::default(),
        }
    }

    fn canonicalize(&self, enode: SymExpr) -> SymExpr {
        match enode {
            SymExpr::Op(op, args) => {
                let args: Vec<EClass> = args.into_iter().map(|c| self.uf.root(c)).collect();
                SymExpr::Op(op, args)
            }
            _ => enode,
        }
    }

    pub fn insert(&mut self, enode: SymExpr, ty: Option<Type>) -> EClass {
        let enode = self.canonicalize(enode);
        if let Some(c) = self.n2c.get(&enode) {
            *c
        } else {
            let c = self.uf.make_node();
            self.n2c.insert(enode.clone(), c);
            self.data.insert(c, (Some(enode), ty));
            self.simplify(c)
        }
    }

    pub fn canonical_enode(&self, c: EClass) -> Option<SymExpr> {
        self.data[&c].0.clone()
    }

    fn sort_key(&self, c: EClass) -> (i32, EClass) {
        if let Some(SymExpr::Const(_)) = self.canonical_enode(c) {
            (0, c)
        } else {
            (1, c)
        }
    }

    fn is_sorted(&self, args: &Vec<EClass>) -> bool {
        for i in 0..args.len() - 1 {
            if self.sort_key(args[i]) > self.sort_key(args[i + 1]) {
                return false;
            }
        }
        true
    }

    fn try_const(&self, c: EClass, value: Option<Literal>) -> Option<Literal> {
        match (self.canonical_enode(c), value) {
            (Some(SymExpr::Const(lit)), None) => Some(lit),
            (Some(SymExpr::Const(lit)), Some(value)) if lit == value => Some(lit),
            _ => None,
        }
    }

    pub fn simplify(&mut self, c: EClass) -> EClass {
        let c = self.uf.root(c);
        let canonical = self.canonical_enode(c);
        if let Some(canonical) = canonical {
            match canonical {
                SymExpr::Op(op, mut args) if op_commutative(&op) && !self.is_sorted(&args) => {
                    // Sort arguments so constants come first
                    args.sort_by_cached_key(|&c| self.sort_key(c));
                    let c_canonical = self.insert(SymExpr::Op(op, args), self.data[&c].1.clone());
                    self.union(c, c_canonical);
                    self.simplify(c_canonical)
                }
                // 0 + x => x
                SymExpr::Op(ValueOps::Add, args)
                    if self.try_const(args[0], Literal::Int(0).into()).is_some() =>
                {
                    let c_canonical = args[1];
                    self.union(c, c_canonical);
                    self.simplify(c_canonical)
                }
                // 0 * x => 0
                SymExpr::Op(ValueOps::Mul, args)
                    if self.try_const(args[0], Literal::Int(0).into()).is_some() =>
                {
                    let c_canonical = args[0];
                    self.union(c, c_canonical);
                    self.simplify(c_canonical)
                }
                // 1 * x => x
                SymExpr::Op(ValueOps::Mul, args)
                    if self.try_const(args[0], Literal::Int(1).into()).is_some() =>
                {
                    let c_canonical = args[1];
                    self.union(c, c_canonical);
                    self.simplify(c_canonical)
                }
                // x / 1 => x
                SymExpr::Op(ValueOps::Div, args)
                    if self.try_const(args[1], Literal::Int(1).into()).is_some() =>
                {
                    let c_canonical = args[0];
                    self.union(c, c_canonical);
                    self.simplify(c_canonical)
                }
                // x - x => 0
                SymExpr::Op(ValueOps::Sub, args) if self.uf.equiv(args[0], args[1]) => {
                    let c_canonical =
                        self.insert(SymExpr::Const(Literal::Int(0)), Type::Int.into());
                    self.union(c, c_canonical);
                    self.simplify(c_canonical)
                }
                _ => c,
            }
        } else {
            c
        }
    }

    fn merge(&self, (old_e, old_ty): EClassData, (new_e, new_ty): EClassData) -> EClassData {
        assert_eq!(old_ty, new_ty);
        // let (enode, ty) = new;
        // if let Some(enode) = enode {
        //     (Some(self.canonicalize(enode)), ty)
        // } else {
        //     (enode, ty)
        // }
        let e = match (&old_e, &new_e) {
            (None, None) => None,
            (x, None) => panic!("incompatible merge {x:?} with None"),
            (None, y) => panic!("incompatible merge {y:?} with None"),
            (Some(SymExpr::Const(x)), Some(SymExpr::Const(y))) => {
                assert_eq!(x, y);
                old_e
            }
            (Some(SymExpr::Const(_)), _) => old_e,
            (_, Some(SymExpr::Const(_))) => new_e,
            // _ => panic!("incompatible merge {old_e:?} with {new_e:?}"),
            _ => new_e,
        };
        (e, new_ty)
    }

    pub fn union(&mut self, x: EClass, y: EClass) -> EClass {
        if self.uf.equiv(x, y) {
            return x;
        }
        let r = self.uf.merge(x, y);
        let x_d = self.data.remove(&x).unwrap();
        let y_d = self.data.remove(&y).unwrap();
        self.data.insert(r, self.merge(x_d, y_d));
        // Repair the hashcons
        loop {
            let mut repairs: Vec<(SymExpr, SymExpr)> = vec![];
            for enode in self.n2c.keys().cloned() {
                let canonical = self.canonicalize(enode.clone());
                if enode != canonical {
                    repairs.push((enode, canonical));
                }
            }
            if repairs.is_empty() {
                break;
            }
            for (old, new) in repairs {
                let old_c = self.n2c[&old];
                if let Some(new_c) = self.n2c.get(&new).cloned() {
                    if !self.uf.equiv(old_c, new_c) {
                        let old_d = self.data.remove(&old_c).unwrap();
                        let new_d = self.data.remove(&new_c).unwrap();
                        let new_c = self.uf.merge(old_c, new_c);
                        // TODO: merge
                        self.data.insert(new_c, self.merge(old_d, new_d));
                    }
                } else {
                    self.n2c.insert(new, old_c);
                }
                self.n2c.remove(&old);
            }
        }
        r
    }

    pub fn c2n(&self) -> HashMap<EClass, Vec<&SymExpr>> {
        let mut res: HashMap<EClass, Vec<&SymExpr>> = HashMap::new();
        for (n, c) in &self.n2c {
            res.entry(self.uf.root(*c)).or_default().push(n);
        }
        res
    }
}

#[derive(Debug)]
pub struct HashCons {
    e2v: HashMap<SymExpr, ValueNumber>,
    v2e: HashMap<ValueNumber, SymExpr>,
    v2t: HashMap<ValueNumber, Type>,
    // uf: UnionFind,
}

impl Default for HashCons {
    fn default() -> Self {
        let mut hc = HashCons {
            e2v: Default::default(),
            v2e: Default::default(),
            v2t: Default::default(),
            // uf: Default::default(),
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
            SymExpr::Op(op, args) if op_commutative(op) => {
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
                let op_type = op_type(op);
                let op_arity = op_arity(op);
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

    fn repair(&mut self, se: SymExpr, old: ValueNumber, new: ValueNumber) -> ValueNumber {
        let v = self.e2v[&se];
        if v == old {
            self.e2v.insert(se.clone(), new);
            self.v2e.insert(old, se);
            new
        } else {
            let v_new = match &se {
                SymExpr::Op(op, args) => {
                    let args: Vec<ValueNumber> = args
                        .iter()
                        .map(|v| self.repair(self.v2e[v].clone(), old, new))
                        .collect();
                    let se_new = SymExpr::Op(op.clone(), args);
                    self.intern(se_new, self.v2t.get(&v).cloned())
                }
                _ => v,
            };
            if v_new != v {
                self.e2v.insert(se.clone(), v_new);
                self.v2e.insert(v, self.v2e[&v_new].clone());
            }
            v_new
        }
    }

    pub fn subsume(&mut self, old: ValueNumber, new: ValueNumber) {
        assert!(self.v2t[&old] == self.v2t[&new]);
        self.v2e.insert(old, self.v2e[&new].clone());
        let all: Vec<SymExpr> = self.e2v.keys().cloned().collect();
        for se in all {
            self.repair(se, old, new);
        }
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
            writeln!(f, "  {} [label=\"{}\"];", n, s)?;
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
        Instruction::Value {
            dest,
            op: ValueOps::Call,
            args,
            op_type,
            ..
        } => {
            let args: Vec<ValueNumber> = args
                .iter()
                .map(|x| ctx.get(x).cloned().unwrap_or_else(|| hc.bot()))
                .collect();
            let call = hc.effect(iloc, op_type.clone().into());
            gvg.effects.insert(iloc, args);
            ctx.insert(dest.clone(), call);
        }
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
        Instruction::Effect { args, .. } => {
            let args: Vec<ValueNumber> = args
                .iter()
                .map(|x| ctx.get(x).cloned().unwrap_or_else(|| hc.bot()))
                .collect();
            let _effect = hc.effect(iloc, None);
            gvg.effects.insert(iloc, args);
        }
        _ => (),
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
    fn simplify_trivial(&self, phi: ValueNumber, args: &PhiArgs, hc: &mut HashCons) -> ValueNumber {
        // If there are 2 unique value numbers, one of which is phi, then
        // return the other one. If all arguments are phi, return bot. Otherwise
        // return phi.
        let mut vals: HashSet<ValueNumber> = args.iter().map(|(_, v)| *v).collect();
        if vals.len() == 2 && vals.contains(&phi) {
            vals.remove(&phi);
            let val = vals.into_iter().next().unwrap();
            if let SymExpr::Phi(_, _) = &hc.v2e[&val] {
                eprintln!("__phi{phi} ~> __phi{val} = ϕ({:?})", self.phis[&val]);
            } else {
                eprintln!("__phi{phi} ~> __v{val} = {:?}", hc.v2e[&val]);
            }
            val
        } else if vals.len() == 1 && vals.contains(&phi) {
            hc.bot()
        } else {
            phi
        }
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
                    // let val_opt = self.simplify_trivial(val, &args, hc);
                    self.phis.insert(val, args);
                    // val_opt
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
                Instruction::Value {
                    op: ValueOps::Call, ..
                }
                | Instruction::Effect { .. } => {
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
            Some(term) => match term {
                Instruction::Effect { args, .. } => {
                    for &arg in args.iter().map(|x| node_abs.get(x).unwrap()) {
                        entry.insert(arg);
                        entry.extend(tc.get(arg, ssa));
                    }
                }
                _ => unreachable!(),
            },
            _ => (),
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
            .filter(|v| ssa.gvg.phis.contains_key(v))
            .collect();
        for phi in live_phis {
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
                .filter(|&v| {
                    let vn = scopes.get(v, dom_tree, hc);
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

fn lower(cfg: &CFG, ssa: &SSA) -> Vec<Block> {
    type Blocks = HashMap<Node, Block>;

    // eprintln!("{}", ssa.hc);

    fn v2s_impl(v: &ValueNumber, hc: &HashCons) -> String {
        match &hc.v2e[v] {
            SymExpr::Bot => "__undefined".to_string(),
            SymExpr::Phi(_, _) => format!("__phi{v}"),
            SymExpr::Param(p) => p.name.clone(),
            _ => format!("__v{v}"),
        }
    }

    let v2s = |v: &ValueNumber| v2s_impl(v, &ssa.hc);

    fn lower_node(
        node: Node,
        cfg: &CFG,
        ssa: &SSA,
        to_compute: &HashSet<ValueNumber>,
        blocks: &mut Blocks,
    ) {
        let v2s = |v: &ValueNumber| v2s_impl(v, &ssa.hc);
        // Don't lower unreachable blocks
        if !ssa.is_reachable(&node) {
            eprintln!("{node:?} is dead, skipping lowering...");
            return;
        }
        let node_abs = ssa.abs[&node].as_ref().unwrap();
        let pond = pond_of_nodes(node, to_compute, cfg, ssa);
        let order = topological_order(&pond);
        // Lower values in order
        let mut insts: Vec<Instruction> = vec![];
        for v in order {
            let dest = v2s(&v);
            match &ssa.hc.v2e[&v] {
                SymExpr::Const(c) => {
                    insts.push(Instruction::Constant {
                        dest,
                        op: ConstOps::Const,
                        const_type: c.get_type(),
                        value: c.clone(),
                    });
                }
                SymExpr::Op(op, args) => {
                    let args: Vec<String> = args.iter().map(v2s).collect();
                    insts.push(Instruction::Value {
                        args: args,
                        dest,
                        funcs: vec![],
                        labels: vec![],
                        op: op.clone(),
                        op_type: op_type(op),
                    });
                }
                SymExpr::Effect(iloc) => {
                    let args: Vec<String> = ssa.gvg.effects[iloc].iter().map(v2s).collect();
                    // Fetch original instruction
                    let orig = &cfg.get(iloc.0).unwrap().insts[iloc.1];
                    match orig {
                        Instruction::Value {
                            op: ValueOps::Call,
                            funcs,
                            op_type,
                            ..
                        } => {
                            insts.push(Instruction::Value {
                                op: ValueOps::Call,
                                args,
                                dest,
                                funcs: funcs.clone(),
                                labels: vec![],
                                op_type: op_type.clone(),
                            });
                        }
                        Instruction::Effect {
                            funcs,
                            op: op @ (EffectOps::Call | EffectOps::Print),
                            ..
                        } => {
                            insts.push(Instruction::Effect {
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
                    // moves as needed.
                }
                SymExpr::Param(_) => {}
                SymExpr::Bot => (),
            }
        }
        match node {
            Node::Entry => {
                blocks.insert(node, Block::new_flat(insts, None));
            }
            Node::Block(_) => {
                let orig = cfg.get(node).unwrap();
                let term = if let Some(term) = &orig.term {
                    match term {
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
                                SymExpr::Const(Literal::Bool(true)) => Some(Instruction::Effect {
                                    args: vec![],
                                    funcs: vec![],
                                    labels: vec![labels[0].clone()],
                                    op: EffectOps::Jump,
                                }),
                                SymExpr::Const(Literal::Bool(false)) => Some(Instruction::Effect {
                                    args: vec![],
                                    funcs: vec![],
                                    labels: vec![labels[1].clone()],
                                    op: EffectOps::Jump,
                                }),
                                _ => Some(Instruction::Effect {
                                    args: vec![v2s(&cond)],
                                    funcs: vec![],
                                    labels: labels.clone(),
                                    op: EffectOps::Branch,
                                }),
                            }
                        }
                        Instruction::Effect {
                            args,
                            funcs,
                            labels,
                            op,
                        } => {
                            let args: Vec<String> =
                                args.iter().map(|x| node_abs[x]).map(|v| v2s(&v)).collect();
                            Some(Instruction::Effect {
                                args,
                                funcs: funcs.clone(),
                                labels: labels.clone(),
                                op: op.clone(),
                            })
                        }
                        _ => unreachable!(),
                    }
                } else {
                    None
                };
                blocks.insert(node, Block::new(insts, term, orig.label.clone()));
            }
            _ => (),
        }
    }

    let dom_tree = cfg.dom_tree();
    let mut scopes = ScopeMemo::default();

    let used = used_values(cfg, ssa);
    let live = {
        let mut live: HashSet<ValueNumber> = HashSet::new();
        for s in used.values() {
            live.extend(s);
        }
        live
    };
    let vb = very_busy(&used, cfg);
    let av = available(&used, cfg, ssa);
    let pre = earliest(&av, &vb, &dom_tree, &ssa.hc, &mut scopes);
    let used_pre = merge_sets(&used, &pre);
    let av_pre = available(&used_pre, cfg, ssa);
    let to_compute = diff_sets(&used_pre, &av_pre);

    // let len = cfg.blocks.len();
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
        cfg,
        ssa,
        &to_compute[&Node::Entry],
        &mut blocks,
    );
    for i in 0..cfg.blocks.len() {
        let node = Node::Block(i);
        // lower_node(*node, &scopes, cfg, ssa, &mut blocks);
        lower_node(node, cfg, ssa, &to_compute[&node], &mut blocks);
    }

    // phi_move[n][phi] = v means at n, we want a move `phi = id v`.
    let mut phi_moves: HashMap<Node, HashMap<ValueNumber, HashSet<ValueNumber>>> = HashMap::new();
    for (phi, phi_args) in &ssa.gvg.phis {
        // assert!(live.contains(phi));
        if !live.contains(phi) {
            eprintln!("__phi{phi} is dead, skipping...");
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
        let block = blocks.entry(*node).or_default();
        // Compute SCC DAG.
        let (dag, sccs) = scc(phi_adj);
        // Linearize DAG
        let order = topological_order(&dag);
        // Process each component
        for root in order {
            if dag[&root].is_empty() {
                // Either root is a leaf, or it was an identity move root ->
                // root which has been collapsed into a single node. In either
                // case, nothing to do.
            } else if sccs[&root].len() == 1 {
                let arg_val = phi_adj[&root].iter().next().unwrap();
                // No cycle; just emit the move
                block.insts.push(Instruction::Value {
                    args: vec![v2s(arg_val)],
                    dest: format!("__phi{root}"),
                    funcs: vec![],
                    labels: vec![],
                    op: ValueOps::Id,
                    op_type: ssa.hc.v2t[&root].clone(),
                });
            } else {
                // NB: since every edge x -> y is a phi move x := y, and there
                // are never two moves for the same phi, it follows that every
                // node has a single successor. Thus, all SCCs in this graph are
                // simple cycles and can be traversed by following the edges
                // from the root node.

                // Introduce a temporary to break the cycle
                let temp = format!("__temp{root}");
                block.insts.push(Instruction::Value {
                    args: vec![v2s(&root)],
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
                        args: vec![v2s(arg_val)],
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

    res.push(blocks.get(&Node::Entry).unwrap().clone());
    for i in 0..cfg.blocks.len() {
        let node = Node::Block(i);
        if ssa.abs[&node].is_none() {
            continue;
        }
        res.push(blocks.get(&node).unwrap().clone());
    }
    res
}

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

fn kill_phis(mut ssa: SSA) -> SSA {
    fn kill_phis_rec(
        phis: Vec<ValueNumber>,
        ssa: &SSA,
        kill: &mut HashMap<ValueNumber, ValueNumber>,
    ) {
        let mut phi_graph: HashMap<ValueNumber, HashSet<ValueNumber>> = Default::default();
        for phi in phis {
            for &(_, v) in &ssa.gvg.phis[&phi] {
                if ssa.gvg.phis.contains_key(&v) {
                    phi_graph.entry(v).or_default().insert(phi);
                }
            }
        }
        complete_adj(&mut phi_graph);
        let (dag, sccs) = scc(&phi_graph);
        eprintln!("SCCs: {:?}", sccs);
        eprintln!("DAG: {:?}", dag);
        let order = topological_order(&dag);
        for root in order {
            let scc = &sccs[&root];
            if scc.len() == 1 {
                // Try to kill trivial phis
                let mut args: HashSet<ValueNumber> =
                    ssa.gvg.phis[&root].iter().map(|(_, v)| *v).collect();
                match args.len() {
                    1 => unreachable!("ϕ(x,x) should never be created"),
                    2 if args.contains(&root) => {
                        args.remove(&root);
                        kill.insert(root, *args.iter().next().unwrap());
                    }
                    _ => (),
                }
            } else {
                let mut outer_ops: HashSet<ValueNumber> = Default::default();
                let mut inner: Vec<ValueNumber> = Default::default();
                for phi in scc {
                    let mut is_inner = true;
                    for (_, arg) in &ssa.gvg.phis[phi] {
                        if !scc.contains(arg) {
                            outer_ops.insert(*arg);
                            is_inner = false;
                        }
                    }
                    if is_inner {
                        inner.push(*phi);
                    }
                }
                match outer_ops.len() {
                    0 => unreachable!("closed ϕ cycle, how is this possible???"),
                    1 => {
                        let kill_with = *outer_ops.iter().next().unwrap();
                        let kill_with = kill.get(&kill_with).cloned().unwrap_or(kill_with);
                        for &phi in scc {
                            kill.insert(phi, kill_with);
                        }
                    }
                    _ => {
                        kill_phis_rec(inner, ssa, kill);
                    }
                }
            }
        }
    }

    // Kill unused phis
    // {
    //     let used: HashSet<ValueNumber> = used_values(&ssa.cfg, &ssa)
    //         .values()
    //         .flatten()
    //         .cloned()
    //         .collect();
    //     let kill: Vec<ValueNumber> = ssa
    //         .gvg
    //         .phis
    //         .keys()
    //         .filter(|v| !used.contains(v))
    //         .cloned()
    //         .collect();
    //     for phi in kill {
    //         ssa.gvg.phis.remove(&phi);
    //     }
    // }

    let mut kill: HashMap<ValueNumber, ValueNumber> = Default::default();
    kill_phis_rec(ssa.gvg.phis.keys().cloned().collect(), &ssa, &mut kill);
    eprintln!("kill: {kill:?}");
    let kill_with: HashSet<ValueNumber> = kill.values().cloned().collect();
    let killed: HashSet<ValueNumber> = kill.keys().cloned().collect();
    eprintln!("{killed:?}");
    eprintln!("{kill_with:?}");
    let try_kill = |v: &mut ValueNumber| {
        let mut kill_with: &usize = v;
        while let Some(next) = kill.get(kill_with) {
            kill_with = next;
        }
        *v = *kill_with;
    };
    eprintln!("{}", ssa.hc);
    for old in kill.keys() {
        let mut new = old;
        while let Some(next) = kill.get(new) {
            new = next;
        }
        ssa.hc.subsume(*old, *new);
    }
    eprintln!("{}", ssa.hc);
    // // Remove dead phis
    for killed in kill.keys() {
        ssa.gvg.phis.remove(killed);
    }
    // Update living phi arguments
    for args in ssa.gvg.phis.values_mut() {
        for (_, v) in args.iter_mut() {
            try_kill(v);
        }
    }
    // Update effect arguments
    for args in ssa.gvg.effects.values_mut() {
        for v in args.iter_mut() {
            try_kill(v);
        }
    }
    // Update abstractions
    for a in ssa.abs.values_mut() {
        if let Some(a) = a {
            for v in a.values_mut() {
                try_kill(v);
            }
        }
    }
    ssa
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

    let ssa = SSA { cfg, hc, gvg, abs };
    // Write hashcons to dot
    {
        // Make sure the directory exists
        std::fs::create_dir_all("dot").unwrap();
        let path = format!("dot/hc_nokill_{}.dot", &func.name);
        let mut file = std::fs::File::create(path).unwrap();
        ssa.hc.dot(&mut file, &ssa.gvg).unwrap();
    }
    let ssa = kill_phis(ssa);
    // Write hashcons to dot
    {
        // Make sure the directory exists
        std::fs::create_dir_all("dot").unwrap();
        let path = format!("dot/hc_kill_{}.dot", &func.name);
        let mut file = std::fs::File::create(path).unwrap();
        ssa.hc.dot(&mut file, &ssa.gvg).unwrap();
    }

    let res = lower(&ssa.cfg, &ssa);
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
    use super::*;

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
    fn test_egraph_basic() {
        let mut egraph = EGraph::new();
        let a = egraph.insert(SymExpr::Const(Literal::Int(1)), None);
        let b = egraph.insert(SymExpr::Phi(vec![], Node::Entry), None);
        let c = egraph.insert(SymExpr::Const(Literal::Int(2)), None);
        let add1 = egraph.insert(SymExpr::Op(ValueOps::Add, vec![a, b]), None);
        let add2 = egraph.insert(SymExpr::Op(ValueOps::Add, vec![a, c]), None);

        {
            println!("BEFORE UNION");
            let c2n = egraph.c2n();
            for (c, n) in c2n {
                println!("{c}: {n:?}");
            }
            println!("{:?}", egraph.data);
        }

        egraph.union(b, c);

        {
            println!("AFTER UNION");
            let c2n = egraph.c2n();
            for (c, n) in c2n {
                println!("{c}: {n:?}");
            }
            println!("{:?}", egraph.data);
        }
    }

    #[test]
    fn test_egraph_comm() {
        let mut egraph = EGraph::new();
        let a = egraph.insert(SymExpr::Const(Literal::Int(0)), None);
        let b = egraph.insert(SymExpr::Const(Literal::Int(1)), None);
        let c = egraph.insert(SymExpr::Phi(vec![], Node::Entry), None);
        let add1 = egraph.insert(SymExpr::Op(ValueOps::Add, vec![b, a]), None);
        let add2 = egraph.insert(SymExpr::Op(ValueOps::Add, vec![c, b]), None);

        {
            println!("BEFORE UNION");
            let c2n = egraph.c2n();
            for (c, n) in c2n {
                println!("{c}: {n:?}");
            }
            println!("{:?}", egraph.data);
            println!("{:?}", egraph.uf.sets());
        }

        egraph.union(b, c);

        {
            println!("AFTER UNION");
            let c2n = egraph.c2n();
            for (c, n) in c2n {
                println!("{c}: {n:?}");
            }
            println!("{:?}", egraph.data);
            println!("{:?}", egraph.uf.sets());
        }
    }

    #[test]
    fn test_egraph_arith() {
        let mut egraph = EGraph::new();
        let mut int =
            |i: i64, e: &mut EGraph| e.insert(SymExpr::Const(Literal::Int(i)), Type::Int.into());
        let mut mul = |a: EClass, b: EClass, e: &mut EGraph| {
            e.insert(SymExpr::Op(ValueOps::Mul, vec![a, b]), Type::Int.into())
        };
        let mut add = |a: EClass, b: EClass, e: &mut EGraph| {
            e.insert(SymExpr::Op(ValueOps::Add, vec![a, b]), Type::Int.into())
        };
        let mut sub = |a: EClass, b: EClass, e: &mut EGraph| {
            e.insert(SymExpr::Op(ValueOps::Sub, vec![a, b]), Type::Int.into())
        };
        let mut div = |a: EClass, b: EClass, e: &mut EGraph| {
            e.insert(SymExpr::Op(ValueOps::Div, vec![a, b]), Type::Int.into())
        };

        let _0 = int(0, &mut egraph);
        let _1 = int(1, &mut egraph);
        let _2 = int(2, &mut egraph);
        let _0_mul = mul(_0, _2, &mut egraph);
        let _0_sub = sub(_1, _1, &mut egraph);
        let _2_mul = mul(_1, _2, &mut egraph);

        let c2n = egraph.c2n();
        for (c, n) in c2n {
            println!("{c}: {n:?}");
        }
        println!("{:?}", egraph.data);
        println!("{:?}", egraph.uf.sets());
    }
}
