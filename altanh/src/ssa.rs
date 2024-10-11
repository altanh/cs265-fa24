use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    io,
};

use crate::cfg::{Block, Node, CFG};
use bril_rs::{Instruction, Literal, ValueOps};

// TODO(altanh): intern
type Var = String;
type Location = Node;
type InstructionLocation = (Node, usize);
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
    Param(Var),
    Phi(ValueNumber, Location),
    Call(InstructionLocation),
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
        SymExpr::Phi(var.0, var.1)
    }
}

#[derive(Debug, Default)]
pub struct HashCons(HashMap<SymExpr, ValueNumber>, HashMap<ValueNumber, SymExpr>);

impl HashCons {
    pub fn param(&mut self, var: Var) -> ValueNumber {
        self.intern(SymExpr::Param(var))
    }

    /// Warning: this will always return a new value number!
    pub fn phi(&mut self, loc: Location) -> ValueNumber {
        let n = self.0.len();
        let v = SymExpr::Phi(n, loc);
        self.0.insert(v.clone(), n);
        self.1.insert(n, v);
        n
    }

    pub fn call(&mut self, loc: InstructionLocation) -> ValueNumber {
        self.intern(SymExpr::Call(loc))
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

    pub fn dot<F>(&self, f: &mut F, g: &GlobalValueGraph) -> io::Result<()>
    where
        F: io::Write,
    {
        writeln!(f, "digraph {{")?;
        for (se, n) in &self.0 {
            let s = match se {
                SymExpr::Const(lit) => format!("{:?}", lit),
                // SymExpr::Var((n, loc)) => format!("{}@{:?}", n, loc),
                SymExpr::Param(var) => format!("{var}"),
                SymExpr::Phi(_, loc) => format!("ϕ{n} @ {loc:?}"),
                SymExpr::Call((n, i)) => format!("call @{n:?}.{i}"),
                SymExpr::Op(Op::Builtin(op), _) => {
                    format!("{:?}", op)
                }
                SymExpr::Op(Op::Extern(func), _) => {
                    format!("@{}", func)
                }
                SymExpr::Bot => "⊥".to_string(),
            };
            writeln!(f, "  {} [label=\"{}\"];", n, s)?;
        }
        // Write phi edges
        for (_, phi) in &g.phis {
            for (vars, val) in phi {
                for (i, v) in vars.iter().enumerate() {
                    writeln!(f, "  {} -> {} [label=\".{}\"];", val, v.1, i)?;
                }
            }
        }
        // Write pure dataflow edges
        for (se, n) in &self.0 {
            if let SymExpr::Op(_, args) = se {
                for (i, arg) in args.iter().enumerate() {
                    // Write dotted edge
                    writeln!(f, "  {} -> {} [style=dotted, label=\".{}\"];", n, arg, i)?;
                }
            }
        }
        // Write call edges
        for (call, args) in &g.call_args {
            for (i, arg) in args.iter().enumerate() {
                writeln!(f, "  {} -> {} [style=dotted, label=\".{}\"];", call, arg, i)?;
            }
        }
        writeln!(f, "}}")
    }
}

/// TODO(altanh): functional map
pub type AStore = HashMap<Var, ValueNumber>;

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

fn step_symbolic(
    i: &Instruction,
    iloc: InstructionLocation,
    gvg: &mut GlobalValueGraph,
    ctx: &mut AStore,
    hc: &mut HashCons,
) {
    match i {
        Instruction::Constant { dest, value, .. } => {
            ctx.insert(dest.clone(), hc.intern(value.clone().into()));
        }
        Instruction::Value {
            dest,
            op: ValueOps::Call,
            args,
            ..
        } => {
            // TODO(altanh): this is unsound; the function may have side
            // effects! How best to model memory and print effects?
            // ctx.insert(
            //     dest.clone(),
            //     eval_symbolic(
            //         &Expr::Op(
            //             Op::Extern(funcs[0].clone()),
            //             args.iter().map(|x| Expr::Var(x.clone())).collect(),
            //         ),
            //         &ctx,
            //         hc,
            //     ),
            // );
            let call = gvg.calls.entry(iloc).or_insert_with(|| hc.call(iloc));
            gvg.call_args.insert(
                *call,
                args.iter()
                    .map(|x| {
                        ctx.get(x)
                            .cloned()
                            .unwrap_or_else(|| hc.intern(SymExpr::Bot))
                    })
                    .collect(),
            );
            ctx.insert(dest.clone(), *call);
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
pub struct GlobalValueGraph {
    pub phis: HashMap<Node, Phi>,
    pub phi_vars: HashMap<(Vec<Var>, Location), ValueNumber>,
    pub calls: HashMap<InstructionLocation, ValueNumber>,
    pub call_args: HashMap<ValueNumber, Vec<ValueNumber>>,
}

impl Display for GlobalValueGraph {
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

impl GlobalValueGraph {
    fn clear_phis(&mut self, loc: Node) {
        self.phis.remove(&loc);
    }

    fn phi_entry(&mut self, loc: Node) -> &mut Phi {
        self.phis.entry(loc).or_insert(Default::default())
    }

    // See "Simple and Efficient Construction of Static Single Assignment
    // Form" by Braun et al. for details.
    fn simplify_trivial(&self, phi: ValueNumber, args: &PhiArgs, hc: &mut HashCons) -> ValueNumber {
        // If there are at 2 unique value numbers, one of which is phi, then
        // return the other one. If all arguments are phi, return bot. Otherwise
        // return phi.
        let mut vals: HashSet<ValueNumber> = args.iter().map(|(_, v)| *v).collect();
        if vals.len() == 2 && vals.contains(&phi) {
            vals.remove(&phi);
            vals.into_iter().next().unwrap()
        } else if vals.len() == 1 && vals.contains(&phi) {
            hc.intern(SymExpr::Bot)
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
        self.clear_phis(loc);
        // Collect all variables with the same phi arguments
        let mut vars: HashMap<PhiArgs, Vec<String>> = HashMap::new();
        for (k, args) in store {
            vars.entry(args).or_insert_with(Vec::new).push(k);
        }
        // Create symbolic variables for each set of equal variables and update
        // phi entries
        let mut result: AStore = Default::default();
        for (args, vars) in vars {
            let val = match args.len() {
                0 => unreachable!(),
                1 => args[0].1,
                _ => {
                    let val = *self
                        .phi_vars
                        .entry((vars.clone(), loc))
                        .or_insert_with(|| hc.phi(loc));
                    let val = self.simplify_trivial(val, &args, hc);
                    self.phi_entry(loc).insert(args, val);
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
    gvg: &mut GlobalValueGraph,
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
                // Skip undefined values.
                if *e == hc.intern(SymExpr::Bot) {
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
            let mut gvg: GlobalValueGraph = Default::default();

            hc.intern(SymExpr::Bot);

            // Initial abstract store: parameters are mapped to their symbolic
            // values, all other variables are (implicitly) mapped to ⊥.
            let mut initial: AStore = HashMap::new();
            for arg in &func.args {
                initial.insert(arg.name.clone(), hc.param(arg.name.clone()));
            }

            let mut abs: HashMap<Node, Option<AStore>> = HashMap::new();
            for node in cfg.flow.keys() {
                abs.insert(*node, None);
            }
            abs.insert(Node::Entry, Some(initial));

            // Initalize worklist with reverse postorder traversal of the CFG
            let mut worklist: VecDeque<Node> = VecDeque::new();
            let mut visited: HashSet<Node> = HashSet::new();

            fn visit(
                node: Node,
                cfg: &CFG,
                worklist: &mut VecDeque<Node>,
                visited: &mut HashSet<Node>,
            ) {
                if visited.contains(&node) {
                    return;
                }
                visited.insert(node);
                if let Some(succs) = cfg.flow.get(&node) {
                    for succ in succs {
                        visit(*succ, cfg, worklist, visited);
                    }
                }
                worklist.push_front(node);
            }

            visit(Node::Entry, &cfg, &mut worklist, &mut visited);

            println!("worklist: {:?}", worklist);

            let mut iter = 0;
            while let Some(n) = worklist.pop_front() {
                println!("iter {iter} at {n:?}: ");
                if let Node::Block(i) = n {
                    let ps: Vec<(Node, &Option<AStore>)> =
                        cfg.flow_r[&n].iter().map(|m| (*m, &abs[m])).collect();
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
                            // Print the diff
                            println!("update at {:?}", n);
                            if let Some(astore) = &astore {
                                let ch = hc.transpose();
                                for (var, val) in astore {
                                    println!(
                                        "    {}: {} -> {:?}",
                                        var,
                                        if let Some(a) = &abs[&n] {
                                            let s = if let Some(val) = a.get(var) {
                                                format!("{:?}", ch[val])
                                            } else {
                                                "⊥".to_string()
                                            };
                                            format!("{}", s)
                                        } else {
                                            "⊥".to_string()
                                        },
                                        ch[val]
                                    );
                                }
                            }
                            abs.insert(n, astore);
                            for succ in &cfg.flow[&n] {
                                worklist.push_back(*succ);
                            }
                        }
                    } else {
                        continue;
                    }
                } else {
                    // Always push successors for entry
                    for succ in &cfg.flow[&n] {
                        worklist.push_back(*succ);
                    }
                }
                iter += 1;
            }

            // Print the abstract store at each block
            let ch = hc.transpose();
            let print = |node: Node, store: &Option<AStore>| {
                let node_name = match node {
                    Node::Block(i) => cfg.blocks[i].label.clone().unwrap_or_else(|| i.to_string()),
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
            };
            print(Node::Entry, &abs[&Node::Entry]);
            for i in 0..cfg.blocks.len() {
                print(Node::Block(i), &abs[&Node::Block(i)]);
            }
            print(Node::Exit, abs.get(&Node::Exit).unwrap_or(&None));

            // Print the hashcons
            println!("{}", hc);
            {
                // Dot
                let mut file = std::fs::File::create(format!("dot/{}_hc.dot", func.name)).unwrap();
                hc.dot(&mut file, &gvg).unwrap();
            }

            // Print the phis
            println!("{}", gvg);

            {
                // Write the CFG to a file
                let mut file = std::fs::File::create(format!("dot/{}.dot", func.name)).unwrap();
                cfg.dot(&mut file).unwrap();
            }
        }
    }
}
