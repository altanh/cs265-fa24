use std::{
    collections::{HashMap, HashSet},
    fmt::{Debug, Display},
    hash::Hash,
    io,
};

use crate::{
    cfg::{dominates, BlockBuilder, Fallthrough},
    util::{complete_adj, is_commutative, is_effectful, op_type, scc, topological_order},
    value::{rules, translate_effectful_op, translate_pure_op, Bril, EffectWrapper, Type},
};
use crate::{
    cfg::{Block, Guard, Node, CFG},
    util::op_arity,
};
use bril_rs::{Argument, Code, ConstOps, EffectOps, Function, Instruction, Literal, ValueOps};

use egg::{Id, RecExpr};

pub type EGraph = egg::EGraph<Bril, ()>;

/// TODO(altanh): functional map
pub type AStore = HashMap<String, Id>;
pub type Loc = Node;
pub type ILoc = (Node, usize);
type PhiArgs = Vec<(Node, Id)>;

#[derive(Debug, Default)]
pub struct GlobalValueGraph {
    pub phis: HashMap<Id, PhiArgs>,
    pub effects: HashMap<ILoc, Id>,
}

fn state_var() -> String {
    format!("__state")
}

fn eval_symbolic(op: ValueOps, args: Vec<Id>, eg: &mut EGraph) -> Id {
    assert!(!is_effectful(&op));
    eg.add(translate_pure_op(op, args))
}

fn bot(eg: &EGraph) -> Id {
    eg.lookup(Bril::Bot).unwrap()
}

fn string(s: String, eg: &mut EGraph) -> Id {
    eg.add(Bril::String(s))
}

fn list(vs: Vec<Id>, eg: &mut EGraph) -> Id {
    eg.add(Bril::List(vs))
}

fn step_symbolic(
    inst: &Instruction,
    iloc: ILoc,
    gvg: &mut GlobalValueGraph,
    ctx: &mut AStore,
    eg: &mut EGraph,
) {
    match inst {
        Instruction::Constant { dest, value, .. } => {
            let v = match value {
                Literal::Int(i) => eg.add(Bril::Int(*i)),
                Literal::Bool(b) => eg.add(Bril::Bool(*b)),
            };
            ctx.insert(dest.clone(), v);
        }
        // Effectful operations
        Instruction::Value {
            dest,
            op,
            args,
            funcs,
            ..
        } if is_effectful(op) => {
            let mut args: Vec<Id> = args
                .iter()
                .map(|x| ctx.get(x).cloned().unwrap_or_else(|| bot(eg)))
                .collect();
            // Normalize variadic arguments
            match op {
                ValueOps::Call => {
                    // (args...) -> (func (list args...))
                    args = vec![string(funcs[0].clone(), eg), list(args, eg)];
                }
                _ => (),
            }
            let in_state = ctx[&state_var()];
            let result = eg.add(translate_effectful_op(
                EffectWrapper::VOp(op.clone()),
                in_state,
                args,
            ));
            let value = eg.add(Bril::Fst(result));
            let out_state = eg.add(Bril::Snd(result));
            gvg.effects.insert(iloc, result);
            // Update value and state
            ctx.insert(dest.clone(), value);
            ctx.insert(state_var(), out_state);
        }
        Instruction::Effect {
            op, args, funcs, ..
        } => {
            let mut args: Vec<Id> = args
                .iter()
                .map(|x| ctx.get(x).cloned().unwrap_or_else(|| bot(eg)))
                .collect();
            // Normalize variadic arguments
            match op {
                EffectOps::Call => {
                    // (args...) -> (func (list args...))
                    args = vec![string(funcs[0].clone(), eg), list(args, eg)];
                }
                EffectOps::Print => {
                    // (args...) -> (print (list args...))
                    args = vec![list(args, eg)];
                }
                _ => (),
            }
            let in_state = ctx[&state_var()];
            let result = eg.add(translate_effectful_op(
                EffectWrapper::EOp(op.clone()),
                in_state,
                args,
            ));
            let out_state = eg.add(Bril::Snd(result));
            gvg.effects.insert(iloc, result);
            // Update state
            ctx.insert(state_var(), out_state);
        }
        // Pure operations
        Instruction::Value { args, dest, op, .. } => {
            let args: Vec<Id> = args
                .iter()
                .map(|x| ctx.get(x).cloned().unwrap_or_else(|| bot(eg)))
                .collect();
            let value = eval_symbolic(op.clone(), args, eg);
            ctx.insert(dest.clone(), value);
        }
    }
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
        loc: Loc,
        store: HashMap<String, PhiArgs>,
        eg: &mut EGraph,
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
                    let vars: Vec<Id> = vars
                        .iter()
                        .map(|x| eg.add(Bril::String(x.clone())))
                        .collect();
                    let vars = list(vars, eg);
                    let loc = eg.add(Bril::Node(loc));
                    let phi = eg.add(Bril::Phi([vars, loc]));
                    phi
                }
            };
            for var in vars {
                result.insert(var, val);
            }
        }
        result
    }
}

struct SSA {
    cfg: CFG,
    eg: EGraph,
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
    loc: Loc,
    gvg: &mut GlobalValueGraph,
    eg: &mut EGraph,
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
        let mut result: HashMap<String, (PhiArgs, HashSet<Id>)> = HashMap::new();
        for (n, s) in stores {
            for (x, e) in s {
                // Skip undefined values.
                if *e == bot(eg) {
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
        Some(gvg.insert_phis(loc, result, eg))
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

pub fn compute_ssa(func: &Function) {
    let cfg = CFG::new(func);
    let mut eg: EGraph = Default::default();
    eg.add(Bril::Bot);
    let mut gvg: GlobalValueGraph = Default::default();

    // Initial abstract store: parameters are mapped to their symbolic
    // values, all other variables are (implicitly) mapped to ⊥.
    let mut initial: AStore = HashMap::new();
    for arg in &func.args {
        // initial.insert(arg.name.clone(), hc.param(arg.clone()));
        let ty: Id = eg.add(Bril::Type(arg.arg_type.clone().into()));
        let name: Id = eg.add_expr(&arg.name.clone().parse().unwrap());
        let param: Id = eg.add(Bril::Param([name, ty]));
        initial.insert(arg.name.clone(), param);
    }
    // Initial state
    {
        let sv = state_var();
        let state = eg.add_expr(&sv.parse().unwrap());
        initial.insert(sv, state);
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
                        // Guard::IfTrue(x) => {
                        //     // If the guard variable is undefined, we
                        //     // can go sicko mode
                        //     let v = a.get(x)?;
                        //     match &hc.v2e[v] {
                        //         SymExpr::Const(Literal::Bool(false)) => None,
                        //         _ => Some((*m, a)),
                        //     }
                        // }
                        // Guard::IfFalse(x) => {
                        //     let v = a.get(x)?;
                        //     match &hc.v2e[v] {
                        //         SymExpr::Const(Literal::Bool(true)) => None,
                        //         _ => Some((*m, a)),
                        //     }
                        // }
                        // Guard::Always => Some((*m, a)),
                        _ => Some((*m, a)),
                    }
                })
                .collect();
            let astore = join(ps, n, &mut gvg, &mut eg);
            if let Some(mut astore) = astore {
                // Symbolically execute the block
                for (j, inst) in cfg.blocks[i].insts.iter().enumerate() {
                    let iloc = (n, j);
                    step_symbolic(inst, iloc, &mut gvg, &mut astore, &mut eg);
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

    // Run rewrites
    let rws = rules();
    let runner = egg::Runner::default().with_egraph(eg);
    let runner = runner.run(&rws);
    let eg = runner.egraph;

    // Write hashcons to dot
    {
        // Make sure the directory exists
        std::fs::create_dir_all("dot").unwrap();
        let path = format!("dot/egraph_{}.dot", &func.name);
        eg.dot().to_dot(path).unwrap();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_egraph_ai() {
        let prog = bril_rs::load_program();
        for func in &prog.functions {
            compute_ssa(func);
        }
    }
}
