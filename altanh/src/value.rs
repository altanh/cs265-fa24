use std::{collections::HashSet, fmt::Display, ops::DerefMut, path::Path, str::FromStr};

use bril_rs::{Argument, EffectOps, Literal, ValueOps};
use egg::{
    define_language, merge_option, rewrite as rw, Analysis, CostFunction, DidMerge, Id, Language,
    RecExpr, Rewrite, Subst, Symbol,
};

use crate::cfg::Node;

pub type Loc = Node;
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ILoc(pub Node, pub usize);
// type Id = usize;

impl Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Node::Entry => write!(f, "entry"),
            Node::Exit => write!(f, "exit"),
            Node::Block(id) => write!(f, "block:{}", id),
        }
    }
}

impl Display for ILoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}", self.0, self.1)
    }
}

impl FromStr for Node {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s == "entry" {
            Ok(Node::Entry)
        } else if s == "exit" {
            Ok(Node::Exit)
        } else if s.starts_with("block:") {
            Ok(Node::Block(s[6..].parse().unwrap()))
        } else {
            Err(format!("Invalid node: {}", s))
        }
    }
}

impl FromStr for ILoc {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut parts = s.split('.');
        let node = parts
            .next()
            .ok_or_else(|| format!("Missing ILoc node"))?
            .parse()?;
        let index = parts
            .next()
            .ok_or_else(|| format!("Missing ILoc index"))?
            .parse()
            .map_err(|_| format!("Invalid ILoc index"))?;
        Ok(ILoc(node, index))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Type {
    Unit, // We use this for state variables and non-value operations
    Int,
    Bool,
    Ptr(Box<Type>),
    Pair(Box<Type>, Box<Type>),
}

impl From<bril_rs::Type> for Type {
    fn from(value: bril_rs::Type) -> Self {
        match value {
            bril_rs::Type::Int => Type::Int,
            bril_rs::Type::Bool => Type::Bool,
            bril_rs::Type::Pointer(t) => Type::Ptr(Box::new((*t).into())),
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Unit => write!(f, "unit"),
            Type::Int => write!(f, "int"),
            Type::Bool => write!(f, "bool"),
            Type::Ptr(t) => write!(f, "ptr<{}>", t),
            Type::Pair(t1, t2) => write!(f, "pair<{},{}>", t1, t2),
        }
    }
}

impl FromStr for Type {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s == "int" {
            Ok(Type::Int)
        } else if s == "bool" {
            Ok(Type::Bool)
        } else if s == "unit" {
            Ok(Type::Unit)
        } else if s.starts_with("ptr<") && s.ends_with('>') {
            Ok(Type::Ptr(Box::new(s[4..s.len() - 1].parse().unwrap())))
        } else if s.starts_with("pair<") && s.ends_with('>') {
            // TODO(altanh): this breaks with nested pairs but we won't create
            // those for now, or maybe ever
            let mut parts = s[5..s.len() - 1].split(',');
            let t1 = parts.next().unwrap().parse().unwrap();
            let t2 = parts.next().unwrap().parse().unwrap();
            Ok(Type::Pair(Box::new(t1), Box::new(t2)))
        } else {
            Err(format!("Invalid type: {}", s))
        }
    }
}

define_language! {
    pub enum Bril {
        "bot" = Bot,

        // Literal values
        Int(i64),
        Bool(bool),
        // Node(Node),
        ILoc(ILoc),

        // Type annotation for function parameters
        Type(Type),
        "param" = Param([Id; 2]),

        // Variadic wrapper
        "list" = List(Vec<Id>),

        // (phi (list x y z) (block:0) type)
        "phi" = Phi([Id; 3]),

        // Pure operations
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        "=" = Eq([Id; 2]),
        "<" = Lt([Id; 2]),
        ">" = Gt([Id; 2]),
        "<=" = Le([Id; 2]),
        ">=" = Ge([Id; 2]),
        "!" = Not(Id),
        "&&" = And([Id; 2]),
        "||" = Or([Id; 2]),
        "id" = Id(Id),
        "&+" = PtrAdd([Id; 2]),

        // val = (fst (call s f xs))
        "fst" = Fst(Id),
        // state = (snd (call s f xs))
        "snd" = Snd(Id),

        "load" = Load([Id; 2]),    //      (load state ptr): S -> P X -> X
        // Effectful operations: they take a state and return a state
        "alloc" = Alloc([Id; 4]),  // (alloc state iloc size ret_ty): (P X, S)
        "call" = Call([Id; 4]),    // (call state fun args ret_ty): S -> F -> X -> * -> (Y, S)
        "store" = Store([Id; 3]),  // (store state ptr val): S -> P X -> X -> S
        "free" = Free([Id; 2]),    //      (free state ptr): S -> P X -> S
        "print" = Print([Id; 2]),  //    (print state vals): S -> X -> S
        Symbol(Symbol),
    }
}

pub fn translate_pure_op(op: ValueOps, args: Vec<Id>) -> Bril {
    match op {
        ValueOps::Add => Bril::Add([args[0], args[1]]),
        ValueOps::Sub => Bril::Sub([args[0], args[1]]),
        ValueOps::Mul => Bril::Mul([args[0], args[1]]),
        ValueOps::Div => Bril::Div([args[0], args[1]]),
        ValueOps::Eq => Bril::Eq([args[0], args[1]]),
        ValueOps::Lt => Bril::Lt([args[0], args[1]]),
        ValueOps::Gt => Bril::Gt([args[0], args[1]]),
        ValueOps::Le => Bril::Le([args[0], args[1]]),
        ValueOps::Ge => Bril::Ge([args[0], args[1]]),
        ValueOps::And => Bril::And([args[0], args[1]]),
        ValueOps::Or => Bril::Or([args[0], args[1]]),
        ValueOps::Not => Bril::Not(args[0]),
        ValueOps::PtrAdd => Bril::PtrAdd([args[0], args[1]]),
        ValueOps::Id => Bril::Id(args[0]),
        _ => panic!("Unexpected operation: {:?}", op),
    }
}

pub enum EffectWrapper {
    VOp(ValueOps),
    EOp(EffectOps),
}

pub fn translate_effectful_op(op: EffectWrapper, state: Id, args: Vec<Id>) -> Bril {
    match op {
        EffectWrapper::VOp(op) => match op {
            ValueOps::Alloc => Bril::Alloc([state, args[0], args[1], args[2]]),
            ValueOps::Call => Bril::Call([state, args[0], args[1], args[2]]),
            ValueOps::Load => Bril::Load([state, args[0]]),
            _ => panic!("Unexpected operation: {:?}", op),
        },
        EffectWrapper::EOp(op) => match op {
            EffectOps::Store => Bril::Store([state, args[0], args[1]]),
            EffectOps::Free => Bril::Free([state, args[0]]),
            EffectOps::Print => Bril::Print([state, args[0]]),
            EffectOps::Call => Bril::Call([state, args[0], args[1], args[2]]),
            _ => panic!("Unexpected operation: {:?}", op),
        },
    }
}

pub type EGraph = egg::EGraph<Bril, BrilAnalysis>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PointsTo {
    /// A new allocation
    Alloc(ILoc, Type),
    // /// Alias to another eclass
    // Alias(Id, Type),
    /// Alias class for all pointer parameters of the same type
    Parameter(Type),
    /// Could point to anything of the same type
    Top(Type),
    // Union(Box<PointsTo>, Box<PointsTo>),
    Union(Vec<PointsTo>),
}

impl PointsTo {
    // pub fn chase(egraph: &egg::EGraph<Bril, BrilAnalysis>, mut id: Id) -> Id {
    //     while let Some(PointsTo::Alias(new_id, _)) = &egraph[id].data.points_to {
    //         id = *new_id;
    //     }
    //     id
    // }

    // pub fn alias(egraph: &egg::EGraph<Bril, BrilAnalysis>, id: Id) -> PointsTo {
    //     PointsTo::Alias(
    //         PointsTo::chase(egraph, id),
    //         egraph[id].data.ty.clone().unwrap(),
    //     )
    // }

    pub fn may_alias(a: &PointsTo, b: &PointsTo) -> bool {
        let res = match (a, b) {
            // Refl
            (PointsTo::Alloc(i1, t1), PointsTo::Alloc(i2, t2)) => i1 == i2 && t1 == t2,
            (PointsTo::Parameter(t1), PointsTo::Parameter(t2)) => t1 == t2,
            (PointsTo::Top(t1), PointsTo::Top(t2)) => t1 == t2,
            // Alloc, Top
            (PointsTo::Alloc(_, t1), PointsTo::Top(t2)) if t1 == t2 => true,
            (PointsTo::Top(t1), PointsTo::Alloc(_, t2)) if t1 == t2 => true,
            // Param, Top
            (PointsTo::Parameter(t1), PointsTo::Top(t2)) if t1 == t2 => true,
            (PointsTo::Top(t1), PointsTo::Parameter(t2)) if t1 == t2 => true,
            // Union
            (PointsTo::Union(pts), pt) | (pt, PointsTo::Union(pts)) => {
                pts.iter().any(|pt1| PointsTo::may_alias(pt1, pt))
            }
            _ => false,
        };
        // eprintln!("may_alias({:?}, {:?}) = {}", a, b, res);
        res
    }

    pub fn join(pts: Vec<PointsTo>) -> PointsTo {
        // Flatten out any nested unions and deduplicate
        let pts: HashSet<PointsTo> = pts
            .into_iter()
            .flat_map(|pt| match pt {
                PointsTo::Union(pts) => pts,
                pt => vec![pt],
            })
            .collect();
        // If there's only one element, return it
        if pts.len() == 1 {
            return pts.into_iter().next().unwrap();
        }
        // If there's a top, return it
        if let Some(top) = pts.iter().find(|pt| matches!(pt, PointsTo::Top(_))) {
            return top.clone();
        }
        // Otherwise, return the union
        PointsTo::Union(pts.into_iter().collect())
    }

    pub fn meet(a: &mut Self, b: Self) -> Option<DidMerge> {
        match (&a, &b) {
            // Refl
            (PointsTo::Alloc(i1, t1), PointsTo::Alloc(i2, t2)) if t1 == t2 && i1 == i2 => {
                Some(DidMerge(false, false))
            }
            (PointsTo::Parameter(t1), PointsTo::Parameter(t2)) if t1 == t2 => {
                Some(DidMerge(false, false))
            }
            (PointsTo::Top(t1), PointsTo::Top(t2)) if t1 == t2 => Some(DidMerge(false, false)),
            // Alloc <: Param; Alloc <: Top
            (PointsTo::Alloc(_, t1), PointsTo::Parameter(t2) | PointsTo::Top(t2)) if t1 == t2 => {
                Some(DidMerge(false, true))
            }
            (PointsTo::Parameter(t1) | PointsTo::Top(t1), PointsTo::Alloc(_, t2)) if t1 == t2 => {
                *a = b;
                Some(DidMerge(true, false))
            }
            // Param <: Top
            (PointsTo::Parameter(t1), PointsTo::Top(t2)) if t1 == t2 => {
                Some(DidMerge(false, false))
            }
            (PointsTo::Top(t1), PointsTo::Parameter(t2)) if t1 == t2 => {
                *a = b;
                Some(DidMerge(true, false))
            }
            _ => None, // Incompatible points-to values
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct AnalysisData {
    pub ty: Option<Type>,
    pub value: Option<Literal>,
    pub points_to: Option<PointsTo>,
}

#[derive(Default)]
pub struct BrilAnalysis;

// Adapted from https://github.com/egraphs-good/egg/blob/main/tests/math.rs
impl Analysis<Bril> for BrilAnalysis {
    type Data = AnalysisData;

    fn make(egraph: &egg::EGraph<Bril, Self>, enode: &Bril) -> Self::Data {
        use Literal::*;
        let int = |i: &Id| {
            egraph[*i].data.value.as_ref().and_then(|l| {
                if let Literal::Int(i) = l {
                    Some(*i)
                } else {
                    None
                }
            })
        };
        let bool = |i: &Id| {
            egraph[*i].data.value.as_ref().and_then(|l| {
                if let Literal::Bool(b) = l {
                    Some(*b)
                } else {
                    None
                }
            })
        };
        let extract_ty = |i: &Id| {
            let Bril::Type(ty) = &egraph[*i].nodes[0] else {
                panic!("Expected type annotation")
            };
            ty.clone()
        };
        let get_ty = |i: &Id| egraph[*i].data.ty.clone();
        let value = (|| {
            Some(match enode {
                Bril::Int(i) => Int(*i),
                Bril::Bool(b) => Bool(*b),
                Bril::Add([a, b]) => Int(int(a)? + int(b)?),
                Bril::Sub([a, b]) => Int(int(a)? - int(b)?),
                Bril::Mul([a, b]) => Int(int(a)? * int(b)?),
                Bril::Div([a, b]) => Int(int(a)? / int(b)?),
                Bril::Eq([a, b]) => Bool(int(a)? == int(b)?),
                Bril::Lt([a, b]) => Bool(int(a)? < int(b)?),
                Bril::Gt([a, b]) => Bool(int(a)? > int(b)?),
                Bril::Le([a, b]) => Bool(int(a)? <= int(b)?),
                Bril::Ge([a, b]) => Bool(int(a)? >= int(b)?),
                Bril::And([a, b]) => Bool(bool(a)? && bool(b)?),
                Bril::Or([a, b]) => Bool(bool(a)? || bool(b)?),
                Bril::Not(a) => Bool(!bool(a)?),
                Bril::Id(a) => egraph[*a].data.value.clone()?,
                _ => return None,
            })
        })();
        let ty = (|| {
            Some(match enode {
                Bril::Param([_, ty]) | Bril::Phi([_, _, ty]) => extract_ty(ty),
                Bril::Int(_) => Type::Int,
                Bril::Bool(_) => Type::Bool,
                Bril::Add(_) | Bril::Sub(_) | Bril::Mul(_) | Bril::Div(_) => Type::Int,
                Bril::Eq(_) | Bril::Lt(_) | Bril::Gt(_) | Bril::Le(_) | Bril::Ge(_) => Type::Bool,
                Bril::And(_) | Bril::Or(_) | Bril::Not(_) => Type::Bool,
                Bril::Id(a) => egraph[*a].data.ty.clone()?,
                Bril::PtrAdd([ptr, _]) => egraph[*ptr].data.ty.clone()?,
                Bril::Fst(pr) => {
                    let Type::Pair(ty, _) = get_ty(pr)? else {
                        unreachable!()
                    };
                    *ty
                }
                Bril::Snd(pr) => {
                    let Type::Pair(_, ty) = get_ty(pr)? else {
                        unreachable!()
                    };
                    *ty
                }
                Bril::Alloc([_, _, _, ret_ty]) => {
                    Type::Pair(Box::new(extract_ty(ret_ty)), Box::new(Type::Unit))
                }
                Bril::Call([_, _, _, ret_ty]) => {
                    Type::Pair(Box::new(extract_ty(ret_ty)), Box::new(Type::Unit))
                }
                Bril::Load([_, ptr]) => {
                    let Type::Ptr(ty) = get_ty(ptr)? else {
                        unreachable!()
                    };
                    *ty
                }
                Bril::Store(_) => Type::Unit,
                Bril::Free(_) => Type::Unit,
                Bril::Print(_) => Type::Unit,
                Bril::List(_)
                | Bril::Bot
                // | Bril::Node(_)
                | Bril::ILoc(_)
                | Bril::Type(_)
                | Bril::Symbol(_) => return None,
            })
        })();
        let points_to = (|| {
            let extract_iloc = |i: &Id| {
                let Bril::ILoc(iloc) = &egraph[*i].nodes[0] else {
                    panic!("Expected ILoc")
                };
                *iloc
            };
            let get_pts = |i: &Id| egraph[*i].data.points_to.clone();
            Some(match enode {
                Bril::Param(_) => match &ty {
                    Some(Type::Ptr(_)) => PointsTo::Parameter(ty.clone().unwrap()),
                    _ => return None,
                },
                // TODO(altanh): analyze offsets
                Bril::PtrAdd([ptr, _]) => get_pts(ptr).clone().unwrap(),
                // Give up on pointers loaded from memory
                Bril::Load(_) => match &ty {
                    Some(Type::Ptr(_)) => PointsTo::Top(ty.clone().unwrap()),
                    _ => return None,
                },
                Bril::Alloc([_, _, iloc, ret_ty]) => {
                    PointsTo::Alloc(extract_iloc(iloc), extract_ty(ret_ty))
                }
                Bril::Call([_, _, _, ret_ty]) => match extract_ty(ret_ty) {
                    ty @ Type::Ptr(_) => PointsTo::Top(ty),
                    _ => return None,
                },
                Bril::Fst(pr) => match get_pts(pr) {
                    Some(pts) => pts,
                    _ => return None,
                },
                Bril::Id(a) => match &ty {
                    Some(Type::Ptr(_)) => get_pts(a).clone().unwrap(),
                    _ => return None,
                },
                _ => return None,
            })
        })();
        AnalysisData {
            ty,
            value,
            points_to,
        }
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> egg::DidMerge {
        merge_option(&mut a.value, b.value, |a, b| {
            assert_eq!(*a, b, "Merged non-equal constants");
            DidMerge(false, false)
        }) | merge_option(&mut a.ty, b.ty, |a, b| {
            assert_eq!(*a, b, "Merged non-equal types");
            DidMerge(false, false)
        }) | merge_option(&mut a.points_to, b.points_to, |a, b| {
            PointsTo::meet(a, b).expect("Merged incompatible pointers")
        })
    }

    fn modify(egraph: &mut egg::EGraph<Bril, Self>, id: Id) {
        let data = egraph[id].data.clone();
        if let Some(lit) = data.value {
            let added = match lit {
                Literal::Int(i) => egraph.add(Bril::Int(i)),
                Literal::Bool(b) => egraph.add(Bril::Bool(b)),
            };
            egraph.union(id, added);
            // egraph[id].nodes.retain(|n| n.is_leaf());
        }
    }
}

pub struct CostFn;
impl CostFunction<Bril> for CostFn {
    type Cost = f64;
    fn cost<C>(&mut self, enode: &Bril, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        use Bril::*;
        let op_cost = match enode {
            Int(_) | Bool(_) => 0.0,
            _ => 1.0,
        };
        enode.fold(op_cost, |acc, id| acc + costs(id))
    }
}

pub fn expr_dot<L>(expr: &RecExpr<L>, filename: impl AsRef<Path>) -> std::io::Result<()>
where
    L: Language + Display,
{
    use std::io::Write;
    let mut file = std::fs::File::create(filename)?;
    writeln!(file, "digraph G {{")?;
    for (i, node) in expr.as_ref().iter().enumerate() {
        writeln!(file, "  {} [label=\"{}\"];", i, node)?;
    }
    for (i, node) in expr.as_ref().iter().enumerate() {
        for child in node.children() {
            writeln!(file, "  {} -> {};", i, child)?;
        }
    }
    writeln!(file, "}}")?;
    Ok(())
}

pub fn arith_rules() -> Vec<Rewrite<Bril, BrilAnalysis>> {
    vec![
        // A
        rw!("add-assoc"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        rw!("mul-assoc"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
        rw!("and-assoc"; "(&& ?a (&& ?b ?c))" => "(&& (&& ?a ?b) ?c)"),
        rw!("or-assoc"; "(|| ?a (|| ?b ?c))" => "(|| (|| ?a ?b) ?c)"),
        // C
        rw!("add-commute"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rw!("mul-commute"; "(* ?a ?b)" => "(* ?b ?a)"),
        rw!("and-commute"; "(&& ?a ?b)" => "(&& ?b ?a)"),
        rw!("or-commute"; "(|| ?a ?b)" => "(|| ?b ?a)"),
        // Simplification
        rw!("add-0"; "(+ ?a 0)" => "?a"),
        rw!("mul-1"; "(* ?a 1)" => "?a"),
        rw!("mul-0"; "(* ?a 0)" => "0"),
        rw!("sub-0"; "(- ?a ?a)" => "0"),
        rw!("and-true"; "(&& ?a true)" => "?a"),
        rw!("and-false"; "(&& ?a false)" => "false"),
        rw!("or-true"; "(|| ?a true)" => "true"),
        rw!("or-false"; "(|| ?a false)" => "?a"),
        rw!("excluded-middle"; "(|| ?a (! ?a))" => "true"),
        rw!("contra"; "(&& ?a (! ?a))" => "false"),
        rw!("not-not"; "(! (! ?a))" => "?a"),
        rw!("eq-true"; "(= ?a ?a)" => "true"),
        rw!("id-elim"; "(id ?a)" => "?a"),
        rw!("le-true"; "(<= ?a ?a)" => "true"),
        rw!("ge-true"; "(>= ?a ?a)" => "true"),
        rw!("lt-false"; "(< ?a ?a)" => "false"),
        rw!("gt-false"; "(> ?a ?a)" => "false"),
    ]
}

pub fn mem_rules() -> Vec<Rewrite<Bril, BrilAnalysis>> {
    vec![
        rw!("load-store"; "(load (store ?s ?p ?v) ?p)" => "?v"),
        rw!("store-store"; "(store (store ?s ?p ?v1) ?p ?v2)" => "(store ?s ?p ?v2)"),
        rw!("ptradd-0"; "(&+ ?p 0)" => "?p"),
    ]
}

pub fn conditional_rules() -> Vec<Rewrite<Bril, BrilAnalysis>> {
    vec![
        rw!("store-comm"; "(store (store ?s ?p ?v) ?q ?w)" => "(store (store ?s ?q ?w) ?p ?v)"
        if no_alias("?p", "?q")),
    ]
}

fn no_alias(p: &'static str, q: &'static str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let p = p.parse().unwrap();
    let q = q.parse().unwrap();
    move |eg, _, subst| {
        let p = &eg[subst[p]];
        let q = &eg[subst[q]];
        let res = !PointsTo::may_alias(
            p.data.points_to.as_ref().unwrap(),
            q.data.points_to.as_ref().unwrap(),
        );
        // eprintln!("no_alias({:?}, {:?}) = {}", p.id, q.id, res);
        res
    }
}
