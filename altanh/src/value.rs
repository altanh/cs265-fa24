use std::{fmt::Display, ops::DerefMut, str::FromStr};

use bril_rs::{Argument, EffectOps, Literal, ValueOps};
use egg::{define_language, rewrite as rw, Id, Rewrite, Symbol};

use crate::cfg::Node;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ILoc(Node, usize);
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
        let node = parts.next().unwrap().parse().unwrap();
        let index = parts.next().unwrap().parse().unwrap();
        Ok(ILoc(node, index))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Effect {
    Call(String),
    Print,
    Store,
    Free,
    Load,
    Alloc,
}

// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
// pub enum Value {
//     Bot,
//     Const(Literal),
//     Param(Argument),
//     Phi(Vec<String>, Loc),
//     Op(ValueOps, Vec<Id>),
//     Effect(Effect, Vec<Id>),
// }

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Type {
    Int,
    Bool,
    Ptr(Box<Type>),
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
            Type::Int => write!(f, "int"),
            Type::Bool => write!(f, "bool"),
            Type::Ptr(t) => write!(f, "ptr<{}>", t),
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
        } else if s.starts_with("ptr<") && s.ends_with('>') {
            Ok(Type::Ptr(Box::new(s[4..s.len() - 1].parse().unwrap())))
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
        Node(Node),
        String(String),

        // Type annotation for function parameters
        Type(Type),
        "param" = Param([Id; 2]),

        // Variadic wrapper
        "list" = List(Vec<Id>),

        // (phi (list x y z) (block:0))
        "phi" = Phi([Id; 2]),

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

        // Effectful operations: they have a state argument
        "alloc" = Alloc([Id; 2]),  //    (alloc state size): S -> N -> (P X, S)
        "call" = Call([Id; 3]),    // (call state fun args): S -> F -> X -> (Y, S)
        "load" = Load([Id; 2]),    //      (load state ptr): S -> P X -> X
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
            ValueOps::Alloc => Bril::Alloc([state, args[0]]),
            ValueOps::Call => Bril::Call([state, args[0], args[1]]),
            ValueOps::Load => Bril::Load([state, args[0]]),
            _ => panic!("Unexpected operation: {:?}", op),
        },
        EffectWrapper::EOp(op) => match op {
            EffectOps::Store => Bril::Store([state, args[0], args[1]]),
            EffectOps::Free => Bril::Free([state, args[0]]),
            EffectOps::Print => Bril::Print([state, args[0]]),
            EffectOps::Call => Bril::Call([state, args[0], args[1]]),
            _ => panic!("Unexpected operation: {:?}", op),
        },
    }
}

pub fn rules() -> Vec<Rewrite<Bril, ()>> {
    vec![
        rw!("add-commute"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rw!("mul-commute"; "(* ?a ?b)" => "(* ?b ?a)"),
        rw!("and-commute"; "(&& ?a ?b)" => "(&& ?b ?a)"),
        rw!("or-commute"; "(|| ?a ?b)" => "(|| ?b ?a)"),
        rw!("add-0"; "(+ ?a 0)" => "?a"),
        rw!("mul-1"; "(* ?a 1)" => "?a"),
        rw!("mul-0"; "(* ?a 0)" => "0"),
        rw!("and-true"; "(&& ?a true)" => "?a"),
        rw!("and-false"; "(&& ?a false)" => "false"),
        rw!("or-true"; "(|| ?a true)" => "true"),
        rw!("or-false"; "(|| ?a false)" => "?a"),
        rw!("not-not"; "(! (! ?a))" => "?a"),
        rw!("eq-true"; "(= ?a ?a)" => "true"),
        rw!("id-elim"; "(id ?a)" => "?a"),
    ]
}
