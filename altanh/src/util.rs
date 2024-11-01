use std::{
    cmp::min,
    collections::{HashMap, HashSet},
    hash::Hash,
};

use bril_rs::*;

pub type UFNode = u32;

pub struct UnionFind {
    nodes: Vec<UFNode>,
}

// TODO(altanh): path compression if it matters
impl UnionFind {
    pub fn new() -> UnionFind {
        UnionFind { nodes: vec![] }
    }

    pub fn make_node(&mut self) -> UFNode {
        let r = self.nodes.len() as UFNode;
        self.nodes.push(r);
        r
    }

    pub fn root(&self, mut n: UFNode) -> UFNode {
        assert!(n < self.nodes.len() as UFNode);
        while self.nodes[n as usize] != n {
            n = self.nodes[n as usize];
        }
        n
    }

    pub fn merge(&mut self, x: UFNode, y: UFNode) -> UFNode {
        let x = self.root(x);
        let y = self.root(y);
        let r = if x < y {
            self.nodes[y as usize] = x;
            x
        } else if y < x {
            self.nodes[x as usize] = y;
            y
        } else {
            // Already merged
            x
        };
        r
    }

    pub fn equiv(&self, x: UFNode, y: UFNode) -> bool {
        self.root(x) == self.root(y)
    }
}

pub fn op_type(op: &ValueOps) -> Option<Type> {
    use ValueOps::*;
    match op {
        Add | Sub | Mul | Div => Some(Type::Int),
        And | Or | Not | Le | Lt | Ge | Gt | Eq => Some(Type::Bool),
        Call | Id | Alloc | Load | PtrAdd | Phi => None,
    }
}

pub fn op_arity(op: &ValueOps) -> Option<usize> {
    use ValueOps::*;
    match op {
        Not | Id | Alloc | Load => Some(1),
        Add | Sub | Mul | Div | And | Or | Le | Lt | Ge | Gt | Eq | PtrAdd => Some(2),
        Call | Phi => None,
    }
}

pub fn is_commutative(op: &ValueOps) -> bool {
    use ValueOps::*;
    match op {
        Add | Mul | And | Or | Eq => true,
        _ => false,
    }
}

pub fn is_effectful(op: &ValueOps) -> bool {
    use ValueOps::*;
    match op {
        Call | Load | Alloc => true,
        _ => false,
    }
}

pub fn complete_adj<V>(adj: &mut HashMap<V, HashSet<V>>)
where
    V: Eq + Hash + Clone,
{
    let us: Vec<V> = adj.values().flatten().cloned().collect();
    for u in us {
        if let None = adj.get(&u) {
            adj.insert(u, HashSet::new());
        }
    }
}

/// `v` in `adj[u]` means `(u, v)` is an edge in the graph.
/// Returns `(R, C)` where `R` is the residual DAG formed by contracting all SCCs
/// to a single node (the "representative"), and `C` maps SCC representatives to
/// the nodes in the SCC.
pub fn scc<V>(adj: &HashMap<V, HashSet<V>>) -> (HashMap<V, HashSet<V>>, HashMap<V, HashSet<V>>)
where
    V: Eq + Hash + Clone,
{
    fn sc<V>(
        v: &V,
        adj: &HashMap<V, HashSet<V>>,
        index: &mut usize,
        stack: &mut Vec<V>,
        v2i: &mut HashMap<V, usize>,
        v2ll: &mut HashMap<V, usize>,
        vs: &mut HashSet<V>,
        res: &mut HashMap<V, HashSet<V>>,
    ) where
        V: Eq + Hash + Clone,
    {
        v2i.insert(v.clone(), *index);
        v2ll.insert(v.clone(), *index);
        *index += 1;
        stack.push(v.clone());
        vs.insert(v.clone());
        for w in &adj[v] {
            if let None = v2i.get(w) {
                sc(w, adj, index, stack, v2i, v2ll, vs, res);
            } else if vs.contains(w) {
                v2ll.insert(v.clone(), min(v2ll[v], v2i[w]));
            }
        }
        if v2ll[v] == v2i[v] {
            let mut component: HashSet<V> = HashSet::new();
            loop {
                let w = stack.pop().unwrap();
                vs.remove(&w);
                component.insert(w.clone());
                if w == *v {
                    break;
                }
            }
            res.insert(v.clone(), component);
        }
    }

    let mut index = 0;
    let mut stack: Vec<V> = vec![];
    let mut v2i: HashMap<V, usize> = HashMap::new();
    let mut v2ll: HashMap<V, usize> = HashMap::new();
    let mut vs: HashSet<V> = HashSet::new();
    let mut res: HashMap<V, HashSet<V>> = HashMap::new();

    for v in adj.keys() {
        if let None = v2i.get(v) {
            sc(
                v, adj, &mut index, &mut stack, &mut v2i, &mut v2ll, &mut vs, &mut res,
            );
        }
    }

    // Compute SCC DAG
    let res_nodes: HashSet<V> = res.keys().cloned().collect();
    let mut res_adj: HashMap<V, HashSet<V>> = HashMap::new();
    for (v, us) in adj {
        if !res_nodes.contains(v) {
            continue;
        }
        for u in us {
            if !res_nodes.contains(u) || *u == *v {
                continue;
            }
            res_adj.entry(v.clone()).or_default().insert(u.clone());
        }
    }
    complete_adj(&mut res_adj);
    (res_adj, res)
}

pub fn topological_order<V>(adj: &HashMap<V, HashSet<V>>) -> Vec<V>
where
    V: Eq + Hash + Clone,
{
    let mut perm: HashSet<V> = Default::default();
    let mut remaining: HashSet<V> = adj.keys().cloned().collect();
    let mut temp: HashSet<V> = Default::default();
    let mut result: Vec<V> = Default::default();

    fn visit<V>(
        n: &V,
        adj: &HashMap<V, HashSet<V>>,
        perm: &mut HashSet<V>,
        temp: &mut HashSet<V>,
        remaining: &mut HashSet<V>,
        result: &mut Vec<V>,
    ) where
        V: Eq + Hash + Clone,
    {
        if perm.contains(n) {
            return;
        }
        if temp.contains(n) {
            panic!("cycle in DAG!");
        }
        temp.insert(n.clone());
        for m in &adj[n] {
            visit(m, adj, perm, temp, remaining, result);
        }
        perm.insert(n.clone());
        remaining.remove(n);
        result.push(n.clone());
    }

    while !remaining.is_empty() {
        let n = remaining.iter().next().cloned().unwrap();
        visit(&n, adj, &mut perm, &mut temp, &mut remaining, &mut result);
    }

    result.reverse();
    result
}
