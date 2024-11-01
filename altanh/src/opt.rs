/// Program optimizations
use crate::{cfg::CFG, ssa::gvn_gcm_cc_dce};
use bril_rs::Function;

/// Loop rotation: while C { B } => if C { do { B } while C }.
/// This enables LICM via the giga pass.
pub fn rotate_loops(func: &Function) -> Function {
    let mut cfg = CFG::new(func);
    cfg.rotate_loops();
    cfg.emit()
}

pub fn giga(func: &Function) -> Function {
    gvn_gcm_cc_dce(func)
}
