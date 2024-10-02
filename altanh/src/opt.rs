use std::collections::HashSet;

use crate::monotone::{conditional_constant, observable_variables, ConstantLattice};
use bril_rs::{Code, ConstOps, EffectOps, Function, Instruction, Literal, Type};

/// Program optimizations

/// Dead code elimination.
/// - Removes instructions that are not used.
pub fn dce(func: &Function) -> Function {
    let cfg = crate::cfg::ControlFlowGraph::new(func);
    let ov_analysis = observable_variables(func);
    let mut new_instrs = vec![];
    for (i, instr) in func.instrs.iter().enumerate() {
        use Instruction::*;
        match instr {
            Code::Instruction(Constant { dest, .. }) | Code::Instruction(Value { dest, .. }) => {
                // If any successors use this instruction, keep it
                if cfg.flow[&i.into()]
                    .iter()
                    .any(|n| ov_analysis[n].contains(dest))
                {
                    new_instrs.push(instr.clone());
                }
            }
            _ => new_instrs.push(instr.clone()),
        }
    }
    if new_instrs.is_empty() {
        new_instrs.push(Code::Instruction(Instruction::Effect {
            args: vec![],
            funcs: vec![],
            labels: vec![],
            op: EffectOps::Nop,
        }));
    }
    Function {
        name: func.name.clone(),
        args: func.args.clone(),
        instrs: new_instrs,
        return_type: func.return_type.clone(),
    }
}

/// Condtional constant propagation.
pub fn cc(func: &Function) -> Function {
    let cc_results = conditional_constant(func);
    let mut new_instrs: Vec<Code> = vec![];
    for (i, code) in func.instrs.iter().enumerate() {
        // if let Some((env, r)) = cc_results.get(&i.into()) {
        if let Code::Instruction(instr) = code {
            let (env, r) = &cc_results[&i.into()];
            // if i is dead, skip
            if !r.contains(&i.into()) {
                continue;
            }
            use bril_rs::Instruction::*;
            match instr.clone() {
                Value { dest, .. } => {
                    // If dest is concrete, replace with constant
                    match env.get(&dest) {
                        Some(ConstantLattice::Int(z)) => {
                            new_instrs.push(Code::Instruction(Constant {
                                dest: dest.clone(),
                                op: ConstOps::Const,
                                const_type: Type::Int,
                                value: Literal::Int(*z),
                            }));
                        }
                        Some(ConstantLattice::Bool(b)) => {
                            new_instrs.push(Code::Instruction(Constant {
                                dest: dest.clone(),
                                op: ConstOps::Const,
                                const_type: Type::Bool,
                                value: Literal::Bool(*b),
                            }));
                        }
                        _ => {
                            new_instrs.push(Code::Instruction(instr.clone()));
                        }
                    }
                }
                Effect {
                    args,
                    labels,
                    op: EffectOps::Branch,
                    ..
                } => {
                    match env.get(&args[0]) {
                        Some(ConstantLattice::Bool(true)) => {
                            // Jump directly to true branch
                            new_instrs.push(Code::Instruction(Effect {
                                args: vec![],
                                funcs: vec![],
                                labels: vec![labels[0].clone()],
                                op: EffectOps::Jump,
                            }));
                        }
                        Some(ConstantLattice::Bool(false)) => {
                            // Jump directly to false branch
                            new_instrs.push(Code::Instruction(Effect {
                                args: vec![],
                                funcs: vec![],
                                labels: vec![labels[1].clone()],
                                op: EffectOps::Jump,
                            }));
                        }
                        _ => {
                            // Do nothing
                            new_instrs.push(Code::Instruction(instr.clone()));
                        }
                    }
                }
                instr => new_instrs.push(Code::Instruction(instr)),
            }
        } else {
            // Label
            new_instrs.push(code.clone());
        }
    }
    Function {
        name: func.name.clone(),
        args: func.args.clone(),
        instrs: new_instrs,
        return_type: func.return_type.clone(),
    }
}
