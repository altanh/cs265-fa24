/// Program optimizations
use crate::cfg::{Block, Node, CFG};
use crate::monotone::{
    ConditionalConstant, ConstantLattice, MonotoneAnalysis, ObservableVariables,
};
use bril_rs::{Code, ConstOps, EffectOps, Function, Instruction, Literal, Type};

/// Dead code elimination.
pub fn dce(func: &Function) -> Function {
    let cfg = CFG::new(func);
    let analysis = ObservableVariables.run(&cfg);
    let mut new_insts = vec![];
    for (i, block) in cfg.blocks.iter().enumerate() {
        let loc: Node = i.into();
        let mut value_in = analysis.value_in[&loc].clone();
        let mut block_insts = vec![];
        // NB: reverse order
        ObservableVariables.for_each_before(block, loc, &mut value_in, |inst, xs| match inst {
            Instruction::Constant { dest, .. } | Instruction::Value { dest, .. } => {
                if xs.contains(dest) {
                    block_insts.push(inst.clone());
                }
            }
            _ => block_insts.push(inst.clone()),
        });
        block_insts.reverse();
        let term = block_insts.pop();
        Block {
            insts: block_insts,
            term,
            label: block.label.clone(),
        }
        .emit(&mut new_insts);
    }
    if new_insts.is_empty() {
        new_insts.push(Code::Instruction(Instruction::Effect {
            args: vec![],
            funcs: vec![],
            labels: vec![],
            op: EffectOps::Nop,
        }));
    }
    Function {
        name: func.name.clone(),
        args: func.args.clone(),
        instrs: new_insts,
        return_type: func.return_type.clone(),
    }
}

/// Conditional constant propagation.
pub fn cc(func: &Function) -> Function {
    let cfg = CFG::new(func);
    let analysis = ConditionalConstant { cfg: &cfg };
    let results = analysis.run(&cfg);
    let mut new_insts = vec![];
    for (i, block) in cfg.blocks.iter().enumerate() {
        let loc: Node = i.into();
        let mut value_in = results.value_in[&loc].clone();
        if !value_in.1.contains(&loc) {
            continue;
        }
        let mut block_insts = vec![];
        analysis.for_each_after(block, loc, &mut value_in, |inst, (env, _)| {
            use Instruction::*;
            match inst {
                Value { dest, .. } => match env.get(dest) {
                    Some(ConstantLattice::Int(z)) => {
                        block_insts.push(Constant {
                            dest: dest.clone(),
                            op: ConstOps::Const,
                            const_type: Type::Int,
                            value: Literal::Int(*z),
                        });
                    }
                    Some(ConstantLattice::Bool(b)) => {
                        block_insts.push(Constant {
                            dest: dest.clone(),
                            op: ConstOps::Const,
                            const_type: Type::Bool,
                            value: Literal::Bool(*b),
                        });
                    }
                    _ => {
                        block_insts.push(inst.clone());
                    }
                },
                Effect {
                    args,
                    labels,
                    op: EffectOps::Branch,
                    ..
                } => {
                    match env.get(&args[0]) {
                        Some(ConstantLattice::Bool(true)) => {
                            // Jump directly to true branch
                            block_insts.push(Effect {
                                args: vec![],
                                funcs: vec![],
                                labels: vec![labels[0].clone()],
                                op: EffectOps::Jump,
                            });
                        }
                        Some(ConstantLattice::Bool(false)) => {
                            // Jump directly to false branch
                            block_insts.push(Effect {
                                args: vec![],
                                funcs: vec![],
                                labels: vec![labels[1].clone()],
                                op: EffectOps::Jump,
                            });
                        }
                        _ => {
                            // Do nothing
                            block_insts.push(inst.clone());
                        }
                    }
                }
                _ => block_insts.push(inst.clone()),
            }
        });
        let term = block_insts.pop();
        Block {
            insts: block_insts,
            term,
            label: block.label.clone(),
        }
        .emit(&mut new_insts);
    }
    Function {
        name: func.name.clone(),
        args: func.args.clone(),
        instrs: new_insts,
        return_type: func.return_type.clone(),
    }
}
