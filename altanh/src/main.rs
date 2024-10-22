use altanh::cfg::CFG;
use bril_rs::load_program;

const WRITE_CFG: bool = false;

fn main() {
    let prog = load_program();

    let mut new_funcs = vec![];

    // Parse the pass sequence: ./altanh <pass1> <pass2> ...
    let passes: Vec<String> = std::env::args().skip(1).collect();

    for func in &prog.functions {
        eprintln!("Optimizing {}...", &func.name);
        let cfg = CFG::new(func);

        if WRITE_CFG {
            // open file for writing using the function name
            let mut file = std::fs::File::create(format!("dot/{}.dot", func.name)).unwrap();
            // write the graph to the file
            cfg.dot(&mut file).unwrap();
        }

        let mut func = func.clone();
        for pass in &passes {
            match pass.as_str() {
                "cc" => {
                    eprintln!("-- Running CC...");
                    func = altanh::opt::cc(&func);
                }
                "dce" => {
                    eprintln!("-- Running DCE...");
                    func = altanh::opt::dce(&func);
                }
                "giga" => {
                    eprintln!("-- Running gigapass...");
                    func = altanh::ssa::gvn_gcm_cc_dce(&func);
                }
                _ => {
                    eprintln!("Unknown pass: {}", pass);
                    std::process::exit(1);
                }
            }
        }

        if WRITE_CFG {
            let cfg = CFG::new(&func);
            // open file for writing using the function name
            let mut file = std::fs::File::create(format!("dot/{}_opt.dot", &func.name)).unwrap();
            // write the graph to the file
            cfg.dot(&mut file).unwrap();
        }

        new_funcs.push(func);
    }

    // print the optimized program
    let new_prog = bril_rs::Program {
        functions: new_funcs,
    };
    bril_rs::output_program(&new_prog);
}
