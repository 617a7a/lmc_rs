use lmc_rs::{VM, VirtualMachine, parse_program};
use tracing::{debug, info};

fn main() {
    tracing_subscriber::fmt::init();

    let filenames: Vec<String> = std::env::args().skip(1).collect();

    for filename in filenames {
        let mut vm = VM::new();
    
        debug!("Reading file {}", filename);
        let contents =
            std::fs::read_to_string(&filename).expect("Something went wrong reading the file");
        debug!("Read file contents");

        debug!("Parsing program into memory");
        vm.load_memory(parse_program(contents).unwrap());
        debug!("Loaded program into memory");
    
        debug!("Executing program");
        while !vm.is_halted() {
            vm.execute_cycle();
        }
        info!("Program {filename} complete");
    }
}
