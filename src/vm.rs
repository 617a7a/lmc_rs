use tracing::{trace, debug, info};

use crate::{MemoryValue, MEMORY_SIZE, MemoryAddress, Instruction, addr, Memory};

pub struct VM {
    pub ram: [MemoryValue; MEMORY_SIZE],
    // Registers
    /// The accumulator is a register that stores the results of arithmetic and logical operations.
    acc: isize,
    /// The program counter is a register that stores the address of the next instruction to be executed.
    pc: MemoryAddress,
    /// The memory address register is a register that stores the address of the memory location to be accessed.
    mar: MemoryAddress,
    /// The memory data register is a register that stores the data to be written or the data just read.
    mdr: MemoryValue,
    /// The current instruction register is a register that stores the current instruction that is being executed.
    cir: Instruction,
    cycle: usize,
    halted: bool,
}

impl std::fmt::Debug for VM {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "")?;
        writeln!(f, "ACC: {:02}", self.acc)?;
        writeln!(f, "PC: {:02}", self.pc.0)?;
        writeln!(f, "MAR: {:02}", self.mar.0)?;
        writeln!(f, "MDR: {:?}", self.mdr)?;
        writeln!(f, "CIR: {:?}", self.cir)?;
        writeln!(f, "CYCLE: {:?}", self.cycle)
    }
}

pub trait VirtualMachine {
    fn new() -> Self;
    fn load_memory(&mut self, ram: Memory);
    fn execute_cycle(&mut self);
    fn fetch(&mut self);
    fn decode_execute(&mut self);
    fn is_halted(&self) -> bool;
}

impl VirtualMachine for VM {
    fn new() -> Self {
        Self {
            ram: [MemoryValue::Value(0); MEMORY_SIZE],
            acc: 0,
            pc: addr!(0),
            mar: addr!(0),
            mdr: MemoryValue::Value(0),
            cir: Instruction::HLT,
            cycle: 0,
            halted: false,
        }
    }

    fn load_memory(&mut self, ram: Memory) {
        self.ram = ram;
    }

    /// Executes a single cycle of the VM using the FDE cycle
    fn execute_cycle(&mut self) {
        self.fetch();
        self.decode_execute();
        trace!("Registers: \n{:?}", self);
    }

    fn fetch(&mut self) {
        self.cycle += 1;
        let span = tracing::span!(tracing::Level::DEBUG, "fetch", cycle = self.cycle);
        let _guard = span.enter();

        debug!("Fetching instruction at address {:?}", self.pc);
        // copy PC to MAR
        self.mar = self.pc;
        self.pc += 1;
        // fetch from memory
        self.mdr = self.ram[self.mar.0 as usize];
        self.cir = match self.mdr {
            MemoryValue::Value(_) => panic!("Fetched value from memory instead of instruction"),
            MemoryValue::Instruction(instruction) => instruction,
        };
    }

    fn decode_execute(&mut self) {
        let span = tracing::span!(tracing::Level::DEBUG, "decode_execute", cycle = self.cycle);
        let _guard = span.enter();
        debug!("Executing instruction {:?}", self.cir);
        // decode instruction
        match self.cir {
            Instruction::INP => {
                println!("Program wants INP: ");
                let mut input = String::new();
                std::io::stdin()
                    .read_line(&mut input)
                    .expect("Failed to read line");
                let input = input
                    .trim()
                    .parse::<isize>()
                    .expect("Failed to parse input");

                self.acc = input;
            }
            Instruction::OUT => {
                // print accumulator to stdout
                info!("OUT: {}", self.acc);
            }
            Instruction::LDA(address) => {
                self.acc = match self.ram[address.0 as usize] {
                    MemoryValue::Value(value) => value,
                    MemoryValue::Instruction(_) => panic!("LDA address points to instruction"),
                };
            }
            Instruction::STA(address) => {
                self.ram[address.0 as usize] = MemoryValue::Value(self.acc);
            }
            Instruction::ADD(address) => {
                self.acc += match self.ram[address.0 as usize] {
                    MemoryValue::Value(value) => value,
                    MemoryValue::Instruction(_) => panic!("ADD address points to instruction"),
                };
            }
            Instruction::SUB(address) => {
                self.acc -= match self.ram[address.0 as usize] {
                    MemoryValue::Value(value) => value,
                    MemoryValue::Instruction(_) => panic!("SUB address points to instruction"),
                };
            }
            Instruction::BRP(address) => {
                if self.acc >= 0 {
                    self.pc = address;
                }
            }
            Instruction::BRZ(address) => {
                if self.acc == 0 {
                    self.pc = address;
                }
            }
            Instruction::BRA(address) => {
                self.pc = address;
            }
            Instruction::HLT => {
                self.halted = true;
            }
        }
    }

    fn is_halted(&self) -> bool {
        self.halted
    }
}