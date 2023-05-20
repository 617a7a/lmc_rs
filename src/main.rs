// LMC VM (interpreter) in Rust

use tracing::{debug, info};

const MEMORY_SIZE: usize = 100;

#[repr(u16)]
#[derive(Clone, Copy, PartialEq, Eq)]
enum Instruction {
    /// INPUT: Retrieve user input and stores it in the accumulator. 901
    INP = 901,
    /// OUTPUT: Output the value stored in the accumulator. 902
    OUT = 902,
    /// LOAD: Load the Accumulator with the contents of the memory address given. 5xx
    LDA(MemoryAddress) = 5,
    /// STORE: Store the value in the Accumulator in the memory address given. 3xx
    STA(MemoryAddress) = 3,
    /// ADD: Add the contents of the memory address to the Accumulator 1xx
    ADD(MemoryAddress) = 1,
    /// SUBTRACT: Subtract the contents of the memory address from the Accumulator 2xx
    SUB(MemoryAddress) = 2,
    /// BRANCH IF POSITIVE: Branch/Jump to the address given if the Accumulator is zero or positive. 8xx
    BRP(MemoryAddress) = 8,
    /// BRANCH IF ZERO: Branch/Jump to the address given if the Accumulator is zero. 7xx
    BRZ(MemoryAddress) = 7,
    /// BRANCH ALWAYS: Branch/Jump to the address given. 6xx
    BRA(MemoryAddress) = 6,
    /// HALT: Stop the code 0
    HLT = 0,
}

impl std::fmt::Debug for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Instruction::INP => write!(f, "INP [901]"),
            Instruction::OUT => write!(f, "OUT [902]"),
            Instruction::LDA(address) => write!(f, "LDA {address:?} [5{address:?}]"),
            Instruction::STA(address) => write!(f, "STA {address:?} [3{address:?}]"),
            Instruction::ADD(address) => write!(f, "ADD {address:?} [1{address:?}]"),
            Instruction::SUB(address) => write!(f, "SUB {address:?} [2{address:?}]"),
            Instruction::BRP(address) => write!(f, "BRP {address:?} [8{address:?}]"),
            Instruction::BRZ(address) => write!(f, "BRZ {address:?} [7{address:?}]"),
            Instruction::BRA(address) => write!(f, "BRA {address:?} [6{address:?}]"),
            Instruction::HLT => write!(f, "HLT (0)"),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum MemoryValue {
    Value(isize),
    Instruction(Instruction),
}

// we'll deal with DAT separately as it doesn't have an opcode, but just defines a memory address

#[derive(Clone, Copy, PartialEq, Eq)]
struct MemoryAddress(usize);

impl MemoryAddress {
    fn new(address: usize) -> Result<Self, Error> {
        if address > (MEMORY_SIZE-1) {
            Err(Error::InvalidMemoryAddress)
        } else {
            Ok(Self(address))
        }
    }

    fn increment(&mut self) {
        if self.0 == (MEMORY_SIZE-1) {
            self.0 = 0;
        } else {
            self.0 += 1;
        }
    }
}

impl std::fmt::Debug for MemoryAddress {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:02}", self.0)
    }
}

macro_rules! addr {
    ($addr:expr) => {
        MemoryAddress::new($addr).unwrap()
    };
}

type Memory = [MemoryValue; MEMORY_SIZE];

struct VM {
    ram: [MemoryValue; MEMORY_SIZE],
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
}

impl VM {
    fn new() -> Self {
        Self {
            ram: [MemoryValue::Value(0); MEMORY_SIZE],
            acc: 0,
            pc: addr!(0),
            mar: addr!(0),
            mdr: MemoryValue::Value(0),
            cir: Instruction::HLT,
        }
    }

    fn load_memory(&mut self, ram: Memory) {
        self.ram = ram;
        debug!("Loaded memory {:?} into VM", ram);
    }

    /// Executes a single cycle of the VM using the FDE cycle
    fn execute_cycle(&mut self) {
        self.fetch();
        self.decode_execute();
    }

    fn fetch(&mut self) {
        let span = tracing::span!(tracing::Level::DEBUG, "fetch");
        let _guard = span.enter();

        debug!("Fetching instruction at address {:?}", self.pc);
        // copy PC to MAR
        self.mar = self.pc;
        self.pc.increment();
        // fetch from memory
        self.mdr = self.ram[self.mar.0 as usize];
        debug!("Fetched MemoryValue {:?}", self.mdr);
        self.cir = match self.mdr {
            MemoryValue::Value(_) => unreachable!(),
            MemoryValue::Instruction(instruction) => instruction,
        };
    }

    fn decode_execute(&mut self) {
        let span = tracing::span!(tracing::Level::DEBUG, "decode_execute");
        let _guard = span.enter();
        debug!("Executing instruction {:?}", self.cir);
        // decode instruction
        match self.cir {
            Instruction::INP => {
                info!("INP: ");
                // read input from stdin
                let mut input = String::new();
                std::io::stdin()
                    .read_line(&mut input)
                    .expect("Failed to read line");
                // parse input as u8
                let input = input
                    .trim()
                    .parse::<isize>()
                    .expect("Failed to parse input");
                // store input in accumulator
                self.acc = input;
            }
            Instruction::OUT => {
                // print accumulator to stdout
                info!("OUT: {}", self.acc);
            }
            Instruction::LDA(address) => {
                // copy value at address to accumulator
                self.acc = match self.ram[address.0 as usize] {
                    MemoryValue::Value(value) => value,
                    MemoryValue::Instruction(_) => 0,
                };
            }
            Instruction::STA(address) => {
                // copy accumulator to address
                self.ram[address.0 as usize] = MemoryValue::Value(self.acc);
            }
            Instruction::ADD(address) => {
                // add value at address to accumulator
                self.acc += match self.ram[address.0 as usize] {
                    MemoryValue::Value(value) => value,
                    MemoryValue::Instruction(_) => 0,
                };
            }
            Instruction::SUB(address) => {
                // subtract value at address from accumulator
                self.acc -= match self.ram[address.0 as usize] {
                    MemoryValue::Value(value) => value,
                    MemoryValue::Instruction(_) => 0,
                };
            }
            Instruction::BRP(address) => {
                // branch to address if accumulator is positive
                if self.acc >= 0 {
                    self.pc = address;
                }
            }
            Instruction::BRZ(address) => {
                // branch to address if accumulator is zero
                if self.acc == 0 {
                    self.pc = address;
                }
            }
            Instruction::BRA(address) => {
                // branch to address
                self.pc = address;
            }
            Instruction::HLT => {
                // stop the program
                std::process::exit(0);
            }
        }
    }
}

fn main() {
    tracing_subscriber::fmt::init();
    // read the LMC assembly from the file given as the first argument
    let args: Vec<String> = std::env::args().collect();
    let filename = &args[1];

    let mut vm = VM::new();

    // read the file
    let contents =
        std::fs::read_to_string(filename).expect("Something went wrong reading the file");

    vm.load_memory(parse_program(contents).unwrap());

    loop {
        vm.execute_cycle();
    }
}

#[derive(Debug)]
enum Error {
    InvalidInstruction(usize),
    InvalidMemoryAddress,
    InvalidValue,
}

fn parse_program(code: String) -> Result<Memory, Error> {
    let mut ram: Memory = [MemoryValue::Value(0); MEMORY_SIZE];

    debug!("Parsing program: {:?}", code.replace("\n", ", "));

    // split the file into lines
    let lines = code
        .split("\n")
        .map(|line| line.trim())
        .filter(|line| !line.is_empty());

    debug!("Read {:?} lines", lines.clone().count());

    // split lines into DAT and non-DAT lines
    let (dat_lines, lines): (Vec<&str>, Vec<&str>) = lines.partition(|line| line.find("DAT").is_some());

    let mut lines: Vec<String> = lines.iter().map(|line| line.to_string()).collect();

    // allocate memory address for each DAT line and store the value if given
    // then replace the identifier in lines with the memory address
    for (i, line) in dat_lines.iter().enumerate() {
        let line = line.trim_start_matches("DAT");
        let split_line: Vec<&str> = line.split_whitespace().collect();

        let value = if split_line.len() == 3 {
            split_line[2]
                .parse::<isize>()
                .map_err(|_| Error::InvalidValue)?
        } else {
            0
        };

        let address = i + lines.len();
        ram[address] = MemoryValue::Value(value);
        lines = lines
            .iter()
            .map(|line| line.replace(split_line[0], &address.to_string()))
            .collect();
    }

    // read each line and parse it into an instruction using its index as the memory address
    for (i, line) in lines.iter().enumerate() {
        let line = line.trim();
        let mut parts = line.split_whitespace();

        let instruction_str = match parts.next() {
            Some(instruction) => instruction,
            None => return Err(Error::InvalidInstruction(i)),
        };

        let mut next_part = || {
            Ok(match parts.next() {
                Some(part) => match part.parse::<usize>() {
                    Ok(part) => addr!(part),
                    Err(_) => return Err(Error::InvalidValue),
                },
                None => return Err(Error::InvalidInstruction(i)),
            })
        };

        let instruction = match instruction_str {
            "INP" => Instruction::INP,
            "OUT" => Instruction::OUT,
            "LDA" => Instruction::LDA(next_part()?),
            "STA" => Instruction::STA(next_part()?),
            "ADD" => Instruction::ADD(next_part()?),
            "SUB" => Instruction::SUB(next_part()?),
            "BRP" => Instruction::BRP(next_part()?),
            "BRZ" => Instruction::BRZ(next_part()?),
            "BRA" => Instruction::BRA(next_part()?),
            "HLT" => Instruction::HLT,
            _ => return Err(Error::InvalidInstruction(i)),
        };
        ram[i] = MemoryValue::Instruction(instruction);
    }

    Ok(ram)
}

#[cfg(test)]
mod tests {
    use super::*;
    
    fn test_parse_program(program: &str, wanted: &[MemoryValue]) {
        let ram = parse_program(program.to_string()).unwrap();

        assert_eq!(ram[..wanted.len()], *wanted);
    }

    #[test]
    fn test_parse_program_simple() {
        test_parse_program(
            "INP\nOUT\nHLT",
            &[
                MemoryValue::Instruction(Instruction::INP),
                MemoryValue::Instruction(Instruction::OUT),
                MemoryValue::Instruction(Instruction::HLT),
            ],
        );

        test_parse_program(
            "INP\nSTA num1\nINP\nADD num1\nOUT\nHLT\nnum1 DAT",
            &[
                MemoryValue::Instruction(Instruction::INP),
                MemoryValue::Instruction(Instruction::STA(addr!(6))),
                MemoryValue::Instruction(Instruction::INP),
                MemoryValue::Instruction(Instruction::ADD(addr!(6))),
                MemoryValue::Instruction(Instruction::OUT),
                MemoryValue::Instruction(Instruction::HLT),
                MemoryValue::Value(0),
            ],
        );
    }
}
