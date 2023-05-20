// LMC VM (interpreter) in Rust

use tracing::{debug, info, trace};

const MEMORY_SIZE: usize = 100;

#[repr(usize)]
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
        if address > (MEMORY_SIZE - 1) {
            Err(Error::InvalidMemoryAddress)
        } else {
            Ok(Self(address))
        }
    }

    fn increment(&mut self) {
        if self.0 == (MEMORY_SIZE - 1) {
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

impl VM {
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
        self.pc.increment();
        // fetch from memory
        self.mdr = self.ram[self.mar.0 as usize];
        self.cir = match self.mdr {
            MemoryValue::Value(_) => unreachable!(),
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
                self.halted = true;
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

    debug!("Reading file {}", filename);
    let contents =
        std::fs::read_to_string(filename).expect("Something went wrong reading the file");
    debug!("Read file contents: \n{}", contents);
    debug!("Parsing program into memory");
    vm.load_memory(parse_program(contents).unwrap());
    debug!("Loaded program into memory");

    debug!("Executing program");
    while !vm.halted {
        vm.execute_cycle();
    }
    debug!("Program execution complete");
}

#[derive(Debug, PartialEq)]
enum Error {
    InvalidInstruction(usize),
    InvalidMemoryAddress,
    InvalidValue,
}

#[derive(Clone)]
struct Line {
    /// An optional text symbol that can be used to reference this line/memory address
    symbol: Option<String>,
    /// The instruction to be executed as a string
    instruction_string: String,
}

impl std::fmt::Debug for Line {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(symbol) = &self.symbol {
            write!(f, "{} {}", symbol, self.instruction_string)
        } else {
            write!(f, "{}", self.instruction_string)
        }
    }
}

fn parse_program(code: String) -> Result<Memory, Error> {
    let span = tracing::span!(tracing::Level::DEBUG, "parse_program");
    let _guard = span.enter();

    let mut ram: Memory = [MemoryValue::Value(0); MEMORY_SIZE];

    // split the file into lines
    let lines = code
        .split("\n")
        // .filter(|line| !line.starts_with("//"))
        .map(|line| clean_line(line.trim()))
        .filter(|line| !line.is_empty())
        .map(|line| {
            // map into Line structs
            let mut split_line = line.split_whitespace();
            let first = split_line.next().unwrap();

            let has_symbol = !matches!(
                first,
                "INP" | "OUT" | "LDA" | "STA" | "ADD" | "SUB" | "BRP" | "BRZ" | "BRA" | "HLT"
            );

            let symbol = if has_symbol {
                Some(first.to_string())
            } else {
                None
            };

            let instruction_string = if has_symbol {
                split_line.collect::<Vec<&str>>().join(" ")
            } else {
                line
            };

            Line {
                symbol,
                instruction_string,
            }
        });

    // split lines into DAT and non-DAT lines
    let (dat_lines, mut lines): (Vec<Line>, Vec<Line>) =
        lines.partition(|line| line.instruction_string.contains("DAT"));

    debug!("Recognised {} DAT lines", dat_lines.len());
    debug!("Recognised {} instructions", lines.len());

    fn replace_symbol_with_address(lines: &mut Vec<Line>, symbol: &str, address: usize) {
        let str_address = format!("{}", address);
        for line in lines {
            // only replace WHOLE words, not substrings
            let instruction_string = line.instruction_string.clone();
            line.instruction_string = instruction_string.split_whitespace().map(|word| {
                if word == symbol {
                    str_address.clone()
                } else {
                    word.to_string()
                }
            }).collect::<Vec<String>>().join(" ");
        }
    }

    // allocate memory address for each DAT line and store the value if given
    // then replace the identifier in lines with the memory address
    for (i, line) in dat_lines.iter().enumerate() {
        let split_line: Vec<&str> = line.instruction_string.split_whitespace().collect();

        let symbol = line
            .symbol
            .clone()
            .expect(format!("Invalid DAT line: {:?}", line).as_str());

        let value = match split_line.get(1) {
            Some(value) => match value.parse::<isize>() {
                Ok(value) => value,
                Err(_) => return Err(Error::InvalidValue),
            },
            None => 0,
        };

        let address = i + lines.len();

        // initialize memory address with given value
        ram[address] = MemoryValue::Value(value);

        replace_symbol_with_address(&mut lines, &symbol, address);
    }

    let marked_lines: Vec<(usize, Line)> = lines
        .clone()
        .iter()
        .enumerate()
        .filter(|(_, line)| line.symbol.is_some())
        .map(|(i, line)| (i, line.clone()))
        .collect();

    // check for duplicate symbols
    for (i, line) in marked_lines.iter() {
        for (j, other_line) in marked_lines.iter() {
            if i != j && line.symbol == other_line.symbol {
                return Err(Error::InvalidInstruction(*i));
            }
        }
    }

    // replace any uses of symbols with the memory address
    debug!(
        "Adding {:?} marker(s) into instructions",
        marked_lines.len()
    );
    for (address, line) in marked_lines.iter() {
        // if the line has a symbol, replace any uses of the symbol in lines with the memory address
        let symbol = line.symbol.as_ref().unwrap();
        replace_symbol_with_address(&mut lines, symbol, *address);
    }

    for (i, line) in lines.iter().enumerate() {
        let mut instruction = line.instruction_string.split_whitespace();

        let opcode = instruction.next().unwrap();
        let argument = instruction.next();

        let get_arg = || {
            argument
                .expect(format!("Invalid instruction: {:?}", line).as_str())
                .parse::<usize>()
                .expect(format!("Invalid instruction: {:?}", line).as_str())
        };

        let instruction = match opcode {
            "INP" => Instruction::INP,
            "OUT" => Instruction::OUT,
            "LDA" => Instruction::LDA(addr!(get_arg())),
            "STA" => Instruction::STA(addr!(get_arg())),
            "ADD" => Instruction::ADD(addr!(get_arg())),
            "SUB" => Instruction::SUB(addr!(get_arg())),
            "BRP" => Instruction::BRP(addr!(get_arg())),
            "BRZ" => Instruction::BRZ(addr!(get_arg())),
            "BRA" => Instruction::BRA(addr!(get_arg())),
            "HLT" => Instruction::HLT,
            _ => return Err(Error::InvalidInstruction(i)),
        };

        ram[i] = MemoryValue::Instruction(instruction);
    }

    Ok(ram)
}

fn clean_line(line: &str) -> String {
    line
        .split("//").next().unwrap()
        .chars()
        .filter(|c| c.is_alphanumeric() || c.is_whitespace())
        .collect()
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

    #[test]
    fn test_run_factorial() {
        let program = include_str!("../lmc/factorial.lmc");
        let ram = parse_program(program.to_string()).unwrap();

        let mut vm = VM::new();
        vm.load_memory(ram);

        while !vm.halted {
            vm.execute_cycle();
        }

        assert_eq!(vm.acc, 2_432_902_008_176_640_000);
    }
}
