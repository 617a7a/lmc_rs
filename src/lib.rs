use std::ops::AddAssign;

mod parser;
mod vm;

pub use parser::*;
pub use vm::*;

pub const MEMORY_SIZE: usize = 100;

#[derive(Debug, PartialEq)]
pub enum Error {
    InvalidInstruction(usize),
    InvalidMemoryAddress,
    InvalidValue,
}

#[repr(usize)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Instruction {
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
pub enum MemoryValue {
    Value(isize),
    Instruction(Instruction),
}

// we'll deal with DAT separately as it doesn't have an opcode, but just defines a memory address

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct MemoryAddress(usize);

impl MemoryAddress {
    fn new(address: usize) -> Result<Self, Error> {
        if address > (MEMORY_SIZE - 1) {
            Err(Error::InvalidMemoryAddress)
        } else {
            Ok(Self(address))
        }
    }
}

impl AddAssign<usize> for MemoryAddress {
    fn add_assign(&mut self, rhs: usize) {
        self.0 += rhs;
    }
}

impl std::fmt::Debug for MemoryAddress {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:02}", self.0)
    }
}

#[macro_export]
macro_rules! addr {
    ($addr:expr) => {
        MemoryAddress::new($addr).unwrap()
    };
}

pub type Memory = [MemoryValue; MEMORY_SIZE];
