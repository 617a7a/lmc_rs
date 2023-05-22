use tracing::debug;

use crate::{Memory, Error, MemoryValue, MEMORY_SIZE, Instruction, addr, MemoryAddress};

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

/// Parses an LMC program into memory
pub fn parse_program(code: String) -> Result<Memory, Error> {
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
}
