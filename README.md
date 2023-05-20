# LMC

LMC-RS is a Rust implementation of the Little Man Computer. LMC is generally used for educational purposes as it models a simple Von Neumann architecture computer which has all of the basic features of a modern computer. It is programmed using assembly code.

## Usage

You can probably turn this into a more useful library but currently it's a binary that loads the assembly code from a file and runs it.

```bash
cargo install --path .
lmc <file>
```

Yes. That's it. There are numerous examples in lmc directory.
