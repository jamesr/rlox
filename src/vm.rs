use std::{fmt::Display, ops::Add};

enum OpCode {
    Return,
    Constant(usize),
    Negate,
    Add,
    Subtract,
    Multiply,
    Divide,
}

#[derive(PartialEq, Clone, Copy, Debug)]
enum Value {
    Number(f64),
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Number(n) => write!(f, "{}", n),
        }
    }
}

struct Chunk {
    code: Vec<OpCode>,
    constants: Vec<Value>,
    lines: Vec<usize>,
}

impl Chunk {
    pub fn new() -> Self {
        Self {
            code: vec![],
            constants: vec![],
            lines: vec![],
        }
    }

    fn add_opcode(&mut self, op: OpCode, line: usize) {
        self.code.push(op);
        self.lines.push(line);
    }

    pub fn add_return(&mut self, line: usize) {
        self.add_opcode(OpCode::Return, line);
    }

    pub fn add_constant(&mut self, v: Value, line: usize) {
        self.add_opcode(OpCode::Constant(self.constants.len()), line);
        self.constants.push(v);
    }

    pub fn add_negate(&mut self, line: usize) {
        self.add_opcode(OpCode::Negate, line);
    }

    pub fn add_add(&mut self, line: usize) {
        self.add_opcode(OpCode::Add, line);
    }

    pub fn add_subtract(&mut self, line: usize) {
        self.add_opcode(OpCode::Subtract, line);
    }

    pub fn add_multiply(&mut self, line: usize) {
        self.add_opcode(OpCode::Multiply, line);
    }

    pub fn add_divide(&mut self, line: usize) {
        self.add_opcode(OpCode::Divide, line);
    }

    fn disassemble(&self) -> Result<(), String> {
        for i in 0..self.code.len() {
            print!("{:0>3} ", i);
            self.disassemble_instruction(i)?;
        }
        Ok(())
    }

    fn disassemble_instruction(&self, i: usize) -> Result<(), String> {
        print!("{:0>4} ", self.lines[i]);
        match &self.code[i] {
            OpCode::Return => println!("return"),
            OpCode::Constant(index) => {
                println!("constant index {} value {}", index, self.constants[*index])
            }
            OpCode::Negate => println!("negate"),
            OpCode::Add => println!("add"),
            OpCode::Subtract => println!("subtract"),
            OpCode::Multiply => println!("multiply"),
            OpCode::Divide => println!("divide"),
        }
        Ok(())
    }
}

struct Vm<'a> {
    chunk: Option<&'a Chunk>,
    ip: usize,
    stack: Vec<Value>,
    trace: bool,
}

impl<'a> Vm<'a> {
    pub fn new() -> Self {
        Self {
            chunk: None,
            ip: 0,
            stack: vec![],
            trace: false,
        }
    }

    fn enable_tracing(&mut self) {
        self.trace = true;
    }

    fn push(&mut self, v: Value) {
        self.stack.push(v)
    }

    fn pop(&mut self) -> Value {
        self.stack.pop().unwrap()
    }

    fn binary_op_number<F>(&mut self, op: F) -> Result<(), String>
    where
        F: FnOnce(f64, f64) -> f64,
    {
        // The right hand side is at the top of the stack and the left hand side is below.
        if let Value::Number(rhs) = self.pop() {
            if let Value::Number(lhs) = self.pop() {
                self.push(Value::Number(op(lhs, rhs)));
                return Ok(());
            }
        }
        return Err("Invalid types for binary ".to_string());
    }

    fn run(&mut self, chunk: &'a Chunk) -> Result<Value, String> {
        self.chunk = Some(chunk);
        loop {
            if self.trace {
                chunk.disassemble_instruction(self.ip)?;
                for v in &self.stack {
                    println!("[ {} ]", v);
                }
            }
            match chunk.code[self.ip] {
                OpCode::Return => {
                    let value = self.pop();
                    return Ok(value);
                }
                OpCode::Constant(index) => {
                    let value = chunk.constants[index];
                    self.push(value);
                }
                OpCode::Negate => {
                    if let Value::Number(n) = self.pop() {
                        self.push(Value::Number(-n));
                    }
                }
                OpCode::Add => self.binary_op_number(|lhs, rhs| lhs + rhs)?,
                OpCode::Subtract => self.binary_op_number(|lhs, rhs| lhs - rhs)?,
                OpCode::Multiply => self.binary_op_number(|lhs, rhs| lhs * rhs)?,
                OpCode::Divide => self.binary_op_number(|lhs, rhs| lhs / rhs)?,
            }
            self.ip = self.ip + 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn disassemble_return() -> Result<(), String> {
        let mut chunk = Chunk::new();
        chunk.add_return(0);
        chunk.disassemble()?;
        Ok(())
    }

    #[test]
    fn disassemble_constant() -> Result<(), String> {
        let mut chunk = Chunk::new();
        chunk.add_constant(Value::Number(4.3), 0);
        chunk.disassemble()?;
        Ok(())
    }

    #[test]
    fn run_constant_and_return() -> Result<(), String> {
        let mut vm = Vm::new();
        let mut chunk = Chunk::new();
        chunk.add_constant(Value::Number(2.4), 0);
        chunk.add_return(1);
        vm.enable_tracing();
        let value = vm.run(&chunk)?;
        assert_eq!(value, Value::Number(2.4));
        Ok(())
    }

    #[test]
    fn run_negate() -> Result<(), String> {
        let mut vm = Vm::new();
        let mut chunk = Chunk::new();
        chunk.add_constant(Value::Number(2.4), 0);
        chunk.add_negate(1);
        chunk.add_return(2);
        assert_eq!(vm.run(&chunk)?, Value::Number(-2.4));
        Ok(())
    }

    #[test]
    fn run_arithmetic() -> Result<(), String> {
        let mut vm = Vm::new();
        let mut chunk = Chunk::new();
        chunk.add_constant(Value::Number(1.2), 1);
        chunk.add_constant(Value::Number(3.4), 1);
        chunk.add_add(2);
        chunk.add_constant(Value::Number(5.6), 3);
        chunk.add_divide(3);
        chunk.add_negate(4);
        chunk.add_return(5);
        assert_eq!(vm.run(&chunk)?, Value::Number(-4.6 / 5.6));

        Ok(())
    }
}
