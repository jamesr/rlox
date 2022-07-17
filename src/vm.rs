use std::{collections::HashMap, fmt::Display};

use crate::error;

#[derive(PartialEq, Clone, Copy, Debug)]
pub enum OpCode {
    Return,
    Constant(usize),
    Negate,
    Add,
    Subtract,
    Multiply,
    Divide,
    Nil,
    True,
    False,
    Not,
    Equal,
    Greater,
    Less,
    Print,
    GetGlobal(usize),
    DefineGlobal(usize),
    SetGlobal(usize),
    JumpIfFalse(i16),
    Jump(i16),
    Pop,
}

#[derive(PartialEq, PartialOrd, Clone, Debug)]
pub enum Value {
    Nil,
    Bool(bool),
    Number(f64),
    String(String),
}

impl Value {
    fn falsey(&self) -> bool {
        match self {
            Value::Nil => true,
            Value::Bool(b) => !*b,
            _ => false,
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Nil => write!(f, "nil"),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Number(n) => write!(f, "{}", n),
            Value::String(s) => write!(f, "{}", s),
        }
    }
}

pub struct Chunk {
    pub code: Vec<OpCode>,
    pub constants: Vec<Value>,
    locs: Vec<error::Location>,
}

macro_rules! add_opcode_helper {
    ($name:ident, $opcode:expr) => {
        pub fn $name(&mut self, loc: error::Location) {
            self.add_opcode($opcode, loc);
        }
    };
}

impl Chunk {
    pub fn new() -> Self {
        Self {
            code: vec![],
            constants: vec![],
            locs: vec![],
        }
    }

    fn add_opcode(&mut self, op: OpCode, loc: error::Location) {
        self.code.push(op);
        self.locs.push(loc);
    }

    pub fn add_constant(&mut self, v: Value, loc: error::Location) {
        self.add_opcode(OpCode::Constant(self.constants.len()), loc);
        self.constants.push(v);
    }

    pub fn add_get_global(&mut self, name: &str, loc: error::Location) {
        self.add_opcode(OpCode::GetGlobal(self.constants.len()), loc);
        self.constants.push(Value::String(name.to_string()));
    }

    pub fn add_define_global(&mut self, name: &str, loc: error::Location) {
        self.add_opcode(OpCode::DefineGlobal(self.constants.len()), loc);
        self.constants.push(Value::String(name.to_string()));
    }

    pub fn add_set_global(&mut self, name: &str, loc: error::Location) {
        self.add_opcode(OpCode::SetGlobal(self.constants.len()), loc);
        self.constants.push(Value::String(name.to_string()));
    }

    pub fn add_jump(&mut self, op: OpCode, loc: error::Location) -> usize {
        self.add_opcode(op, loc);
        self.code.len() - 1
    }

    pub fn patch_jump(&mut self, offset: usize) {
        let code_len = self.code.len();
        let jump_opcode = self.code[offset];
        let relative_offset = i16::checked_sub(code_len as i16 - 1, offset as i16).unwrap();
        match jump_opcode {
            OpCode::JumpIfFalse(_) => self.code[offset] = OpCode::JumpIfFalse(relative_offset),
            OpCode::Jump(_) => self.code[offset] = OpCode::Jump(relative_offset),
            _ => {
                panic!(
                    "attempted to patch non-jump opcode {:?} at offset {}",
                    jump_opcode, offset
                );
            }
        }
    }

    add_opcode_helper!(add_return, OpCode::Return);
    add_opcode_helper!(add_negate, OpCode::Negate);
    add_opcode_helper!(add_add, OpCode::Add);
    add_opcode_helper!(add_subtract, OpCode::Subtract);
    add_opcode_helper!(add_multiply, OpCode::Multiply);
    add_opcode_helper!(add_divide, OpCode::Divide);
    add_opcode_helper!(add_nil, OpCode::Nil);
    add_opcode_helper!(add_true, OpCode::True);
    add_opcode_helper!(add_false, OpCode::False);
    add_opcode_helper!(add_not, OpCode::Not);
    add_opcode_helper!(add_equal, OpCode::Equal);
    add_opcode_helper!(add_greater, OpCode::Greater);
    add_opcode_helper!(add_less, OpCode::Less);
    add_opcode_helper!(add_print, OpCode::Print);
    add_opcode_helper!(add_pop, OpCode::Pop);

    pub fn disassemble(&self) -> Result<(), error::RuntimeError> {
        for i in 0..self.code.len() {
            print!("{:0>3} ", i);
            self.disassemble_instruction(i)?;
        }
        Ok(())
    }

    fn disassemble_instruction(&self, i: usize) -> Result<(), error::RuntimeError> {
        print!("{:0>4} ", self.locs[i].line);
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
            OpCode::Nil => println!("nil"),
            OpCode::True => println!("true"),
            OpCode::False => println!("false"),
            OpCode::Not => println!("not"),
            OpCode::Equal => println!("equal"),
            OpCode::Greater => print!("greater"),
            OpCode::Less => print!("less"),
            OpCode::Print => print!("print"),
            OpCode::GetGlobal(index) => {
                println!(
                    "get global index {} value {}",
                    index, self.constants[*index]
                )
            }
            OpCode::DefineGlobal(index) => {
                println!(
                    "define global index {} value {}",
                    index, self.constants[*index]
                )
            }
            OpCode::SetGlobal(index) => {
                println!(
                    "set global index {} value {}",
                    index, self.constants[*index]
                )
            }
            OpCode::JumpIfFalse(offset) => println!("jump if false {}", offset),
            OpCode::Jump(offset) => println!("jump {}", offset),
            OpCode::Pop => println!("pop"),
        }
        Ok(())
    }
}

pub struct Vm {
    ip: usize,
    stack: Vec<Value>,
    trace: bool,
    current_loc: error::Location,
    globals: HashMap<String, Value>,
}

impl Vm {
    pub fn new() -> Self {
        Self {
            ip: 0,
            stack: vec![],
            trace: false,
            current_loc: error::Location::default(),
            globals: HashMap::new(),
        }
    }

    pub fn enable_tracing(&mut self) {
        self.trace = true;
    }

    fn push(&mut self, v: Value) {
        self.stack.push(v)
    }

    fn error(&self, message: &str) -> error::RuntimeError {
        error::RuntimeError::new(message, self.current_loc.clone())
    }

    fn pop(&mut self) -> Result<Value, error::RuntimeError> {
        match self.stack.pop() {
            Some(v) => Ok(v),
            None => Err(self.error("Pop with empty stack.")),
        }
    }

    fn peek(&self) -> Result<&Value, error::RuntimeError> {
        match self.stack.last() {
            Some(v) => Ok(v),
            None => Err(self.error("Peek with empty stack.")),
        }
    }

    fn binary_op_number<F>(&mut self, op: F) -> Result<(), error::RuntimeError>
    where
        F: FnOnce(f64, f64) -> f64,
    {
        // The right hand side is at the top of the stack and the left hand side is below.
        if let Value::Number(rhs) = self.pop()? {
            if let Value::Number(lhs) = self.pop()? {
                self.push(Value::Number(op(lhs, rhs)));
                return Ok(());
            }
        }
        return Err(self.error("Invalid types for binary op."));
    }

    fn binary_op_string<F>(&mut self, op: F) -> Result<(), error::RuntimeError>
    where
        F: FnOnce(String, String) -> String,
    {
        // The right hand side is at the top of the stack and the left hand side is below.
        if let Value::String(rhs) = self.pop()? {
            if let Value::String(lhs) = self.pop()? {
                self.push(Value::String(op(lhs, rhs)));
                return Ok(());
            }
        }
        return Err(error::RuntimeError::new(
            "Invalid types for binary op.",
            self.current_loc.clone(),
        ));
    }

    pub fn run(&mut self, chunk: Chunk) -> Result<Value, error::RuntimeError> {
        self.ip = 0;
        loop {
            if self.trace {
                println!("=== instruction ===");
                chunk.disassemble_instruction(self.ip)?;
                println!();
                println!("=== stack ===");
                for v in &self.stack {
                    println!("[ {} ]", v);
                }
                println!("=== globals ===");
                for (name, value) in &self.globals {
                    println!("\"{}\": -> {}", &name, &value);
                }
            }
            self.current_loc = chunk.locs[self.ip].clone();
            match chunk.code[self.ip] {
                OpCode::Return => {
                    let value = self.pop()?;
                    return Ok(value);
                }
                OpCode::Constant(index) => {
                    let value = chunk.constants[index].clone();
                    self.push(value);
                }
                OpCode::Negate => {
                    if let Value::Number(n) = self.pop()? {
                        self.push(Value::Number(-n));
                    } else {
                        return Err(self.error("Operand must be a number."));
                    }
                }
                OpCode::Add => match self.peek()? {
                    Value::Number(_) => self.binary_op_number(|lhs, rhs| lhs + rhs),
                    Value::String(_) => self.binary_op_string(|lhs, rhs| lhs + &rhs),
                    _ => return Err(self.error("Operands must be two strings or two numbers.")),
                }?,
                OpCode::Subtract => self.binary_op_number(|lhs, rhs| lhs - rhs)?,
                OpCode::Multiply => self.binary_op_number(|lhs, rhs| lhs * rhs)?,
                OpCode::Divide => self.binary_op_number(|lhs, rhs| lhs / rhs)?,
                OpCode::Nil => self.push(Value::Nil),
                OpCode::True => self.push(Value::Bool(true)),
                OpCode::False => self.push(Value::Bool(false)),
                OpCode::Not => {
                    let val = self.pop()?;
                    self.push(Value::Bool(val.falsey()))
                }
                OpCode::Equal => {
                    let rhs = self.pop()?;
                    let lhs = self.pop()?;
                    self.push(Value::Bool(lhs == rhs));
                }
                OpCode::Greater => {
                    let rhs = self.pop()?;
                    let lhs = self.pop()?;
                    self.push(Value::Bool(lhs > rhs));
                }
                OpCode::Less => {
                    let rhs = self.pop()?;
                    let lhs = self.pop()?;
                    self.push(Value::Bool(lhs < rhs));
                }
                OpCode::Print => {
                    let value = self.pop()?;
                    println!("{}", value);
                }
                OpCode::GetGlobal(index) => {
                    let name_constant = chunk.constants[index].clone();
                    if let Value::String(name) = name_constant {
                        let value = match self.globals.get(&name) {
                            Some(v) => v,
                            None => {
                                return Err(self.error(&format!("Undefined variable {}", &name)));
                            }
                        };
                        self.push(value.clone());
                    } else {
                        return Err(self.error("global name must be string"));
                    }
                }
                OpCode::DefineGlobal(index) => {
                    let name_constant = chunk.constants[index].clone();
                    if let Value::String(name) = name_constant {
                        let value = self.pop()?;
                        self.globals.insert(name, value);
                    } else {
                        return Err(self.error("global name must be string"));
                    }
                }
                OpCode::SetGlobal(index) => {
                    let name_constant = chunk.constants[index].clone();
                    if let Value::String(name) = name_constant {
                        let value = self.pop()?;
                        match self.globals.get_mut(&name) {
                            Some(v) => *v = value,
                            None => {
                                return Err(self.error(&format!("Undefined variable '{}'", name)));
                            }
                        }
                    } else {
                        return Err(self.error("global name must be string"));
                    }
                }
                OpCode::JumpIfFalse(offset) => {
                    if self.peek()?.falsey() {
                        self.ip = (self.ip as i16).checked_add(offset).unwrap() as usize;
                    }
                }
                OpCode::Jump(offset) => {
                    self.ip = (self.ip as i16).checked_add(offset).unwrap() as usize;
                }
                OpCode::Pop => {
                    self.pop()?;
                }
            }
            self.ip = self.ip + 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::error;

    use super::*;

    #[test]
    fn disassemble_return() -> Result<(), error::Error> {
        let mut chunk = Chunk::new();
        chunk.add_return(error::Location::default());
        chunk.disassemble()?;
        Ok(())
    }

    #[test]
    fn disassemble_constant() -> Result<(), error::Error> {
        let mut chunk = Chunk::new();
        chunk.add_constant(Value::Number(4.3), error::Location::default());
        chunk.disassemble()?;
        Ok(())
    }

    macro_rules! run_test_add_opcode {
        ($chunk:ident, patch_jump, $_loc:expr, $param:expr) => {
            $chunk.patch_jump($param)
        };
        ($chunk:ident, $opcode:ident, $loc:expr, $param:expr) => {
            $chunk.$opcode($param, $loc);
        };
        ($chunk:ident, $opcode:ident, $loc:expr) => {
            $chunk.$opcode($loc);
        };
    }

    macro_rules! run_test {
        ($name:ident, $expected:expr, $($opcode:ident $(=> $param:expr)? ),*) => {
            #[test]
            fn $name() -> Result<(), error::Error> {
                let mut vm = Vm::new();
                //vm.enable_tracing();
                let mut chunk = Chunk::new();
                let mut loc = error::Location::default();
                $(
                    run_test_add_opcode!(chunk, $opcode, loc.clone() $(, $param)?);
                    loc.line = loc.line + 1;
                )*
                //chunk.disassemble();
                let result = vm.run(chunk);
                assert_eq!(result, $expected);
                Ok(())
            }
        };
    }

    run_test!(
        run_constant_and_return,
        Ok(Value::Number(2.4)),
        add_constant => Value::Number(2.4),
        add_return
    );

    run_test!(
        run_negate,
        Ok(Value::Number(-2.4)),
        add_constant => Value::Number(2.4),
        add_negate,
        add_return
    );

    run_test!(
        run_arithmetic,
        Ok(Value::Number(-4.6 / 5.6)),
        add_constant => Value::Number(1.2),
        add_constant => Value::Number(3.4),
        add_add,
        add_constant => Value::Number(5.6),
        add_divide,
        add_negate,
        add_return
    );

    run_test!(
        run_add_strings,
        Ok(Value::String("foobar".to_string())),
        add_constant => Value::String("foo".to_string()),
        add_constant => Value::String("bar".to_string()),
        add_add,
        add_return
    );

    run_test!(
        run_add_number_and_string,
        Err(error::RuntimeError::new(
                "Invalid types for binary op.",
                error::Location { line: 2, col: 0..0 }
            )),
        add_constant => Value::String("foo".to_string()),
        add_constant => Value::Number(1.2),
        add_add,
        add_return
    );

    run_test!(
        run_greater_than_not,
        Ok(Value::Bool(true)),
        add_constant => Value::Number(0.6),
        add_constant => Value::Number(1.2),
        add_greater,
        add_not,
        add_return
    );

    run_test!(
        run_jump_if_false,
        Ok(Value::Number(1.0)),
        add_constant => Value::Number(1.0),
        add_constant => Value::Bool(false),
        add_jump => OpCode::JumpIfFalse(3),
        add_pop, // Pop the conditional in "then" branch.
        add_constant => Value::Number(2.0),
        add_jump => OpCode::Jump(1), // Jump over "else" branch.
        add_pop, // Pop the conditional in "else" branch.
        add_return

    );
}
