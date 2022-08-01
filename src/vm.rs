use std::{cell::RefCell, collections::BTreeMap, fmt::Display};

use crate::{
    error,
    gc::Heap,
    vmgc::{self, ValuePtr},
};

#[derive(PartialEq, PartialOrd, Clone, Copy, Debug)]
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
    GetLocal(usize),
    SetLocal(usize),
    JumpIfFalse(i16),
    Jump(i16),
    Pop,
}

#[derive(PartialEq, PartialOrd, Debug)]
pub enum Value {
    Nil,
    Bool(bool),
    Number(f64),
    String(String),
    Function(Function),
    Array(Vec<ValuePtr>),
    Map(BTreeMap<String, ValuePtr>),
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
            Value::Function(fun) => write!(f, "<fn {}>", fun.name),
            Value::Array(a) => write!(f, "array len {}", a.len()),
            Value::Map(m) => write!(f, "map with {} entries", m.len()),
        }
    }
}

#[derive(Debug)]
pub struct Function {
    pub arity: usize,
    pub chunk: Chunk,
    pub name: String,
}

impl Function {
    pub fn new(arity: usize, name: &str) -> Self {
        Self {
            arity,
            chunk: Chunk::new(),
            name: name.to_string(),
        }
    }
}

impl PartialEq for Function {
    fn eq(&self, _other: &Self) -> bool {
        false
    }
}

impl PartialOrd for Function {
    fn partial_cmp(&self, _other: &Self) -> Option<std::cmp::Ordering> {
        None
    }
}

struct CallFrame {
    function: ValuePtr,
    ip: usize,
    stack_offset: usize,
}

#[derive(Debug)]
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

    pub fn add_get_local(&mut self, depth: usize, loc: error::Location) {
        self.add_opcode(OpCode::GetLocal(depth), loc);
    }

    pub fn add_set_local(&mut self, depth: usize, loc: error::Location) {
        self.add_opcode(OpCode::SetLocal(depth), loc);
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

    pub fn current_code_offset(&self) -> usize {
        self.code.len()
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
            OpCode::GetLocal(depth) => println!("get local index {}", depth),
            OpCode::SetLocal(depth) => println!("set local index {}", depth),
        }
        Ok(())
    }
}

struct State {
    frames: Vec<CallFrame>,
    stack: ValuePtr,
    globals: ValuePtr,
    heap: vmgc::Heap,
}

pub struct Vm {
    state: RefCell<State>,
    trace: bool,
    current_loc: error::Location,
}

impl Vm {
    pub fn new() -> Self {
        let mut heap = Heap::new();
        //heap.enable_tracing(true);
        let stack = heap.alloc_cell(Value::Array(vec![])).unwrap();
        heap.add_root(stack.clone());
        let globals = heap.alloc_cell(Value::Map(BTreeMap::new())).unwrap();
        heap.add_root(globals.clone());
        Self {
            state: RefCell::new(State {
                frames: vec![],
                stack,
                globals,
                heap,
            }),
            trace: false,
            current_loc: error::Location::default(),
        }
    }

    pub fn enable_tracing(&mut self) {
        self.trace = true;
    }

    pub fn alloc_value(&self, v: Value) -> Result<ValuePtr, error::RuntimeError> {
        self.state_mut().heap.alloc_cell(v).map_err(|e| {
            error::RuntimeError::new(
                &format!("Allocation error: {:?}", e),
                error::Location::default(),
            )
        })
    }

    fn state(&self) -> std::cell::Ref<State> {
        self.state.borrow()
    }

    fn state_mut(&self) -> std::cell::RefMut<State> {
        self.state.borrow_mut()
    }

    fn push(&self, v: ValuePtr) {
        match self.state_mut().stack.borrow_mut() {
            Value::Array(a) => a.push(v),
            _ => panic!("stack is not an array"),
        }
    }

    fn push_value(&self, v: Value) -> Result<(), error::RuntimeError> {
        let ptr = self.alloc_value(v)?;
        Ok(self.push(ptr))
    }

    fn pop(&self) -> Result<ValuePtr, error::RuntimeError> {
        match self.state_mut().stack.borrow_mut() {
            Value::Array(a) => match a.pop() {
                Some(v) => Ok(v),
                None => Err(self.error("Pop with empty stack.")),
            },
            _ => panic!("stack is not an array"),
        }
    }

    fn peek(&self) -> Result<ValuePtr, error::RuntimeError> {
        if let Value::Array(stack) = self.state().stack.borrow() {
            match stack.last() {
                Some(v) => Ok(v.clone()),
                None => Err(self.error("Peek with empty stack.")),
            }
        } else {
            panic!("stack is not an array");
        }
    }

    fn error(&self, message: &str) -> error::RuntimeError {
        error::RuntimeError::new(message, self.current_loc.clone())
    }

    fn binary_op_number<F>(&self, op: F) -> Result<(), error::RuntimeError>
    where
        F: FnOnce(f64, f64) -> f64,
    {
        // The right hand side is at the top of the stack and the left hand side is below.
        if let Value::Number(rhs) = self.pop()?.borrow() {
            if let Value::Number(lhs) = self.pop()?.borrow() {
                self.push_value(Value::Number(op(*lhs, *rhs)))?;
                return Ok(());
            }
        }
        return Err(self.error("Invalid types for binary op."));
    }

    fn binary_op_string<F>(&self, op: F) -> Result<(), error::RuntimeError>
    where
        F: FnOnce(String, String) -> String,
    {
        // The right hand side is at the top of the stack and the left hand side is below.
        if let Value::String(rhs) = self.pop()?.borrow() {
            if let Value::String(lhs) = self.pop()?.borrow() {
                // TODO - extra string copies here
                self.push_value(Value::String(op(lhs.to_string(), rhs.to_string())))?;
                return Ok(());
            }
        }
        return Err(error::RuntimeError::new(
            "Invalid types for binary op.",
            self.current_loc.clone(),
        ));
    }

    pub fn run(&mut self, function: Function) -> Result<ValuePtr, error::RuntimeError> {
        let fun_ptr = self.alloc_value(Value::Function(function))?;
        self.push(fun_ptr.clone());
        self.state_mut().frames.push(CallFrame {
            function: fun_ptr,
            ip: 0,
            stack_offset: 0, //  self.stack().len(),
        });
        self.run_frame()
    }

    fn ip(&self) -> usize {
        self.state().frames.last().unwrap().ip
    }

    fn set_ip(&self, ip: usize) {
        self.state_mut().frames.last_mut().unwrap().ip = ip
    }

    pub fn run_frame(&mut self) -> Result<ValuePtr, error::RuntimeError> {
        let fun = {
            let state = self.state();
            let top_frame = state.frames.last().unwrap();
            top_frame.function.clone()
        };
        let chunk = match fun.borrow() {
            Value::Function(f) => &f.chunk,
            _ => panic!("call frame does not refer to function"),
        };

        loop {
            if self.trace {
                println!("=== instruction ===");
                chunk.disassemble_instruction(self.ip())?;
                println!();
                println!("=== stack ===");
                if let Value::Array(stack) = self.state().stack.borrow() {
                    for v in stack {
                        println!("[ {} ]", v.borrow());
                    }
                }
                println!("=== globals ===");
                if let Value::Map(globals) = self.state().globals.borrow() {
                    for (name, value) in globals {
                        println!("\"{}\": -> {}", &name, value.borrow());
                    }
                }
            }
            self.current_loc = chunk.locs[self.ip()].clone();
            match chunk.code[self.ip()] {
                OpCode::Return => {
                    let value = self.pop()?;
                    return Ok(value);
                }
                OpCode::Constant(index) => {
                    let value = &chunk.constants[index];
                    let value_clone = match value {
                        Value::Nil => Value::Nil,
                        Value::Bool(b) => Value::Bool(*b),
                        Value::Number(n) => Value::Number(*n),
                        Value::String(s) => Value::String(s.to_string()),
                        Value::Function(_) => panic!("unexpected function in constant table"),
                        Value::Array(_) => panic!("unexpected array in constant table"),
                        Value::Map(_) => panic!("unexpected array in constant table"),
                    };
                    self.push_value(value_clone)?;
                }
                OpCode::Negate => {
                    if let Value::Number(n) = *self.pop()? {
                        self.push_value(Value::Number(-n))?;
                    } else {
                        return Err(self.error("Operand must be a number."));
                    }
                }
                OpCode::Add => match self.peek()?.borrow() {
                    Value::Number(_) => self.binary_op_number(|lhs, rhs| lhs + rhs),
                    Value::String(_) => self.binary_op_string(|lhs, rhs| lhs + &rhs),
                    _ => return Err(self.error("Operands must be two strings or two numbers.")),
                }?,
                OpCode::Subtract => self.binary_op_number(|lhs, rhs| lhs - rhs)?,
                OpCode::Multiply => self.binary_op_number(|lhs, rhs| lhs * rhs)?,
                OpCode::Divide => self.binary_op_number(|lhs, rhs| lhs / rhs)?,
                OpCode::Nil => self.push_value(Value::Nil)?,
                OpCode::True => self.push_value(Value::Bool(true))?,
                OpCode::False => self.push_value(Value::Bool(false))?,
                OpCode::Not => {
                    let val = self.pop()?;
                    self.push_value(Value::Bool(val.falsey()))?;
                }
                OpCode::Equal => {
                    let rhs = &*self.pop()?;
                    let lhs = &*self.pop()?;
                    self.push_value(Value::Bool(lhs == rhs))?;
                }
                OpCode::Greater => {
                    let rhs = &*self.pop()?;
                    let lhs = &*self.pop()?;
                    self.push_value(Value::Bool(lhs > rhs))?;
                }
                OpCode::Less => {
                    let rhs = &*self.pop()?;
                    let lhs = &*self.pop()?;
                    self.push_value(Value::Bool(lhs < rhs))?;
                }
                OpCode::Print => {
                    let value = &*self.pop()?;
                    println!("{}", value);
                }
                OpCode::GetGlobal(index) => {
                    let name_constant = &chunk.constants[index];
                    if let Value::String(name) = name_constant {
                        if let Value::Map(globals) = self.state().globals.borrow() {
                            let value = match globals.get(name) {
                                Some(v) => v,
                                None => {
                                    return Err(self.error(&format!("Undefined variable {}", name)));
                                }
                            };
                            self.push(value.clone());
                        }
                    } else {
                        return Err(self.error("global name must be string"));
                    }
                }
                OpCode::DefineGlobal(index) => {
                    let name_constant = &chunk.constants[index];
                    if let Value::String(name) = name_constant {
                        let value = self.pop()?;
                        if let Value::Map(m) = self.state_mut().globals.borrow_mut() {
                            m.insert(name.to_string(), value);
                        }
                    } else {
                        return Err(self.error("global name must be string"));
                    }
                }
                OpCode::SetGlobal(index) => {
                    let name_constant = &chunk.constants[index];
                    if let Value::String(name) = name_constant {
                        let value = self.pop()?;
                        if let Value::Map(m) = self.state_mut().globals.borrow_mut() {
                            match m.get_mut(name) {
                                Some(v) => *v = value,
                                None => {
                                    return Err(
                                        self.error(&format!("Undefined variable '{}'", name))
                                    );
                                }
                            }
                        }
                    } else {
                        return Err(self.error("global name must be string"));
                    }
                }
                OpCode::JumpIfFalse(offset) => {
                    if self.peek()?.falsey() {
                        self.set_ip((self.ip() as i16).checked_add(offset).unwrap() as usize);
                    }
                }
                OpCode::Jump(offset) => {
                    self.set_ip((self.ip() as i16).checked_add(offset).unwrap() as usize);
                }
                OpCode::Pop => {
                    self.pop()?;
                }
                OpCode::GetLocal(idx) => {
                    if let Value::Array(stack) = self.state().stack.borrow() {
                        self.push(stack[idx].clone());
                    }
                }
                OpCode::SetLocal(idx) => match self.state_mut().stack.borrow_mut() {
                    Value::Array(a) => a[idx] = self.peek()?.clone(),
                    _ => panic!("stack is not an array"),
                },
            }
            let new_ip = self.ip() + 1;
            if new_ip == chunk.code.len() {
                return Ok(self.alloc_value(Value::Nil)?);
            }
            self.set_ip(new_ip);
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
                let mut fun = Function::new(0, "<test>");
                let mut loc = error::Location::default();
                let chunk = &mut fun.chunk;
                $(
                    run_test_add_opcode!(chunk, $opcode, loc.clone() $(, $param)?);
                    loc.line = loc.line + 1;
                )*
                //fun.chunk.disassemble();
                let function = vm.alloc_value(Value::Function(fun))?;
                vm.push(function.clone());
                vm.state.borrow_mut().frames.push(CallFrame {
                    function,
                    ip: 0,
                    stack_offset: 0,
                });

                let expected: Result::<Value, error::RuntimeError> = $expected;
                match vm.run_frame(){
                    Ok(v) => {
                        assert!(expected.is_ok());
                        assert_eq!(*v, expected.ok().unwrap());
                    },
                    Err(e) => {
                        assert!(expected.is_err());
                        assert_eq!(e, expected.err().unwrap());
                    },
                };
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
