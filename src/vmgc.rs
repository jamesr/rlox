use std::{collections::BTreeMap, fmt::Display, rc::Rc};

use crate::{gc, vm};

pub type Heap = gc::Heap<VmHeader>;
pub type FunctionPtr = gc::CellPtr<Function>;

pub type Map = BTreeMap<String, Value>;
pub type MapPtr = gc::CellPtr<Map>;

pub type Array = Vec<Value>;
pub type ArrayPtr = gc::CellPtr<Array>;

pub type StringPtr = gc::CellPtr<String>;

pub trait Callable: std::fmt::Debug {
    fn call(&self, args: Vec<Value>) -> Value;

    fn arity(&self) -> usize;
}

#[derive(PartialOrd, Debug, Clone)]
pub enum Value {
    Nil,
    Bool(bool),
    Number(f64),
    String(StringPtr),
    Function(FunctionPtr),
    NativeFunction(by_address::ByAddress<Rc<dyn Callable>>),
    Array(ArrayPtr),
    Map(MapPtr),
}

impl Value {
    pub fn falsey(&self) -> bool {
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
            Value::String(s) => write!(f, "{}", s.borrow()),
            Value::Function(fun) => write!(f, "<fn {}>", fun.name),
            Value::NativeFunction(_) => write!(f, "<native fn>"),
            Value::Array(a) => write!(f, "array len {}", a.len()),
            Value::Map(m) => write!(f, "map with {} entries", m.len()),
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match self {
            Value::Nil => match other {
                Value::Nil => true,
                _ => false,
            },
            Value::Bool(b) => match other {
                Value::Bool(ob) => b == ob,
                _ => false,
            },
            Value::Number(n) => match other {
                Value::Number(on) => n == on,
                _ => false,
            },
            Value::String(s) => match other {
                Value::String(os) => s.as_ptr() == os.as_ptr() || s.borrow() == os.borrow(),
                _ => false,
            },
            Value::Function(f) => match other {
                Value::Function(of) => f.as_ptr() == of.as_ptr(),
                _ => false,
            },
            Value::NativeFunction(f) => match other {
                Value::NativeFunction(of) => f == of,
                _ => false,
            },
            Value::Array(a) => match other {
                Value::Array(oa) => a.as_ptr() == oa.as_ptr() || a.borrow() == oa.borrow(),
                _ => false,
            },
            Value::Map(m) => match other {
                Value::Map(om) => m.as_ptr() == om.as_ptr() || m.borrow() == om.borrow(),
                _ => false,
            },
        }
    }
}

#[derive(Debug)]
pub struct Function {
    pub arity: usize,
    pub chunk: vm::Chunk,
    pub name: String,
}

impl Function {
    pub fn new(arity: usize, name: &str) -> Self {
        Self {
            arity,
            chunk: vm::Chunk::new(),
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

pub struct VmHeader {
    mark: gc::Mark,
    ty: VmTypeId,
}

#[derive(Clone, Copy)]
pub enum VmTypeId {
    Function,
    Map,
    Array,
    String,
}

impl gc::AllocTypeId for VmTypeId {}

impl gc::AllocObject<VmTypeId> for Function {
    const TYPE_ID: VmTypeId = VmTypeId::Function;
}

impl gc::AllocObject<VmTypeId> for Map {
    const TYPE_ID: VmTypeId = VmTypeId::Map;
}

impl gc::AllocObject<VmTypeId> for Array {
    const TYPE_ID: VmTypeId = VmTypeId::Array;
}

impl gc::AllocObject<VmTypeId> for String {
    const TYPE_ID: VmTypeId = VmTypeId::String;
}

impl gc::AllocHeader for VmHeader {
    type TypeId = VmTypeId;

    fn new<T: gc::AllocObject<Self::TypeId>>(_size: usize, mark: gc::Mark) -> Self {
        Self {
            mark,
            ty: T::TYPE_ID,
        }
    }

    fn new_array<T: gc::AllocObject<Self::TypeId>>(_size: usize, mark: gc::Mark) -> Self {
        Self {
            mark,
            ty: T::TYPE_ID,
        }
    }

    fn trace(&self, object: std::ptr::NonNull<()>) -> Vec<std::ptr::NonNull<()>> {
        fn trace_value(val: &Value) -> Vec<std::ptr::NonNull<()>> {
            match val {
                Value::Function(f) => vec![f.as_ptr().cast::<()>()],
                Value::Array(a) => vec![a.as_ptr().cast::<()>()],
                Value::Map(m) => vec![m.as_ptr().cast::<()>()],
                _ => vec![],
            }
        }
        match self.ty {
            VmTypeId::Function => vec![],
            VmTypeId::Map => {
                let map = unsafe { object.cast::<Map>().as_ref() };
                let mut ptrs = vec![];
                map.values().for_each(|v| ptrs.append(&mut trace_value(v)));
                ptrs
            }
            VmTypeId::Array => {
                let array = unsafe { object.cast::<Array>().as_ref() };
                let mut ptrs = vec![];
                array.iter().for_each(|v| ptrs.append(&mut trace_value(v)));
                ptrs
            }
            VmTypeId::String => vec![],
        }
    }

    fn drop(&self, object: std::ptr::NonNull<()>) {
        match self.ty {
            VmTypeId::Function => unsafe {
                std::ptr::drop_in_place(object.cast::<Function>().as_ptr());
            },
            VmTypeId::Map => unsafe {
                std::ptr::drop_in_place(object.cast::<Map>().as_ptr());
            },
            VmTypeId::Array => unsafe {
                std::ptr::drop_in_place(object.cast::<Array>().as_ptr());
            },
            VmTypeId::String => unsafe {
                std::ptr::drop_in_place(object.cast::<String>().as_ptr());
            },
        }
    }

    fn set_mark(&mut self, mark: gc::Mark) {
        self.mark = mark;
    }

    fn mark(&self) -> gc::Mark {
        self.mark
    }

    fn size(&self) -> usize {
        match self.ty {
            VmTypeId::Function => std::mem::size_of::<Function>(),
            VmTypeId::Map => std::mem::size_of::<Map>(),
            VmTypeId::Array => std::mem::size_of::<Array>(),
            VmTypeId::String => std::mem::size_of::<String>(),
        }
    }

    fn layout(&self) -> std::alloc::Layout {
        match self.ty {
            VmTypeId::Function => std::alloc::Layout::new::<Function>(),
            VmTypeId::Map => std::alloc::Layout::new::<Map>(),
            VmTypeId::Array => std::alloc::Layout::new::<Array>(),
            VmTypeId::String => std::alloc::Layout::new::<String>(),
        }
    }

    fn type_id(&self) -> Self::TypeId {
        self.ty
    }
}
