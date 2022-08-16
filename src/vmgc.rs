use std::{collections::BTreeMap, fmt::Display};

use crate::{gc, vm};

pub type Heap = gc::Heap<VmHeader>;
pub type ValuePtr = gc::CellPtr<Value>;
pub type FunctionPtr = gc::CellPtr<Function>;

pub type Map = BTreeMap<String, ValuePtr>;
pub type MapPtr = gc::CellPtr<Map>;

pub type Array = Vec<ValuePtr>;
pub type ArrayPtr = gc::CellPtr<Array>;

#[derive(PartialEq, PartialOrd, Debug)]
pub enum Value {
    Nil,
    Bool(bool),
    Number(f64),
    String(String),
    Function(FunctionPtr),
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
    Value, // TODO: Pack things
    Function,
    Map,
    Array,
}

impl gc::AllocTypeId for VmTypeId {}

impl gc::AllocObject<VmTypeId> for Value {
    const TYPE_ID: VmTypeId = VmTypeId::Value;
}

impl gc::AllocObject<VmTypeId> for Function {
    const TYPE_ID: VmTypeId = VmTypeId::Function;
}

impl gc::AllocObject<VmTypeId> for Map {
    const TYPE_ID: VmTypeId = VmTypeId::Map;
}

impl gc::AllocObject<VmTypeId> for Array {
    const TYPE_ID: VmTypeId = VmTypeId::Array;
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
        match self.ty {
            VmTypeId::Value => {
                let val = unsafe { object.cast::<Value>().as_ref() };
                match val {
                    Value::Function(f) => vec![f.as_ptr().cast::<()>()],
                    Value::Array(a) => vec![a.as_ptr().cast::<()>()],
                    Value::Map(m) => vec![m.as_ptr().cast::<()>()],
                    _ => vec![],
                }
            }
            VmTypeId::Function => vec![],
            VmTypeId::Map => {
                let map = unsafe { object.cast::<Map>().as_ref() };
                map.values()
                    .map(|v| v.as_ptr().cast::<()>())
                    .collect::<Vec<_>>()
            }
            VmTypeId::Array => {
                let array = unsafe { object.cast::<Array>().as_ref() };
                array
                    .iter()
                    .map(|ptr| ptr.as_ptr().cast::<()>())
                    .collect::<Vec<_>>()
            }
        }
    }

    fn drop(&self, object: std::ptr::NonNull<()>) {
        match self.ty {
            VmTypeId::Value => unsafe {
                std::ptr::drop_in_place(object.cast::<Value>().as_ptr());
            },
            VmTypeId::Function => unsafe {
                std::ptr::drop_in_place(object.cast::<Function>().as_ptr());
            },
            VmTypeId::Map => unsafe {
                std::ptr::drop_in_place(object.cast::<Map>().as_ptr());
            },
            VmTypeId::Array => unsafe {
                std::ptr::drop_in_place(object.cast::<Array>().as_ptr());
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
            VmTypeId::Value => std::mem::size_of::<Value>(),
            VmTypeId::Function => std::mem::size_of::<Function>(),
            VmTypeId::Map => std::mem::size_of::<Map>(),
            VmTypeId::Array => std::mem::size_of::<Array>(),
        }
    }

    fn layout(&self) -> std::alloc::Layout {
        match self.ty {
            VmTypeId::Value => std::alloc::Layout::new::<Value>(),
            VmTypeId::Function => std::alloc::Layout::new::<Function>(),
            VmTypeId::Map => std::alloc::Layout::new::<Map>(),
            VmTypeId::Array => std::alloc::Layout::new::<Array>(),
        }
    }

    fn type_id(&self) -> Self::TypeId {
        self.ty
    }
}
