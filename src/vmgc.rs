use crate::{gc, vm::Value};

pub type ValuePtr = gc::CellPtr<Value>;
pub type Heap = gc::Heap<VmHeader>;

pub struct VmHeader {
    mark: gc::Mark,
    ty: VmTypeId,
}

#[derive(Clone, Copy)]
pub enum VmTypeId {
    Value, // TODO: Pack things
}

impl gc::AllocTypeId for VmTypeId {}

impl gc::AllocObject<VmTypeId> for Value {
    const TYPE_ID: VmTypeId = VmTypeId::Value;
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
        let val = unsafe { object.cast::<Value>().as_ref() };
        match val {
            Value::Array(a) => a
                .iter()
                .map(|ptr| ptr.as_ptr().cast::<()>())
                .collect::<Vec<_>>(),
            Value::Map(m) => m
                .values()
                .map(|v| v.as_ptr().cast::<()>())
                .collect::<Vec<_>>(),
            _ => vec![],
        }
    }

    fn set_mark(&mut self, mark: gc::Mark) {
        self.mark = mark;
    }

    fn mark(&self) -> gc::Mark {
        self.mark
    }

    fn size(&self) -> usize {
        std::mem::size_of::<Value>()
    }

    fn layout(&self) -> std::alloc::Layout {
        std::alloc::Layout::new::<Value>()
    }

    fn type_id(&self) -> Self::TypeId {
        self.ty
    }
}
