use std::alloc::Layout;
use std::cell::{Cell, RefCell};
use std::mem::size_of;
use std::ptr::NonNull;
use std::{collections::HashSet, marker::PhantomData};

extern crate alloc;

pub struct Heap<H> {
    roots: HashSet<NonNull<H>>,
    all_allocs: RefCell<Vec<NonNull<H>>>,
    tracing: bool,
    _phantom: PhantomData<H>,
}

#[derive(Debug)]
pub struct RawPtr<T: Sized> {
    ptr: NonNull<T>,
}

impl<T: Sized> Clone for RawPtr<T> {
    fn clone(&self) -> Self {
        RawPtr { ptr: self.ptr }
    }
}

impl<T: Sized> Copy for RawPtr<T> {}

impl<T> RawPtr<T> {
    fn new(ptr: *mut T) -> Self {
        RawPtr {
            ptr: unsafe { NonNull::new_unchecked(ptr) },
        }
    }
}

pub trait AllocTypeId: Copy + Clone {}

#[derive(PartialEq, Copy, Clone, Debug)]
pub enum Mark {
    Allocated,
    Reachable,
}

pub trait AllocObject<T: AllocTypeId> {
    const TYPE_ID: T;
}

pub trait AllocHeader: Sized {
    type TypeId: AllocTypeId;

    fn new<T: AllocObject<Self::TypeId>>(size: usize, mark: Mark) -> Self;

    fn new_array<T: AllocObject<Self::TypeId>>(size: usize, mark: Mark) -> Self;

    fn trace(&self, object: NonNull<()>) -> Vec<NonNull<()>>;

    fn set_mark(&mut self, mark: Mark);

    fn mark(&self) -> Mark;

    fn size(&self) -> usize;

    fn layout(&self) -> Layout;

    fn type_id(&self) -> Self::TypeId;
}

#[derive(Debug)]
pub enum AllocError {
    OOM,
    BadAllocationRequest,
}

trait AllocRaw {
    type Header: AllocHeader;

    fn alloc<T>(&self, object: T) -> Result<RawPtr<T>, AllocError>
    where
        T: AllocObject<<Self::Header as AllocHeader>::TypeId>;

    fn alloc_array<T>(&self, size_bytes: usize) -> Result<RawPtr<u8>, AllocError>
    where
        T: AllocObject<<Self::Header as AllocHeader>::TypeId>;

    fn get_header(object: NonNull<()>) -> NonNull<Self::Header>;
    fn get_object(header: NonNull<Self::Header>) -> NonNull<()>;
}

impl<H: AllocHeader> AllocRaw for Heap<H> {
    type Header = H;

    fn alloc<T>(&self, object: T) -> Result<RawPtr<T>, AllocError>
    where
        T: AllocObject<<Self::Header as AllocHeader>::TypeId>,
    {
        // Compute the layout of a header followed by an object.
        let layout = Layout::new::<Self::Header>()
            .extend(Layout::for_value::<T>(&object))
            .map_err(|_| AllocError::BadAllocationRequest)?
            .0;

        // Get memory for the header+object from the global allocator.
        let ptr = unsafe { std::alloc::alloc(layout) };
        if ptr.is_null() {
            return Err(AllocError::OOM);
        }

        // Construct a header value.
        let header = Self::Header::new::<T>(size_of::<T>(), Mark::Allocated);

        // Write it into the start of the allocated memory.
        unsafe {
            (ptr as *mut Self::Header).write(header);
        }

        // Compute address of start of the object.
        let object_ptr = unsafe { (ptr as *mut Self::Header).offset(1) as *mut T };

        // Write object into object space.
        unsafe {
            object_ptr.write(object);
        }

        // Remember this allocation.
        self.all_allocs
            .borrow_mut()
            .push(unsafe { NonNull::new_unchecked(ptr as *mut Self::Header) });

        Ok(RawPtr::new(object_ptr))
    }

    fn alloc_array<T>(&self, size_bytes: usize) -> Result<RawPtr<u8>, AllocError>
    where
        T: AllocObject<<Self::Header as AllocHeader>::TypeId>,
    {
        // Compute layout for header + array of size_bytes u8s
        let layout = Layout::new::<Self::Header>()
            .extend(Layout::array::<u8>(size_bytes).map_err(|_| AllocError::BadAllocationRequest)?)
            .map_err(|_| AllocError::BadAllocationRequest)?
            .0;

        // Get memory for the header+object from the global allocator.
        // Ask for zeroed memory to initialize the array.
        let ptr = unsafe { std::alloc::alloc_zeroed(layout) };
        if ptr.is_null() {
            return Err(AllocError::OOM);
        }

        // Construct a header.
        let header = Self::Header::new_array::<T>(size_bytes, Mark::Allocated);

        // Write it to the start of the allocated memory.
        unsafe {
            (ptr as *mut Self::Header).write(header);
        }

        // Compute the start of the array.
        let array_ptr = unsafe { (ptr as *mut Self::Header).offset(1) as *mut u8 };

        // Remember this allocation.
        self.all_allocs
            .borrow_mut()
            .push(unsafe { NonNull::new_unchecked(ptr as *mut Self::Header) });

        Ok(RawPtr::new(array_ptr))
    }

    fn get_header(object: NonNull<()>) -> NonNull<Self::Header> {
        unsafe { NonNull::new_unchecked(object.cast::<Self::Header>().as_ptr().offset(-1)) }
    }
    fn get_object(header: NonNull<Self::Header>) -> NonNull<()> {
        unsafe { NonNull::new_unchecked(header.as_ptr().offset(1).cast::<()>()) }
    }
}

#[derive(Debug)]
pub struct CellPtr<T: Sized> {
    inner: Cell<RawPtr<T>>,
}

impl<T: Sized> CellPtr<T> {
    fn new(inner: Cell<RawPtr<T>>) -> Self {
        Self { inner }
    }

    pub fn borrow(&self) -> &T {
        unsafe { self.inner.get().ptr.as_ref() }
    }

    pub fn borrow_mut(&self) -> &mut T {
        unsafe { self.inner.get().ptr.as_mut() }
    }
}

impl<T: Sized> Clone for CellPtr<T> {
    fn clone(&self) -> Self {
        CellPtr {
            inner: self.inner.clone(),
        }
    }
}

impl<T: Sized> std::ops::Deref for CellPtr<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.borrow()
    }
}

impl<T: Sized> std::ops::DerefMut for CellPtr<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.borrow_mut()
    }
}

impl<H: AllocHeader> Heap<H> {
    pub fn new() -> Self {
        Self {
            roots: HashSet::new(),
            all_allocs: RefCell::new(vec![]),
            tracing: false,
            _phantom: PhantomData::default(),
        }
    }

    pub fn alloc_cell<T: AllocObject<H::TypeId>>(
        &mut self,
        object: T,
    ) -> Result<CellPtr<T>, AllocError> {
        Ok(CellPtr::new(Cell::new(self.alloc(object)?)))
    }

    pub fn add_root<T: AllocObject<H::TypeId>>(&mut self, root: CellPtr<T>) {
        self.roots
            .insert(Heap::<H>::get_header(root.inner.get().ptr.cast::<()>()));
    }

    pub fn remove_root<T: AllocObject<H::TypeId>>(&mut self, root: CellPtr<T>) {
        self.roots
            .remove(&Heap::<H>::get_header(root.inner.get().ptr.cast::<()>()));
    }

    pub fn collect(&mut self) -> usize {
        if self.tracing {
            println!("mark with {} roots", self.roots.len());
        }
        let mut reachable = self.roots.iter().map(|r| *r).collect::<Vec<_>>();
        // Mark all the reachable objects.
        while !reachable.is_empty() {
            let mut next = reachable.pop().unwrap();
            let header = unsafe { next.as_mut() };
            if self.tracing {
                println!(
                    "considering object {:?} mark is {:?}",
                    next.as_ptr(),
                    header.mark()
                );
            }
            if header.mark() != Mark::Reachable {
                header.set_mark(Mark::Reachable);
                let object = Heap::<H>::get_object(next);
                let traced: Vec<NonNull<()>> = header.trace(object);
                traced
                    .iter()
                    .map(|o| Heap::<H>::get_header(*o))
                    .for_each(|s| reachable.push(s.cast::<H>()));
            }
        }
        let mut freed = 0;

        if self.tracing {
            println!("sweep");
        }
        // Cull all the unreachable objects.
        for header_ptr in &mut *self.all_allocs.borrow_mut() {
            let header = unsafe { header_ptr.as_mut() };
            if self.tracing {
                println!(
                    "looking at {:?} mark is {:?}",
                    header_ptr.as_ptr(),
                    header.mark()
                );
            }
            if header.mark() == Mark::Reachable {
                header.set_mark(Mark::Allocated);
            } else {
                // TODO: Drop the object somehow - through the trait?
                // let object = Heap::<H>::get_object(*header_ptr);
                let ptr = header_ptr.as_ptr() as *mut u8;
                let layout = Layout::new::<H>().extend(header.layout()).unwrap().0;
                unsafe {
                    std::alloc::dealloc(ptr, layout);
                }

                freed = freed + 1
            }
        }
        freed
    }

    fn enable_tracing(&mut self, enable: bool) {
        self.tracing = enable;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TestHeader {
        mark: Mark,
        ty: TestTypeId,
    }

    #[derive(PartialEq, Copy, Clone)]
    enum TestTypeId {
        Number,
        ObjectWithPtrs,
    }

    impl AllocTypeId for TestTypeId {}

    #[derive(PartialEq, Copy, Clone, Debug)]
    struct Number {
        val: u32,
    }

    struct ObjectWithPtrs {
        data: u32,
        ptrs: Vec<CellPtr<ObjectWithPtrs>>,
    }

    impl AllocObject<TestTypeId> for Number {
        const TYPE_ID: TestTypeId = TestTypeId::Number;
    }
    impl AllocObject<TestTypeId> for ObjectWithPtrs {
        const TYPE_ID: TestTypeId = TestTypeId::ObjectWithPtrs;
    }

    impl AllocHeader for TestHeader {
        type TypeId = TestTypeId;

        fn new<T: AllocObject<Self::TypeId>>(size: usize, mark: Mark) -> Self {
            Self {
                mark: Mark::Allocated,
                ty: T::TYPE_ID,
            }
        }

        fn new_array<T: AllocObject<Self::TypeId>>(size: usize, mark: Mark) -> Self {
            Self {
                mark: Mark::Allocated,
                ty: T::TYPE_ID,
            }
        }

        fn trace(&self, object: NonNull<()>) -> Vec<NonNull<()>> {
            match self.ty {
                TestTypeId::Number => vec![],
                TestTypeId::ObjectWithPtrs => {
                    let obj_ref = unsafe { object.cast::<ObjectWithPtrs>().as_ref() };
                    obj_ref
                        .ptrs
                        .iter()
                        .map(|c| c.inner.get().ptr.cast::<()>())
                        .collect::<Vec<_>>()
                }
            }
        }

        fn set_mark(&mut self, mark: Mark) {
            self.mark = mark;
        }

        fn mark(&self) -> Mark {
            self.mark
        }

        fn size(&self) -> usize {
            0
        }

        fn layout(&self) -> Layout {
            match self.ty {
                TestTypeId::Number => Layout::new::<Number>(),
                TestTypeId::ObjectWithPtrs => Layout::new::<ObjectWithPtrs>(),
            }
        }

        fn type_id(&self) -> Self::TypeId {
            self.ty
        }
    }

    #[test]
    fn alloc_num() -> Result<(), AllocError> {
        let mut heap = Heap::<TestHeader>::new();
        let ptr = heap.alloc(Number { val: 5 })?;
        let cell_ptr = CellPtr::new(Cell::new(ptr));
        heap.add_root(cell_ptr.clone());
        let num = cell_ptr.borrow();
        assert_eq!(num, &Number { val: 5 });
        let num_mut = cell_ptr.borrow_mut();
        *num_mut = Number { val: 6 };
        assert_eq!(*num_mut, Number { val: 6 });

        assert_eq!(heap.collect(), 0);
        heap.remove_root(cell_ptr.clone());
        assert_eq!(heap.collect(), 1);
        Ok(())
    }

    #[test]
    fn alloc_objects_with_handles() -> Result<(), AllocError> {
        let mut heap = Heap::<TestHeader>::new();
        let ptr_one = heap.alloc(ObjectWithPtrs {
            data: 42,
            ptrs: vec![],
        })?;
        let cell_ptr_one = CellPtr::new(Cell::new(ptr_one));
        let ptr_two = heap.alloc(ObjectWithPtrs {
            data: 17,
            ptrs: vec![cell_ptr_one.clone()],
        })?;
        let cell_ptr_two = CellPtr::new(Cell::new(ptr_two));
        heap.add_root(cell_ptr_two.clone());
        assert_eq!(heap.collect(), 0);
        assert_eq!(cell_ptr_one.borrow().data, 42);
        assert_eq!(cell_ptr_two.borrow().data, 17);
        heap.remove_root(cell_ptr_two.clone());
        assert_eq!(heap.collect(), 2);
        Ok(())
    }
}
