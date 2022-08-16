use std::alloc::Layout;
use std::cell::{Cell, RefCell};
use std::fmt::Debug;
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

impl<H> Default for Heap<H> {
    fn default() -> Self {
        Self {
            roots: Default::default(),
            all_allocs: Default::default(),
            tracing: Default::default(),
            _phantom: Default::default(),
        }
    }
}

#[derive(Debug, PartialEq, PartialOrd)]
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

    fn drop(&self, object: NonNull<()>);

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

        if self.tracing {
            println!("allocated object at {:?} header at {:?}", object_ptr, ptr);
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

#[derive(PartialEq, PartialOrd)]
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

    pub fn as_ptr(&self) -> std::ptr::NonNull<T> {
        self.inner.get().ptr
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

impl<T: Sized + Debug> Debug for CellPtr<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "CellPtr({:?}) -> {:?}",
            self.as_ptr(),
            self.borrow()
        ))
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
        if self.tracing {
            self.collect();
        }
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
            println!("=== collect start ===");
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
                reachable.append(&mut self.trace(header, next));
            }
        }

        if self.tracing {
            println!("sweep - all allocs is {:?}", self.all_allocs);
        }
        let num_objects = self.all_allocs.borrow().len();
        let mut still_active = vec![];
        // Cull all the unreachable objects.
        for mut header_ptr in self.all_allocs.take().into_iter() {
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
                still_active.push(header_ptr);
            } else {
                header.drop(Heap::<H>::get_object(header_ptr));
                let ptr = header_ptr.as_ptr() as *mut u8;
                if self.tracing {
                    println!("deallocating {:?}", ptr);
                }
                let layout = Layout::new::<H>().extend(header.layout()).unwrap().0;
                unsafe {
                    std::alloc::dealloc(ptr, layout);
                }
            }
        }
        let freed = num_objects - still_active.len();
        self.all_allocs.replace(still_active);
        if self.tracing {
            println!("=== collect over. freed {} objects ===", freed);
        }
        freed
    }

    fn trace(&self, header: &H, header_ptr: std::ptr::NonNull<H>) -> Vec<std::ptr::NonNull<H>> {
        let object = Heap::<H>::get_object(header_ptr);
        let traced: Vec<NonNull<()>> = header.trace(object);
        traced
            .iter()
            .map(|o| Heap::<H>::get_header(*o))
            .map(|s| s.cast::<H>())
            .collect::<Vec<_>>()
    }

    pub fn enable_tracing(&mut self, enable: bool) {
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
        DropItem,
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

        fn new<T: AllocObject<Self::TypeId>>(_size: usize, mark: Mark) -> Self {
            Self {
                mark,
                ty: T::TYPE_ID,
            }
        }

        fn new_array<T: AllocObject<Self::TypeId>>(_size: usize, mark: Mark) -> Self {
            Self {
                mark,
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
                TestTypeId::DropItem => vec![],
            }
        }

        fn drop(&self, object: NonNull<()>) {
            match self.ty {
                TestTypeId::Number => {}
                TestTypeId::ObjectWithPtrs => {}
                TestTypeId::DropItem => {
                    unsafe {
                        let ptr = object.cast::<DropItem>().as_ptr();
                        std::ptr::drop_in_place(ptr);
                    };
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
            match self.ty {
                TestTypeId::Number => std::mem::size_of::<Number>(),
                TestTypeId::ObjectWithPtrs => std::mem::size_of::<ObjectWithPtrs>(),
                TestTypeId::DropItem => std::mem::size_of::<DropItem>(),
            }
        }

        fn layout(&self) -> Layout {
            match self.ty {
                TestTypeId::Number => Layout::new::<Number>(),
                TestTypeId::ObjectWithPtrs => Layout::new::<ObjectWithPtrs>(),
                TestTypeId::DropItem => Layout::new::<DropItem>(),
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

    struct DropTracker {
        dropped: HashSet<i32>,
    }

    impl DropTracker {
        fn new() -> Self {
            Self {
                dropped: HashSet::new(),
            }
        }
        fn add_drop(&mut self, id: i32) {
            self.dropped.insert(id);
        }

        fn dropped(&self, id: i32) -> bool {
            self.dropped.contains(&id)
        }
    }

    struct DropItem<'a> {
        id: i32,
        tracker: &'a mut DropTracker,
    }

    impl<'a> Drop for DropItem<'a> {
        fn drop(&mut self) {
            self.tracker.add_drop(self.id);
        }
    }

    impl AllocObject<TestTypeId> for DropItem<'_> {
        const TYPE_ID: TestTypeId = TestTypeId::DropItem;
    }

    #[test]
    fn drop_test() {
        let mut tracker = DropTracker::new();
        let mut heap = Heap::<TestHeader>::new();
        let item = DropItem {
            id: 1,
            tracker: &mut tracker,
        };
        let _ptr = heap.alloc(item);
        assert!(!tracker.dropped(1));
        assert_eq!(heap.collect(), 1);
        assert!(tracker.dropped(1));
    }
}
