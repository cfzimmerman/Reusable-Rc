use std::{
    cell::{Cell, RefCell},
    mem::size_of,
    rc::Rc,
};

type PoolRef<T> = Rc<RefCell<ReuRcPoolInner<T>>>;

/// To do: great doc comment with example
//
// To developer: Do not impl clone on this. Have the user create and use one pool, otherwise
// the API gets too complicated. Pool sharability is only for internal use.
pub struct ReuRcPool<T> {
    /// The pool needs to be accessible by every pointer allocated by it, so it's
    /// wrapped in an `Rc` itself. Again, this `Rc` is only for the purpose of
    /// returning memory to the pool and doesn't have any interaction with the
    /// user-facing API.
    pool: PoolRef<T>,
}

/// A memory pool for reusable reference-counted objects. Spawns `ReuRc` smart
/// pointers that behave like a normal `Rc`, but the underlying heap allocations
/// are returnedto this memory pool on `drop` instead of being freed.
struct ReuRcPoolInner<T> {
    /// Exclusive pointers to aligned, dereferencable, initialized objects of
    /// type `ReuRcInner<T>`. If a pointer is in this vector, it must be the
    /// only pointer or reference in existence to that allocation.
    unused: Vec<*mut ReuRcInner<T>>,

    /// The maximum number of objects that will be stored for reuse.
    /// Note that the user supplies a limit in `bytes`, but this value is
    /// the total count of allocated but unused `ReuRcInner<T>`.
    max_num_unused: Option<usize>,
}

impl<T> ReuRcPool<T>
where
    T: Default + 'static,
{
    /// Creates a new memory pool from which reusable Rcs can be spawned.
    ///
    /// The `max_bytes` parameter specifies the amount of unused heap memory the pool
    /// is permitted to hold on to. If `None`, the pool will reuse every allocation
    /// it makes, giving the pool a nondecreasing amount of allocated memory of size
    /// equal to the maximum amount of memory ever needed at once.
    ///
    /// If a limit of `Some(max_bytes)` is given, the pool will always yield `ReuRc`
    /// objects (heap permitting) from `spawn`, but memory will be freed when necessary
    /// so that total the amount of unused memory held by the pool never exceeds `max_bytes`.
    pub fn new(max_bytes: Option<usize>) -> Self {
        ReuRcPool {
            pool: Rc::new(RefCell::new(ReuRcPoolInner {
                unused: Vec::new(),
                max_num_unused: max_bytes.map(|bytes| bytes / size_of::<ReuRcInner<T>>()),
            })),
        }
    }

    /// Acquires a new `ReuRc` from the memory pool. The given `ReuRc` may be a new allocation,
    /// or it may be recycled from a previously spawned object. Regardless, the returned smart
    /// pointer will be the only reference to this data and can safely be used like a normal `Rc`.
    ///
    /// The `init` closure is used to initialize the underlying data. Any value or contents
    /// of `T` passed to `init` are UNDEFINED and it is considered Undefined Behavior to
    /// read or copy the preexisting object.
    /// Use `init` only to initialize `T` as if it were a completely new object.
    pub fn spawn(&mut self, init: impl Fn(&mut T)) -> ReuRc<T> {
        let reused = self.pool.borrow_mut().unused.pop();
        let unused_alloc = reused.unwrap_or_else(|| ReuRcInner::new(self.pool.clone()));

        {
            // Safety:
            // - Alignment: The pointer originally came from a leaked box. Because the box was
            // aligned and pointers are never moved by this module, the pointer to that box is still aligned.
            // - Dereferencable: The pointer points to the beginning of a single contiguous element of
            // type `ReuRcInner<T>`. This module never casts pointers to a different underlying
            // type, so it still points to an object of type `ReuRcInner<T>`.
            // - Initialized: Because all pointers in the `unused` vector have static lifetime from
            // `Box::leak` AND have not been deallocated, they are always initialized.
            // - Aliasing: This allocation either came from a fresh `Box::leak` or the `unused` pool. Newly leaked
            // data has static lifetime and is always safe. The `unused` pool has an invariant of always
            // holding exclusive pointers to initialized objects of static data. As long as that is maintained,
            // this data is allocated.
            let alloc_mut = unsafe {
                unused_alloc
                    .as_mut()
                    .expect("The allocation pointer should NEVER be null")
            };

            let ref_ct = alloc_mut.ref_ct.get_mut();
            assert_eq!(
                *ref_ct, 0,
                "Nonzero ref count for alloc indicates serious Undefined Behavior"
            );
            init(&mut alloc_mut.contents);
            alloc_mut.incr_ref_ct();
        }

        // After this exits, zero mutable references or pointers to this type exist, and none will
        // exist until the last reference to this is dropped and the allocation is reclaimed.
        ReuRc {
            alloc: unused_alloc as *const ReuRcInner<T>,
        }
    }
}

pub struct ReuRc<T>
where
    T: Default + 'static,
{
    alloc: *const ReuRcInner<T>,
}

impl<T> ReuRc<T>
where
    T: Default + 'static,
{
    /// Retrieve an immutable reference to the shared data.
    pub fn borrow(&self) -> &T {
        // Safety:
        // See `spawn` for Alignment and Dereferencable.
        // - Initialized: Assuming the data was initialized at the time of `clone`, the reference
        // count to this data has always been nonzero since then (because of `self`). Because
        // the data can only be deallocated when the reference count is zero, this data must
        // still be initialized.
        // - Aliasing: Mutable pointers to this data are only ever held exclusively in
        // the `unused` pool vector of briefly before deallocation in `ReuRc::drop`.
        // Because both of those events can only occur when the reference count is zero
        // and the existence of `Self` implies that currently it is nonzero, there must
        // only be immutable references to this aligned, dereferencable, and initialized data.
        unsafe {
            &self
                .alloc
                .as_ref()
                .expect("The allocation pointer should NEVER be null")
                .contents
        }
    }
}

impl<T> Clone for ReuRc<T>
where
    T: Default + 'static,
{
    fn clone(&self) -> Self {
        // Safety:
        // See `Spawn` for Alignment and Dereferencable.
        // - Initialized: Assume the data returned from `spawn` was initialized. The allocation
        // is never modified as long as the internal `ref_ct` is nonzero. The internal `ref_ct`
        // is nonzero as long as at least one `ReuRc` exists pointing to it. At least one
        // is guaranteed to exist because at-minimum `self` exists. So, the allocation is just
        // as valid now as when it was created.
        // - Aliasing: We're creating a const reference from a const pointer. Initialization in
        // `spawn` traded this allocation's only pointer for a const pointer. After that, only
        // const pointers exist to the `ReuRcInner`. The exclusive mutable pointer is only ever
        // re-created on `Drop`, so there do not exist any mutable references to this data at
        // the same time this const reference exists.
        {
            let alloc_ref = unsafe {
                self.alloc
                    .as_ref()
                    .expect("The allocation pointer should NEVER be null")
            };
            alloc_ref.incr_ref_ct();
        }
        ReuRc { alloc: self.alloc }
    }
}

impl<T> Drop for ReuRc<T>
where
    T: Default + 'static,
{
    fn drop(&mut self) {
        {
            // Safety:
            // See `Spawn` for Alignment and Dereferencable.
            // - Initialized: Assume the safety of `spawn` and `clone`. By their invariants and
            // because `self` imples the existence of at least one `ReuRc`, `alloc`
            // is a valid pointer to an instance of `ReuRcInner<T>`.
            // - Aliasing: Because the reference count is nonzero, the only pointers to the
            // allocation are `const`, meaning that an immutable reference will not exist
            // simultanously with a mutable one.
            let alloc_ref = unsafe {
                self.alloc
                    .as_ref()
                    .expect("The allocation pointer should NEVER be null")
            };
            alloc_ref.decr_ref_ct();
            if alloc_ref.ref_ct.get() != 0 {
                return;
            }

            // Safety:
            // The early return above is essential. This path is ONLY taken if the reference
            // count is now zero. If the reference count is zero, then after this `Drop` concludes
            // there will be no external references to this data. That means the
            // pointer below is the only pointer in existence to this data, so casting it as `mut`
            // and later using it is allowed by the aliasing rules.
            let alloc_mut = self.alloc as *mut ReuRcInner<T>;

            let mut pool = alloc_ref.pool.borrow_mut();
            let pool_is_full = pool
                .max_num_unused
                .is_some_and(|limit| limit <= pool.unused.len());
            if !pool_is_full {
                pool.unused.push(alloc_mut);
                return;
            }
        }

        // Safety:
        // The ONLY reason to be here is (1) the reference count is zero and (2) the unused
        // allocation pool is full already.
        // By the safety comments above, assert that there are now zero references or pointers
        // to this data except for the pointer being dropped right now. After drop, there will
        // be zero pointers or references in existence. So, freeing this data will not leave
        // any dangling pointers or references after drop.
        // Constructing a Box from the data is safe because because the data was box-leaked
        // in the first place and has not been structurally modified since.
        unsafe {
            let _ = Box::from_raw(self.alloc as *mut ReuRcInner<T>);
        };
    }
}

struct ReuRcInner<T> {
    pool: PoolRef<T>,
    ref_ct: Cell<usize>,
    contents: T,
}

impl<T> ReuRcInner<T>
where
    T: Default + 'static,
{
    /// Allocates a new instance of `Self`. Because `Self` is leaked onto
    /// the heap, it now has a static lifetime and will be unmoved until the
    /// program exits or the value is forcibly deallocated.
    fn new(pool: PoolRef<T>) -> *mut Self {
        let reu_rc = ReuRcInner {
            pool,
            ref_ct: 0.into(),
            contents: T::default(),
        };
        let leaked: &'static mut Self = Box::leak(Box::new(reu_rc));
        leaked as *mut Self
    }

    /// Increases the reference count on `Self`. This should only ever be called
    /// when a new reference to the underlying data is created.
    fn incr_ref_ct(&self) {
        self.ref_ct.set(self.ref_ct.get() + 1);
    }

    /// Decreases the reference count on `Self`. This should only ever be called
    /// when a reference to the underlying data is dropped.
    fn decr_ref_ct(&self) {
        self.ref_ct.set(
            self.ref_ct
                .get()
                .checked_sub(1)
                .expect("Decreasing a ref ct of zero indicates a major bug and Undefined Behavior"),
        );
    }
}
