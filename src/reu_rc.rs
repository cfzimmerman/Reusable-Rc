use std::{
    cell::{Cell, RefCell},
    rc::Rc,
};

type PoolRef<T> = Rc<RefCell<ReuRcPoolInner<T>>>;

// Do not impl clone on this. Have the user create and use one pool, otherwise
// the API gets too complicated. Pool sharability is only for internal use.
pub struct ReuRcPool<T> {
    pool: PoolRef<T>,
}

struct ReuRcPoolInner<T> {
    unused: Vec<*mut ReuRcInner<T>>,
}

impl<T> ReuRcPool<T>
where
    T: Default + 'static,
{
    /// Returns the allocation to the pool or deallocates it.
    fn relcaim(&mut self, child: &mut ReuRcInner<T>) {
        assert_eq!(
            *child.ref_ct.get_mut(),
            0,
            "Reclaim must only ever be called when there are zero references out"
        );
        // The &mut guarantees exclusive access
        // Should this be moved straight into drop? Probably.
        // Create a *mut from the &mut
        // Does the data really need to be wiped?
        // Push the pointer into the unused vec
        // Comment: if needed, there could be a deallocation sequence here as well. Maybe set the
        // max pool size?
        todo!("actually reclaim it")
    }

    fn spawn(&mut self, init: impl Fn(&mut T)) -> ReuRc<T> {
        let reused = self.pool.borrow_mut().unused.pop();
        let unused_alloc = reused.unwrap_or_else(|| ReuRcInner::new(self.pool.clone()));

        {
            // Safety:
            // - Alignment: The pointer came from a leaked box. Because the box was aligned, the pointer
            // to that box is also aligned.
            // - Dereferencable: The pointer points to the beginning of a single contiguous element of
            // type ReuRcInner<T>.
            // - Initialized: Because all pointers in the `unused` vector have static lifetime from
            // `Box::leak` AND have not been deallocated, they are always initialized.
            // - Aliasing: This allocation either came from a fresh `Box::leak` or the `unused` pool. Newly leaked
            // data has static lifetime and is always safe. The `unused` pool has an invariant of always
            // holding exclusive pointers to initialized objects of static data. As long as that is maintained,
            // this data is allocated.
            let alloc_ref: &'static mut ReuRcInner<T> = unsafe {
                unused_alloc
                    .as_mut()
                    .expect("The allocation pointer should NEVER be null")
            };

            let ref_ct = alloc_ref.ref_ct.get_mut();
            assert_eq!(
                *ref_ct, 0,
                "Nonzero ref count for alloc indicates serious Undefined Behavior"
            );
            init(&mut alloc_ref.contents);
            alloc_ref.incr_ref_ct();
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
        // re-created on `Drop`, and this code never casts a const pointer to a mut pointer.
        // So there do not exist any mutable references to this data at the same time this const
        // reference exists.
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
        // Get an &mut ref to the allocation. Prove its safety.
        // Assert the reference count is 1. Set it to zero.
        // Let the pool reclaim it
        todo!();
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
