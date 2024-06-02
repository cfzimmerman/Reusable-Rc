use std::{
    cell::{Cell, RefCell},
    fmt::Debug,
    marker::PhantomData,
    mem::size_of,
    rc::Rc,
};

type PoolRef<T> = Rc<RefCell<ReuRcPoolInner<T>>>;

/// To do: great doc comment with example
/// Explain default too.
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

/// Used to specify a pool size limit after which excess
/// memory is freed.
#[derive(Debug, Clone, Copy)]
pub enum PoolSizeLimit {
    /// Limit the pool size to a number of bytes.
    Bytes(usize),
    /// Limit the pool size to a number of objects. Includes the size
    /// of `T` AND all metadata attached to the allocation for `T`.
    ObjCt(usize),
    /// The pool never frees unused memory.
    Unlimited,
}

impl<T> ReuRcPool<T>
where
    T: Default + 'static,
{
    /// Creates a new memory pool from which reusable Rcs can be spawned.
    ///
    /// The `size_limit` parameter provides a way to limit the amount of total
    /// unused memory the pool is permitted to reserve for future use. If
    /// `Unlimited`, the pool will reuse every allocation it makes, giving
    /// the pool a nondecreasing amount of allocated memory of size
    /// equal to the maximum amount of memory ever needed at once.
    ///
    /// If a limit is given, the pool will always yield `ReuRc`
    /// objects (heap permitting) from `spawn`, but memory will be freed when necessary
    /// so that total the amount of unused memory held by the pool never exceed what
    /// is specifiec.
    pub fn new(size_limit: PoolSizeLimit) -> Self {
        let max_num_unused = match size_limit {
            PoolSizeLimit::Bytes(bytes) => Some(bytes / size_of::<ReuRcInner<T>>()),
            PoolSizeLimit::ObjCt(ct) => Some(ct),
            PoolSizeLimit::Unlimited => None,
        };
        ReuRcPool {
            pool: Rc::new(RefCell::new(ReuRcPoolInner {
                unused: Vec::new(),
                max_num_unused,
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
    //
    // Taking `&self` would compile, but using `&mut self` is more explicit to the caller that
    // we're making mutations.
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
            // `Box::leak` and have not been deallocated, they are always initialized.
            // - Aliasing: This allocation either came from a fresh `Box::leak` or the `unused` pool.
            // In both cases, the pointer we now hold is the only pointer or reference in existence
            // to this piece of data, so there cannot be any immutable references that conflict
            // with this mutable reference.
            let alloc_mut = unsafe {
                unused_alloc
                    .as_mut()
                    .expect("The allocation pointer should NEVER be null")
            };

            assert_eq!(
                alloc_mut.ref_ct.get(),
                0,
                "Nonzero ref count from a new alloc indicates serious Undefined Behavior"
            );
            alloc_mut.incr_ref_ct();
            init(&mut alloc_mut.contents);
        }

        // After this exits, zero mutable references or pointers to this type exist, and none will
        // exist until the last RcReu is dropped and the allocation is reclaimed.
        ReuRc {
            alloc: unused_alloc as *const ReuRcInner<T>,
            _alloc: PhantomData,
        }
    }
}

/// A smart pointer wrapping a shared instance of type `T`. It's reference-counted
/// heap memory similar to an `Rc`, but the underlying allocation may be returned
/// to a pool on the final `drop` instead of being freed.
pub struct ReuRc<T>
where
    T: Default + 'static,
{
    alloc: *const ReuRcInner<T>,
    _alloc: PhantomData<ReuRcInner<T>>,
}

impl<T> ReuRc<T>
where
    T: Default + 'static,
{
    /// Retrieve an immutable reference to the shared data.
    #[inline]
    pub fn get(&self) -> &T {
        // Safety:
        // See `spawn` for Alignment and Dereferencable.
        // - Initialized: Assuming the data was initialized at the time of `clone`, the reference
        // count to this data has always been nonzero since then (because of `self`). Because
        // the data can only be deallocated when the reference count is zero, this data must
        // still be initialized.
        // - Aliasing: Mutable pointers to this data are only ever held exclusively in
        // the `unused` vector or briefly before deallocation in `ReuRc::drop`.
        // Because both of those events can only occur when the reference count is zero
        // and the existence of `self` implies that currently it is nonzero, there must
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
        // is never freed or repurposed  as long as the internal `ref_ct` is nonzero. The internal
        // `ref_ct` is nonzero as long as at least one `ReuRc` exists pointing to it. At least one
        // is guaranteed to exist because `self` exists. So, the allocation is just
        // as valid now as when it was created.
        // - Aliasing: We're creating a const reference from a const pointer. Initialization in
        // `spawn` traded this allocation's only pointer for a const pointer. After that, only
        // const pointers exist to the `ReuRcInner`. The exclusive mutable pointer is only ever
        // re-created on `Drop`, so there do not exist any mutable references to this data at
        // the same time this const reference exists.
        {
            unsafe {
                self.alloc
                    .as_ref()
                    .expect("The allocation pointer should NEVER be null")
                    .incr_ref_ct();
            };
        }
        ReuRc {
            alloc: self.alloc,
            _alloc: PhantomData,
        }
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
            // because `self` imples the existence of at least one `ReuRc`, the reference count
            // is nonzero and `alloc` is a valid pointer to an instance of `ReuRcInner<T>`.
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
                // Other references to this data still exist.
                return;
            }

            let mut pool = alloc_ref.pool.borrow_mut();
            let pool_is_full = pool
                .max_num_unused
                .is_some_and(|limit| limit <= pool.unused.len());

            if !pool_is_full {
                // Safety:
                // The early return above is essential. This path is ONLY taken if the reference
                // count is now zero and the memory will be reused.
                // If the reference count is zero, then after this `Drop` there will be no
                // external references to the underlying data. Once `alloc_ref`
                // above and `self.alloc` no longer exist, the pointer below will be the only pointer
                // in existence to this data. After this drop exits, then, the `mut` pointer
                // below can safely be used later as allowed by the aliasing rules.
                pool.unused.push(self.alloc as *mut ReuRcInner<T>);
                return;
            }
        }

        // Safety:
        // The ONLY reason to be here is (1) the reference count is zero and (2) the unused
        // allocation pool is full already.
        // By the safety comments above, assert that there are now zero references or pointers
        // to this data except for the pointer being dropped in `self`. After drop, there will
        // be zero pointers or references in existence. So, freeing this data will not leave
        // any dangling pointers or references after drop.
        // Constructing a Box from the data is safe because because the data was box-leaked
        // in the first place and has not been structurally modified since.
        unsafe {
            let _freed_on_drop = Box::from_raw(self.alloc as *mut ReuRcInner<T>);
        };
    }
}

impl<T> Debug for ReuRc<T>
where
    T: Default + Debug + 'static,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.get().fmt(f)
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
    /// program exits or the value is carefully deallocated.
    fn new(pool: PoolRef<T>) -> *mut Self {
        let leaked: &'static mut Self = Box::leak(Box::new(ReuRcInner {
            pool,
            ref_ct: 0.into(),
            contents: T::default(),
        }));
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

#[cfg(test)]
mod tests {
    use super::ReuRcPool;
    use crate::{PoolSizeLimit, ReuRc, ReuRcInner};
    use std::{collections::HashMap, hint::black_box, mem::size_of, rc::Rc, time::Instant};

    /* For sanitizers
    export RUSTFLAGS=-Zsanitizer=address RUSTDOCFLAGS=-Zsanitizer=address
    */

    /*
    #[test]
    fn verify_sanitizers_are_on() {
        const SIZE: usize = 5;
        let alloc = Box::new([7; SIZE]);
        let ptr = &alloc as *const Box<[i32; SIZE]>;
        drop(alloc);

        let _use_after_free = unsafe { (*ptr)[2] };
        println!("The line above should throw a sanitizer error");
    }
    */

    /// Tests if `ReuRc` can function at the level of a simple `Rc`.
    #[test]
    fn simple_rc() {
        let mut pool: ReuRcPool<Vec<u8>> = ReuRcPool::new(PoolSizeLimit::Unlimited);
        let parent_buf: [u8; 100] = [7; 100];

        let slice = &parent_buf[..10];
        let init = |vector: &mut Vec<u8>| {
            vector.clear();
            vector.extend_from_slice(slice);
        };

        let reu_rc = pool.spawn(init);
        let rr2 = reu_rc.clone();
        let rr3 = rr2.clone();
        let rr4 = rr3.clone();
        drop(rr2);
        let reu_rc_sl = reu_rc.get();

        assert_eq!(reu_rc_sl, slice);
        assert_eq!(reu_rc_sl, rr3.get());
        assert_eq!(reu_rc_sl, rr4.get());
    }

    /// Verifies allocations are efficiently reused.
    #[test]
    fn simple_reuse() {
        const OBJ_CT: usize = 2_000_000;
        let mut pool: ReuRcPool<usize> = ReuRcPool::new(PoolSizeLimit::Unlimited);

        let rc_start = Instant::now();

        for num in 0..OBJ_CT {
            let rc = Rc::new(num);
            black_box(rc.clone());
            black_box(rc);
        }
        let rc_time = rc_start.elapsed();

        let reu_rc_start = Instant::now();
        for num in 0..OBJ_CT {
            let reu_rc = pool.spawn(|mem| *mem = num);
            black_box(reu_rc.clone());
            black_box(reu_rc);
        }
        let reu_rc_time = reu_rc_start.elapsed();

        println!("Time to {OBJ_CT} allocs: rc: {rc_time:?}, reu_rc: {reu_rc_time:?}");
        // assert!(reu_rc_time.as_nanos() < rc_time.as_nanos());
        assert_eq!(pool.pool.borrow().unused.len(), 1);
    }

    /// Forces allocations in exceess of the given pool's object limit, verifying
    /// that allocations are properly freed and the pool remains appropriately sized.
    fn verify_limited(pool: &mut ReuRcPool<usize>) {
        let pool_obj_limit = pool
            .pool
            .borrow()
            .max_num_unused
            .expect("If the pool doesn't have a size limit, then this test is pointless");
        for _ in 0..100 {
            assert!(pool.pool.borrow_mut().unused.len() <= pool_obj_limit);
            {
                let mut refs = Vec::new();
                for num in 0..(pool_obj_limit * 2) {
                    // intentionally letting the first one drop
                    let reu_rc = pool.spawn(|mem| *mem = num);
                    refs.push(reu_rc.clone());
                    refs.push(reu_rc.clone());
                }
                black_box(&refs);
            }
            assert_eq!(pool.pool.borrow_mut().unused.len(), pool_obj_limit);
        }
    }

    /// Verifies object count limitations and deallocation work as expected.
    #[test]
    fn count_limited() {
        const POOL_SIZE: usize = 5;

        let mut pool: ReuRcPool<usize> = ReuRcPool::new(PoolSizeLimit::ObjCt(POOL_SIZE));
        verify_limited(&mut pool);
    }

    /// Verifies byte size limitations and deallocation work as expected.
    #[test]
    fn byte_limited() {
        const POOL_SIZE: usize = 5;

        // The +1 is just to throw things off
        let pool_size_bytes = (size_of::<ReuRcInner<usize>>() * POOL_SIZE) + 1;
        let mut pool: ReuRcPool<usize> = ReuRcPool::new(PoolSizeLimit::Bytes(pool_size_bytes));

        verify_limited(&mut pool);
    }

    /// Creates a group of hash maps that hold `ReuRc<Vec<usize>>` buffers.
    /// For some number of cycles, scans buffers, copies them into `ReuRc` containers,
    /// and inserts them into a map.
    /// Then, calls the callback with the info at the current state.
    /// The intention is to create a fairly complex data flow that would expose any logic
    /// errors or undefined behavior hidden in the implementation.
    fn complex_access(
        cb: impl Fn(
            &mut ReuRcPool<Vec<usize>>,
            &mut Vec<HashMap<(usize, usize), ReuRc<Vec<usize>>>>,
            usize,
            &[usize],
        ),
    ) {
        const OBJS_PER_CYCLE: usize = 10;
        const POOL_MAX_OBJS: usize = (OBJS_PER_CYCLE as f32 * 0.8) as usize;
        const CHUNK_SIZE: usize = 10;

        let mut pool: ReuRcPool<Vec<usize>> = ReuRcPool::new(PoolSizeLimit::ObjCt(POOL_MAX_OBJS));

        let mut maps: Vec<HashMap<(usize, usize), ReuRc<Vec<usize>>>> = vec![HashMap::new(); 8];

        for cycle in 0..100 {
            for (id, chunk) in [cycle; OBJS_PER_CYCLE * CHUNK_SIZE]
                .chunks(CHUNK_SIZE)
                .enumerate()
            {
                let data = pool.spawn(|buf| {
                    buf.clear();
                    buf.extend_from_slice(chunk);
                });
                for map in &mut maps {
                    map.insert((cycle, id), data.clone());
                }
            }
            black_box(&mut maps);

            cb(&mut pool, &mut maps, POOL_MAX_OBJS, &[cycle; CHUNK_SIZE]);
        }
    }

    /// Runs the `complex_access` test with a focus on data living between different
    /// cycles.
    #[test]
    fn complex_access_lifespan() {
        complex_access(|pool, maps, pool_max_objs, _| {
            // Take some values out of the maps arbitrarily. If we choose one to take out, remove
            // it from all the maps so the ReuRc gets deallocated.
            while let Some(target_entry) = maps.first().unwrap().keys().next().copied() {
                if maps.first().unwrap().len() < pool_max_objs / 4 {
                    break;
                }
                for map in maps.iter_mut() {
                    map.remove(&target_entry);
                }
            }

            // Verify that the size limitation is correct and that at least
            // this many values have been deallocated.
            assert_eq!(pool.pool.borrow().unused.len(), pool_max_objs);
        });
    }

    /// Runs the `complex_access` test with a focus on data within allocations.
    #[test]
    fn complex_access_integrity() {
        complex_access(|pool, maps, pool_max_objs, expect_entries| {
            // Verify that all the entries in all the maps have exactly
            // the data they're supposed to.
            for map in maps.iter() {
                for buf in map.values() {
                    assert_eq!(buf.get(), &expect_entries);
                }
            }

            for map in maps.iter_mut() {
                map.clear();
            }

            // The unalloc pool should be completely full right now.
            assert_eq!(pool.pool.borrow().unused.len(), pool_max_objs);
        });
    }
}
