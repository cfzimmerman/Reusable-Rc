# Reusable Rc

This crate implements a memory pool from which reusable Rcs can be acquired. On drop, allocations may be returned to the underlying memory pool. This structure can be more efficient than a normal `Rc` when many allocations are created and freed repeatedly. In a release-mode micro-benchmark (see `crate::reu_rc::tests::simple_reuse_flaky()`) in which 10 million instances of both `ReuRc` and `Rc` were created, cloned, and released, the `Rc` loop took `1.268058125` seconds, and the `ReuRc` loop took `123.038834` milliseconds.
