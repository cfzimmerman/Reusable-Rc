# Reusable Rc

This crate implements a memory pool from which reusable Rcs can be acquired. On drop, allocations may be returned to the underlying memory pool. This structure can be more efficient than a normal `Rc` when many allocations are created and freed repeatedly. In a release-mode micro-benchmark (see `crate::reu_rc::tests::simple_reuse()`) in which 10 million instances of both `ReuRc` and `Rc` were created, cloned, dereferenced, and released, the `Rc` loop took `171.855375 ms`, and the `ReuRc` loop took `91.399458 ms`.
