# Lengths before construction

`AllocationLengths.bend` inverts the actual guards in
`Codec.conclude_word` and `open_checked`. For any variable purpose,
u64 counter, stack, remaining body, and remaining ceiling, reaching a
construction state requires the compound check `Fits`. This establishes that
the declared quantity fits **both the body and the ceiling**, without an extra
premise about representable minima or final message acceptance.

This includes prefixes whose content will later be rejected and avoids
relying only on the final-result correctness theorem. Every stack and u64 has
an exact natural measure obtained from existing proofs; compound-minimum
overflow remains a rejection. The rule of eleven minimum bytes per record pair
also establishes the limit on its declared count.

The module emits neither `CheckedLength` nor `AllocatedField`, chooses no
`Environment`, and measures no memory. Native integration must still establish
correspondence between the branches actually executed, original wire position
and quantity, and checking before every partial construction. Fixed-width
primitives need this operational bridge too. Revised Law 2 requires the check
without a physical ceiling; the production Codec function was preserved.

The module and its universal test passed in separate official checker and
kernel processes. Two negative mutations remove the guard requirement and the
body bound respectively; both must be rejected.
