# Optional ordinary Bend library

Base: `5925c57febd978d44fa24000233647a59e7898a6` (original reference
`9b751fab3c7c349ff473a2d11a7133573b6c4df2`). No prerequisite experiments merged.
Pinned official Bend 2.0.39 and BendTT are unchanged; `.tools` is an ignored
symlink to the shared immutable installation. All generated artifacts and
application sessions are local under `build/library`.

## Milestones and inventory

The first implementation milestone adds `Value`, `Record`, `Key`, `Int64` and
`Laws`. `Value.Int64`/`integer`/`int_value` preserve every signed64 bit pattern.
`Record.make` rejects invalid, duplicate and unordered fields and nested invalid
values; `Record.fields` reverses raw record construction. `Key.encode` tags each
character and component; `decode` rejects malformed and trailing input. It does
not hash or truncate. `Int64` provides comparison, checked add/sub/increment/
decrement and checked multiply/divmod using two words, with only small loop
indices represented as Nat. Division truncates toward zero, rejects zero and
INT64_MIN/-1, and gives remainder the dividend's sign. `Laws.Safe`, finite-depth
composition and per-field permission obligations are templates, not certificates.

Later milestones (implementation and validation in progress): `Read`, `Sequence`,
`Aggregate`, `Relation`, `Mutation`, `Index`, `Summary`, `TableLaws`; restricted
application flows and native arithmetic oracle. A final inventory and actual
validation results will replace this progress report before completion.

## Proof and validation status

`experiments/library/Foundation.bend` exercises canonical records, delimiter/
Unicode keys, signed arithmetic extrema, carry and borrow. General module laws
cover typed integer and record roundtrips, key segment/arity roundtrip and key
injectivity, accepted arithmetic word result, and CPS finite-depth permissions.
Both official checkers are queued under the shared heavy-test lock; no pass is
claimed before their results arrive. Native, application and final checks remain.

No contract, primitive, compiler, stored scalar domain, canonical limit or
permission grant is changed. Helpers construct ordinary Actions; applications
must prove their own installed laws at every prefix and success publication.
No assumptions or automatic certificates are generated. Performance unmeasured.

## Second checkpoint

All ordinary modules now exist as working implementations. Primary-only checks
pass Foundation, Modules, Behavior and a local generated restricted-user proof
root. `Int64.add_success_under_no_overflow`/`add_rejects_overflow` and corresponding
subtraction equations are nonvacuous two-sided contracts. `signed_success` and
`signed_rejected` cover magnitude conversion, with `mul_success` conditional on
the actual unsigned calculation and its range predicate. These are word-level
API guarantees, not a full signed mathematical arithmetic development.

The task proof now directly instantiates `Laws.reads` and `Laws.write_rows` with
`Policy.Allowed`. Further actual checks remain pending the shared heavy lock.
