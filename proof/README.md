# General proofs

`proof/VERIFY.bend` aggregates the pure implementation proofs and
`ContractService.contract_of_service`, whose target is exactly
`LAWS.Contract(a,k)`. `tests/proof/VERIFY.bend` reapplies their public
interfaces in quantified laws. The server conclusion is conditional on the
explicit tool and Rust/Node/C integration contracts; their bodies have not
been mechanized in Bend.

- `Foundations`, `Orders`, `Authentication`: structure and authenticated identity.
- `Machine`, `Safety`, `Preparation`, `Publication`: incremental execution,
  administrator laws, and proposal preparation.
- `Call`: existence of actual preparation after finalization, and composition
  of authenticated/certified execution with faithful preparation, valid
  completion, and rollback. It uses actual `Core` functions without assuming
  fidelity or conclusion validity.
- `Representation`, `Transport`, `ReceptionLimits`, `Reification`: bytes, framing,
  and actual arguments.
- `CodecVerify`: 692 laws about the original Codec. `CodecLaw2` proves that
  acceptance reconstructs the exact original encoding, every representable
  encoding within the ceiling is accepted, and the result satisfies
  `Interface.DecodingCorrect`, including rejections.
- `InputVerify`, `Configuration`: composition of actual input,
  authentication, errors, and configuration.
- `Resources`, `AllocationLengths`, `ErrorsFixed`: the three logical sizes and
  length checking before construction. They do not model physical memory or
  deadlines.

## Checking

```sh
make verify
```

This checks hashes of the 18 translated historical files and 14 active
contract modules, checks positive aggregates with separate `--check-only` and
`--verdict` runs, and executes six negative controls that remove distinct
premises: identity, bytes, administrator law, publication, length, and
reification. The runner's timeout only stops stalled development checks.

Old closed examples and prior-run reports were removed from the current
suite; their versions remain in Git. General proofs were not removed to
reduce line counts. The original Portuguese contract remains in Git history;
the on-disk historical archive is an English translation.

## Eight laws and trusted boundary

The [eight-law map](SERVICE_CONTRACT.md) identifies the eight proof terms used
in composition, the actual functions they concern, and five premise groups.
Published-state validity, authenticated identity, and correct publication are
conclusions; none of the eight laws is received as a premise. `Processable`
remains external and is not redefined by the candidate's success.

Composition establishes the kernel and serial protocol. Applying it to the
executable assumes official-tool correctness and refinement of concrete
source, process, pipe, store, and delivery blocks described in the map. Review
and tests support that operational bridge; they are not a mechanized proof of
Rust/Node/C or the complete compiler. Traces omitting real observations and
premises of post-publication validity are not allowed.
