# Official verifier

JayDB uses the **original Safe and BendTT from Bend 2.0.39**, without changes to rules, quantities, fuel, axioms, or the runtime. Their hashes are recorded in `tools/admission/toolchain.lock.json`.

`checkBook` asks the official `safe_emit` for the payload of the Book already checked by the frontend. `checkKernelFile` runs the original BendTT on that file. There is no alternative kernel, retry with different fuel, or fallback after rejection.

A process failure or representation not implemented by Safe is distinct from a proof rejected by the kernel. JayDB does not rewrite the certificate or supply a replacement witness to obtain acceptance.

Installation only copies the already compiled official kernel and checks its hash:

```sh
python3 tools/bootstrap.py --source /path/to/bend-2.0.39 --kernel /path/to/bendtt
```

The expected kernel has SHA-256 `e365eba1741602bb45261aa0eb6bd2c6f5db885d4b9d4cd603a27bc3c5a9ed18`. Using the database does not require generating a new Lean verifier.

`make verify` checks the general proofs in both official modes. Acceptance of these components alone does not prove the contract of the complete executable.


`startBookCheck` uses the same translator, pinned binary, original CLI/defaults
and verdict parser as the synchronous path. It fixes and hashes the translated
payload before spawning, then resolves with a verdict or infrastructure error
only after child close and log reading. Its private input/log directory remains
owned until completion and is then removed. This allows trusted compilation to
overlap the kernel process; callers must await the result before admission or
artifact release. A failed check never authorizes the speculative output.
