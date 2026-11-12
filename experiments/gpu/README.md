# Experimental GPU programs

Ported from archived `archive/experiment-gpu` (`4ff823d`) and its integration
`ad79983`, adapted to the current checked metadata controller, exact prepared
byte seals, persistence, FIFO scheduler and timing boundary. Old measurements
were deliberately not copied. Current results live in
[the evidence note](../../paper/evidence/gpu-programs.md).

`Client.bend` computes a U32 mixing tree with 64 rounds per leaf.
`HeavyClient.bend` uses depth × 4096 rounds. Depth is the runtime credential
replacement's text length. Both make an explicit `tree!` call after a private
credential write/read; refusal and physical failures must roll that write back.
`ClientProof.bend` proves the same universal restricted-user access and finite
Action obligations for either client. It does not prove the numeric checksum;
independent Python oracles check that separately. Avoid unbounded user inputs
in production: this experiment adds no runtime quota or timeout.

Build and send an ordinary request (all heavy work holds the common lock):

```sh
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; make build'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited;
  python3 tools/client.py --code experiments/gpu/Client.bend \
    --proof examples/access/ClientProof.bend --credential alice-token --arguments '\''"abc"'\'' |
  ./jaydb2 --configuration examples/access/Configuration.bend \
    --seed examples/access/Seed.bend --threads 1 --gpu 512 |
  python3 tools/client.py --decode'
```

To prepare once and submit multiple runtime inputs on the same process:

```sh
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; python3 - <<'\''PY'\''
from pathlib import Path
from tests.service.test_end_to_end import ROOT, Server
code = (ROOT/"experiments/gpu/Client.bend").read_text()
proof = (ROOT/"experiments/gpu/ClientProof.bend").read_text()
server = Server(ROOT/"examples/access", options=["--threads", "1", "--gpu", "512"])
try:
    receipt = server.prepared(0, code, "alice-token", proof=proof)
    assert receipt["status"] == "prepared", (receipt, server.diagnostics())
    handle = receipt["value"]
    print(receipt)
    print(server.prepared(1, handle, "alice-token", "abc"))
    print(server.prepared(1, handle, "abc", "xy"))
    server.finish()
finally:
    server.close()
PY'
```

Replace `--gpu 512` with `--gpu off --threads 16` for the same bang program on
Bend's CPU pool. Initialization/authentication/control remain CPU in either
mode. The GPU report must show nonzero `#define BANGS` in the emitted C and
`hasBangs: true`; a successful non-bang program is not launch evidence.

Run `make test-gpu` and `make benchmark-gpu` directly. They acquire the heavy
lock internally and safely inherit `JAYDB_HEAVY_LOCK_FD` when already locked.
The latter uses the paper's fixed-clock wrapper and writes raw JSON to
`paper/evidence/gpu-programs.json`; it needs Python NumPy for the independent
large-workload oracle. Corpus is 512 MiB. No emitted C or pinned Bend file is
modified. Read the [trusted-base statement](../../proof/README.md#trusted-base)
before interpreting source theorems or performance evidence.
