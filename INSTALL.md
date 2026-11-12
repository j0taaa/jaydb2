# Installation and first session

## Tested environment

The current checkout uses the tool profile tested for experimental release
0.1.0: Linux x86_64 (Ubuntu 24.04), Node 24.19, Clang 19, Rust/Cargo 1.98,
and Python 3.12. The service is Rust + Node + Bend
executables; Python is used for installation and the demonstration client.

Check the installed tools:

```sh
node --version
/usr/bin/clang-19 --version
rustc --version
cargo --version
python3 --version
ulimit -Hs
```

The last command must report `unlimited`. The launcher configures the soft
stack limit; a finite hard limit requires a Linux session/profile that permits
that change. This does not modify Bend or Node. Git and GitHub CLI (`gh`) are
used by the download commands below. If the repository requires access,
authenticate `gh` with an authorized account.

## Get the source and Bend tools

```sh
gh repo clone j0taaa/jaydb2
cd jaydb2
git checkout main
mkdir -p .tools/bootstrap
gh release download v0.1.0 --repo j0taaa/jaydb2 \
  --pattern bendtt-linux-x86_64.tar.gz --dir .tools/bootstrap
tar -xzf .tools/bootstrap/bendtt-linux-x86_64.tar.gz -C .tools/bootstrap
python3 tools/bootstrap.py \
  --kernel .tools/bootstrap/bendtt-linux-x86_64/bendtt
python3 tools/bend.py version
make build
```

The download/bootstrap steps above can also be run with
`bash tools/ci/bootstrap.sh`; it wraps the same pinned installer and still
requires authorized `gh` access for the release download. Supplying an existing
kernel path (`bash tools/ci/bootstrap.sh /path/to/bendtt`) avoids that download.
Neither route builds a substitute checker.

The checkout is current English-language `main`; the v0.1.0 release download
is used only for the unchanged pinned BendTT distribution.

Bootstrap downloads and checks the official Bend 2.0.39 sources.
`tools/bend.py` downloads the official distribution and must print
`bend 2.0.39`. Nothing is installed globally. The release's BendTT archive is
JayDB's distribution of the already pinned, unpatched artifact, accompanied by
source and licenses; it is not presented as a binary published by upstream.

The installer requires SHA-256
`e365eba1741602bb45261aa0eb6bd2c6f5db885d4b9d4cd603a27bc3c5a9ed18`
for BendTT. The five sources and Bend executable are also checked against
[toolchain.lock.json](tools/admission/toolchain.lock.json). A different binary
is rejected; installation does not compile a replacement verifier.

If you already have the exact sources and kernel, use:

```sh
python3 tools/bootstrap.py --source /path/to/bend-2.0.39 \
  --kernel /path/to/bendtt
```

## Use the example application

For a persistent Node/TypeScript application, continue with the
[durable quickstart](QUICKSTART.md). It writes a task and reads it after a real
process restart. The command below remains a useful disposable RAM smoke demo.

```sh
make demo
```

This starts a RAM instance with Alice and Bob, sends five requests, and exits
the server after receiving all responses:

```json
{"status": "success", "value": "alice-new"}
{"status": "authentication", "value": null}
{"status": "refusal", "value": "cancelled"}
{"status": "success", "value": "alice-final"}
{"status": "success", "value": "bob-new"}
```

The fourth call uses the third call's credential: the provisional write before
refusal was discarded. The fifth call uses another identity.
[The example](examples/access/README.md) explains the sources and universal
proof. Administrator laws restrict every read and write, including before a
refusal. Existing tests include the forbidden attempt to read another account
and refuse afterward.

Each `make demo` starts from the seed. Exiting loses the RAM instance. This
example neither writes a database to disk nor starts a network listener.

Native programs use the host's available CPU parallelism by default (at most
128 workers), while requests are processed serially. Pass `--threads N` to
`./jaydb2` to select 1–128 workers per native process. `--threads 1` selects single-threaded
execution and can reduce overhead for small sequential programs or when
running many instances. GPU execution is disabled by default; opt in with `--gpu 512` as described below.

For your own application, supply configuration and a seed with a validity
proof, then send programs/proofs through the same stdin/stdout protocol.
[demo.sh](examples/access/demo.sh) shows the complete connection;
`tools/client.py` generates frames and decodes responses. The client's Bend
function accesses data exclusively through database operations.

## Verify the installation

The optional TypeScript client has development dependencies only for building,
type checking and tests. Install them, then run the accessory/host smoke gate:

```sh
npm ci --prefix clients/typescript
make smoke
```

For the complete proof/native/recovery/application release gate, run
`make check-release`. See [verification](docs/verification.md) for prerequisites,
the common heavy-work lock, CI workflows and the precise scope of each gate.
Individual original checks remain available:

```sh
make verify-contract
make verify
make test
```

These commands are separate from the build. `make verify` requires composition
of the eight laws in both official checkers; `make test` exercises the real
integration. Known official runtime limitations are documented in
[SIMPLE_RUNTIME.md](native/SIMPLE_RUNTIME.md). The proof scope and integration
contracts are described in [proof guide](proof/README.md).

Experimental CUDA execution is opt-in with `--gpu 512` (64–4096 MiB). It needs
a Linux NVIDIA device with concurrent managed memory, CUDA driver and NVRTC
headers/libraries visible to `/usr/bin/clang-19` (`cuda.h`, `nvrtc.h`, `-lcuda`,
`-lnvrtc`); the measured system installs these under `/usr`, with no
`/usr/local/cuda` requirement. Official `--gpu-build` prebuilds each device
bundle after proof admission. A requested bang fails without a usable device;
CPU default remains available. See [GPU usage](experiments/gpu/README.md).
