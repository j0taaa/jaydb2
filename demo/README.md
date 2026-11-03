# JayDB2 workbench

**https://jaydb2-demo.jaypussy.site**

A compact administrator workbench for the real `examples/acessos` database.
The adapter runs the Rust executable and official Bend verification/compiler
pipeline. All custom programs and proofs use the existing canonical request
protocol and admission checks.

## Run

Follow [INSTALL.md](../INSTALL.md), then:

```sh
make demo-web
```

Open **http://localhost:8094**. Python 3's standard library is the only web
dependency. For another port: `python3 -B demo/server.py --port 9000`.

## Workbench

- **Data:** all published rows, table/JSON views, state hash, byte size, and
  observation time. “Use” fills the selected row's current credential.
- **Schema:** built-in `usuarios` columns, key, application schema declaration,
  and actual configured canonical byte limits.
- **Laws:** full configuration plus structural validity, credential constraints,
  certificate requirements, and termination definitions.
- **Sources:** the frozen public modules actually used by this instance, its
  environment identity and hashes, original seed, and example client/proof.
- **Request:** editable `Client.bend`, `ClientProof.bend`, credential, and JSON
  arguments. Open local Bend files, load an example, export a draft, or run
  with Ctrl/Command+Enter. Programs/proofs are sent verbatim.
- **Requests:** returned JSON, actual checker diagnostics, exact sent request,
  code and proof, generated `Bindings.bend` and `Instance.bend`, and real
  before/after published state. The last 40 requests are retained in RAM.

The JSON arguments editor is parsed on the server, retaining exact int64
values rather than rounding them through JavaScript numbers. JSON response,
request, and state viewers use server-formatted strings for the same reason.
Unsupported wire values, such as fractional numbers, are rejected before a
request is sent. The database's 32,768-byte canonical message limit applies
to custom code, proof, arguments, and credential together.

The examples are Change credential, Verify credential (an idempotent
write/read using the same client), Write then refuse, and Forbidden read.
Changing the program can require changing its proof. Rejected proofs produce
`certificado` with the real admission diagnostic and leave state unchanged.

## Live administrator inspection

The demo explicitly starts JayDB2 with `--inspect-socket ADMIN_SOCKET`, a
read-only Unix socket in a private directory. At initialization the host
exports the exact canonical bytes it owns, frozen public sources, original
seed source, environment, and limits. After each request it exports the actual
published state and any host/checker error. For authenticated requests it also
exports the actual generated context and source bindings before admission.

The adapter decodes these bytes with the existing wire codec and pushes
snapshots through `/api/events` using Server-Sent Events. It does not infer
state from request arguments or responses, mutate a mirror database, or read
private proposal state. The grid remains responsive during compilation and
changes when a new published snapshot arrives. Other tabs sharing the session
receive the same live stream. Read-only reconnects never replay a transaction.

**This is an administrator capability outside the ordinary client interface.**
It deliberately exposes all rows and example credentials to that instance's
owner. It is opt-in, read-only, and separate from stdin/stdout; workers do not
inherit the socket descriptor. Client programs still have to satisfy the
example's access law. The service-contract proofs do not cover this optional
inspection mode or the web adapter. The normal CLI does not enable it.

Each browser cookie identifies a separate real RAM instance. Refreshes retain
it; resetting, 30 minutes without a session/transaction request, process death,
or a service restart discards it. Event-stream heartbeats do not extend the
idle lifetime. At most eight instances and two simultaneous adapter calls are
retained. Requests to one instance are serialized around its binary pipes.

The adapter's 180-second response watchdog is outside the database contract.
An incomplete response closes the instance; a lost HTTP response can leave
the outcome unknown. Requests are never automatically retried. If inspection
fails, the UI marks the displayed snapshot as stale/unavailable.

## Checks

```sh
cargo test --locked
make test-demo-web
make demo
```

HTTP tests use real database processes and cookie jars, with no mocked DB.
They exercise custom programs/proofs, compiler diagnostics, published-state
streaming during compilation, publication, authentication, rollback, rejected
proofs, uniqueness, Unicode, concurrent requests, instance isolation/reset,
and HTTP boundaries.

## Hosting

The user service assumes this checkout is `~/projects/jaydb2`:

```sh
make build
mkdir -p ~/.config/systemd/user
ln -s "$PWD/demo/jaydb2-demo.service" ~/.config/systemd/user/jaydb2-demo.service
systemctl --user daemon-reload
systemctl --user enable --now jaydb2-demo.service
host-app proxy jaydb2-demo 8094
```

For an installed service, restart after updating Python or the database binary:

```sh
systemctl --user restart jaydb2-demo.service
journalctl --user -u jaydb2-demo.service
```

Static files are served directly from `demo/static`. Both the PC and hosting
gateway must remain online. This administrator playground uses public example
credentials; it is not intended to hold production secrets.
