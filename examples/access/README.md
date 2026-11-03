# Access to one's own credential

This configuration installs an access law: throughout execution, reading or
changing the `credential` column is allowed only on the row whose key is the
authenticated identity. It applies at every prefix, including when the program
ends in refusal. All other operations are forbidden.

The seed contains Alice (`alice-token`) and Bob (`bob-token`). With a text
argument, the program writes the current identity's new credential, reads that
same cell, and returns the value read. The next call must use the new
credential. With another argument it provisionally writes and reads its own
cell and refuses; those changes are not published.

`ClientProof.bend` proves sequence permissions for every state and prefix,
publication conditions, and termination. Changing only the row read or written
to another identity's invalidates that proof. Stable-state validity does not
replace permissions for intermediate events.

## Credential-change CLI application

After following [INSTALL.md](../../INSTALL.md), run from the root:

```sh
make demo
```

[demo.sh](demo.sh) uses the existing protocol client and a single real server
instance. Its five calls are:

1. Alice changes `alice-token` to `alice-new`: `success`.
2. The old credential is rejected: `authentication`.
3. Alice requests cancellation: `refusal`; the provisional write of `discarded`
   is not published.
4. `alice-new` still authenticates and publishes `alice-final`.
5. Bob authenticates with `bob-token` and publishes `bob-new` to his own account.

Responses are shown as JSON by `tools/client.py --decode`. This client accepts
all session frames while keeping responses separate. The program, proof, and
database rules remain in this example's Bend files; the script only supplies
requests and connects processes.

To change the sequence, edit the script's `request` calls. The second argument
is JSON: text requests a change; `null` requests refusal. Each script run
restarts Alice and Bob from `Seed.bend`.

The vertical test is in `tests/service/test_end_to_end.py`. It uses real binary
requests, both official checking tools, and executables emitted by the official
compiler.
