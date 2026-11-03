# Atomic credential swap

Initial state contains Alice (`alice-token`) and Bob (`bob-token`).
`Client.bend`, authenticated with `alice-token`, first writes `bob-token` to
Alice, then `alice-token` to Bob. The first write creates a temporary duplicate.
Final state has unique credentials and can be published.

At the end of the same call, the read uses Alice's initial identity and returns
`bob-token`. On the next call, `Who.bend` identifies `alice-token` as Bob and
`bob-token` as Alice. Optional swap arguments are a list of two new credentials;
leaving them equal at completion produces `data` and discards all changes.

Configuration uses only logical message, state, and response limits, with no
physical budget or per-stage deadline, and explicitly selects zero
administrator laws. Certificates prove technical conditions and termination
for every state/context/argument; there are no built-in role privileges.
Applications may install laws restricting these writes or intermediate states.

```sh
./jaydb2 --configuration examples/credential-exchange/Configuration.bend \
  --seed examples/credential-exchange/Seed.bend
```

`tools/client.py` generates each binary message for the running instance's
stdin. The full test is in `tests/service/test_end_to_end.py`.
