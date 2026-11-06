# SQL task policy adapter

This directory packages the existing task application's schema, seed, ownership
laws and proof composition for the [SQL frontend](../../clients/sql/README.md).
`prepare.py NEW_DIRECTORY` refuses an existing destination, then copies the
ordinary task modules. It increases the message ceiling for generated
multi-row programs; it does not change any law.

The TypeScript emitter supplies request-specific `Client.bend` source and a
universal certificate through normal preparation. The packaged original
`Client.bend` is not an SQL interpreter or a privileged execution entry.

`check.py` is a development check for the generated certificates in both
official modes. Run it through `make test-sql-native` under the common heavy
test lock, with unlimited stack. See the frontend README for runnable Drizzle
and SQL examples and the exact compatibility limits.
