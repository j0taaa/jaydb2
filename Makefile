.PHONY: all build verify-contract verify test test-host test-admission test-native test-integration test-library demo demo-web test-demo-web test-persistence

all: build

build:
	cargo build --locked --release

# Optional developer accessories; no engine or protocol changes.
.PHONY: test-client test-sql test-sql-native test-sql-stress test-accessories test-accessories-native smoke check-release
test-client:
	npm --prefix clients/typescript run check
	npm --prefix clients/typescript test
	npm --prefix clients/typescript run build

test-sql:
	npm --prefix clients/sql run check
	npm --prefix clients/sql test

# Caller holds the common heavy-work lock. Uses the real official toolchain.
test-sql-native: build
	python3 -B applications/sql/check.py
	npm --prefix clients/sql run test:integration
	npm --prefix clients/sql run test:limits

# Independent SQLite oracle against real native SQL/Drizzle executions.
test-sql-stress: build
	npm --prefix clients/sql run test:stress

test-accessories: test-client test-sql
	clients/typescript/node_modules/.bin/tsc -p applications/tasks/tsconfig.json
	python3 -B -m unittest tests.accessories.test_tasks -v
	python3 -B -m unittest discover -s examples/starter -p test_starter.py -v

# Caller holds the shared heavy-work lock, as for the existing native targets.
test-accessories-native: build test-sql-native test-sql-stress
	npm --prefix clients/typescript run test:integration
	python3 -B examples/starter/check.py --all
	python3 -B -m unittest tests.accessories.test_tasks_native -v

smoke:
	bash tools/ci/check.sh smoke

check-release:
	bash tools/ci/check.sh full

verify-contract:
	python3 -B tools/check.py

verify:
	python3 -B tools/check.py --coverage VERIFY.bend tests/proof/VERIFY.bend library/VERIFY.bend
	python3 -B tests/proof/test_proofs.py

test: build test-admission test-native test-host test-integration

test-host:
	cargo test --locked

# Run under flock /tmp/jaydb2-experiments-heavy.lock, as for other heavy checks.
test-persistence:
	cargo build --locked --release --features storage-fault-injection --target-dir .build/persistence/fault
	mkdir -p .build/persistence/tmp
	TMPDIR="$(CURDIR)/.build/persistence/tmp" JAYDB_PERSISTENCE_BINARY="$(CURDIR)/.build/persistence/fault/release/jaydb2" python3 -B -m unittest tests.service.test_persistence -v

test-admission:
	node --test --test-concurrency=1 tests/admission/*.test.mjs tests/verifier/*.test.mjs

test-native: build
	python3 -B tests/native/test_simple_runtime.py

test-integration: build
	python3 -B -m unittest tests.service.test_end_to_end tests.service.test_prepared tests.service.test_preprocessing tests.service.test_scheduling tests.service.test_timing tests.service.test_observers -v

test-library: build
	mkdir -p build/library/tmp
	TMPDIR="$(CURDIR)/build/library/tmp" python3 -B applications/tasks/query_check.py

demo: build
	bash examples/access/demo.sh

demo-web: build
	python3 -B demo/server.py

test-demo-web: build
	python3 -B -m unittest discover -s tests/demo -v

# Caller must hold /tmp/jaydb2-experiments-heavy.lock, as for other heavy tests.
.PHONY: test-idempotency
test-idempotency: build
	python3 -B applications/vouchers/check.py

# Caller holds the common heavy lock; hooks are absent from normal builds.
.PHONY: test-idempotency-recovery
test-idempotency-recovery:
	cargo build --locked --release --features storage-fault-injection --target-dir .build/idempotency/fault
	mkdir -p .build/idempotency/tmp
	TMPDIR="$(CURDIR)/.build/idempotency/tmp" JAYDB_IDEMPOTENCY_BINARY="$(CURDIR)/.build/idempotency/fault/release/jaydb2" python3 -B -m unittest tests.service.test_receipt_recovery -v

# Existing aggregate reaches Preprocessing, Persistence and the
# extended optional library. Receipts add their independent functional root.
# Caller holds /tmp/jaydb2-experiments-heavy.lock; no nested lock is acquired.
.PHONY: verify-integration test-feature-integration
verify-integration: verify-contract verify
	python3 -B tools/check.py tests/service/ReceiptHelpers.bend

test-feature-integration: build
	python3 -B applications/indexed/run_check.py
	python3 -B tests/service/check_features.py
	python3 -B applications/vouchers/check.py --restart

# One opt-in fault binary for the storage, timing and lost-reply receipt gates.
# Caller holds the shared heavy lock. Use a short TMPDIR for Unix test sockets.
.PHONY: test-recovery-integration
test-recovery-integration:
	cargo build --locked --release --features storage-fault-injection --target-dir .build/integration/fault
	JAYDB_PERSISTENCE_BINARY="$(CURDIR)/.build/integration/fault/release/jaydb2" JAYDB_IDEMPOTENCY_BINARY="$(CURDIR)/.build/integration/fault/release/jaydb2" python3 -B -m unittest tests.service.test_persistence tests.service.test_timing_persistence tests.service.test_receipt_recovery -v

# Standalone prepared-program regression gate; caller holds the common lock.
.PHONY: prepared
prepared: build
	python3 -B -m unittest tests.service.test_prepared -v
