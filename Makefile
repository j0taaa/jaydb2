.PHONY: all build verify-contract verify test test-host test-admission test-native test-integration test-library demo demo-web test-demo-web test-persistence

all: build

build:
	cargo build --locked --release

verify-contract:
	python3 -B tools/check.py

verify:
	python3 -B tools/check.py VERIFY.bend tests/proof/VERIFY.bend library/VERIFY.bend
	python3 -B tests/proof/test_proofs.py

test: test-admission test-native test-host test-integration

test-host:
	cargo test --locked

# Run under flock /tmp/jaydb2-experiments-heavy.lock, as for other heavy checks.
test-persistence:
	cargo build --locked --release --features storage-fault-injection --target-dir .build/persistence/fault
	mkdir -p .build/persistence/tmp
	TMPDIR="$(CURDIR)/.build/persistence/tmp" JAYDB_PERSISTENCE_BINARY="$(CURDIR)/.build/persistence/fault/release/jaydb2" python3 -B -m unittest tests.service.test_persistence -v

test-admission:
	node --test --test-concurrency=1 tests/admission/*.test.mjs tests/verifier/*.test.mjs

test-native:
	python3 -B tests/native/test_simple_runtime.py

test-integration:
	python3 -B -m unittest tests.service.test_end_to_end tests.service.test_prepared tests.service.test_preprocessing tests.service.test_scheduling tests.service.test_concurrency -v

test-library:
	python3 -B applications/tasks/query_check.py

demo: build
	bash examples/access/demo.sh

demo-web: build
	python3 -B demo/server.py

test-demo-web: build
	python3 -B -m unittest discover -s tests/demo -v

.PHONY: test-concurrency
test-concurrency: build
	python3 -B -m unittest tests.service.test_concurrency -v
