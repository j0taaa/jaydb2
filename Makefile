.PHONY: all build verify-contract verify test test-host test-admission test-native test-integration test-library demo demo-web test-demo-web

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

test-admission:
	node --test --test-concurrency=1 tests/admission/*.test.mjs tests/verifier/*.test.mjs

test-native:
	python3 -B tests/native/test_simple_runtime.py

test-integration:
	python3 -B -m unittest tests.service.test_end_to_end tests.service.test_prepared -v

test-library: build
	mkdir -p build/library/tmp
	python3 -B experiments/library/prepare_proofs.py
	python3 -B tools/check.py library/VERIFY.bend build/library/application-proof/Check.bend
	python3 -B experiments/library/test_negative.py
	TMPDIR="$(CURDIR)/build/library/tmp" python3 -B experiments/library/test_arithmetic.py
	TMPDIR="$(CURDIR)/build/library/tmp" python3 -B applications/tasks/query_check.py

demo: build
	bash examples/access/demo.sh

demo-web: build
	python3 -B demo/server.py

test-demo-web: build
	python3 -B -m unittest discover -s tests/demo -v
