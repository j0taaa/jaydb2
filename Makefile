.PHONY: all build verify-contract verify test test-host test-admission test-native test-integration demo

all: build

build:
	cargo build --locked --release

verify-contract:
	python3 -B tools/check.py

verify:
	python3 -B tools/check.py VERIFICAR.bend tests/proof/VERIFICAR.bend
	python3 -B tests/proof/test_proofs.py

test: test-admission test-native test-host test-integration

test-host:
	cargo test --locked

test-admission:
	node --test --test-concurrency=1 tests/admission/*.test.mjs tests/verifier/*.test.mjs

test-native:
	python3 -B tests/native/test_simple_runtime.py

test-integration:
	python3 -B -m unittest tests.service.test_end_to_end -v

demo: build
	bash examples/acessos/demo.sh
