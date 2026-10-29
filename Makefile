.PHONY: verify-contract verify test-host test-admission test-native test-integration

verify-contract:
	python3 tools/check.py

verify:
	python3 tools/check.py VERIFICAR.bend
	python3 tools/check.py proof/VERIFICAR.bend tests/proof/VERIFICAR.bend

test-host:
	python3 -B -m unittest tests.service.test_simple_service tests.service.test_delivery tests.service.test_staging tests.service.test_entry tests.service.test_isolated tests.service.test_loading tests.service.test_lifecycle tests.service.test_reentrancy -v

test-admission:
	node --test --test-concurrency=1 tests/admission/*.test.mjs tests/verifier/*.test.mjs

test-native:
	python3 -B tests/native/test_simple_runtime.py

test-integration:
	python3 -B -m unittest tests.service.test_initialization tests.service.test_end_to_end tests.service.test_credentials_end_to_end tests.service.test_swap_end_to_end -v
