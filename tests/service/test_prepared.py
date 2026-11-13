"""Universal preparation and native reuse against the real access law."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from tests.service.test_end_to_end import ROOT, Server
from tools.client import encode, prepared_frame, unframe


def universal_access_proof(proof):
    # The existing proof already derives safety for arbitrary ctx,args. Only
    # its final target specializes those values to one concrete request.
    return proof.replace('def B.certificate(s, valid, identity, n):',
        'def B.certificate(ctx, args, s, valid, identity, n):\n  +ctx = ctx\n  +args = args'
        ).replace('I.context()', 'ctx').replace('I.arguments()', 'args')


def checked_worker_result(data):
    """Decode only the private checked route/principal envelope in tests."""
    assert data[0] == 6, data[:32]
    data = data[1:]
    size = int.from_bytes(data[:8], 'big')
    environment = data[8:8+size].decode()
    data = data[8+size:]
    values = []
    for _ in range(2):
        tag, data = data[0], data[1:]
        assert tag in (0, 1)
        if tag:
            size = int.from_bytes(data[:8], 'big')
            values.append(data[8:8+size].decode())
            data = data[8+size:]
        else:
            values.append(None)
    assert data[0] in (0, 1) and data[1] in (0, 1)
    return dict(environment=environment, route=values[0], principal=values[1], matches=bool(data[0]),
        authentication_ready=bool(data[1]), decision=data[2:])


class PreparedTests(unittest.TestCase):
    def server(self, folder, env=None):
        server = Server(folder, env=env)
        self.addCleanup(server.close)
        return server

    def test_reuse_current_identity_state_and_sealed_native_without_admission(self):
        example = ROOT/'examples/access'
        code = (example/'Client.bend').read_text()
        proof = '\uFEFF' + universal_access_proof((example/'ClientProof.bend').read_text())
        with tempfile.TemporaryDirectory(prefix='jaydb-prepared-test-') as temporary:
            folder = Path(temporary)
            # Changing original inputs after preparation cannot change the
            # instance's frozen configuration/dependencies or compiled source.
            (folder/'Size.bend').write_text('import Base\ndef message() -> Nat:\n  32768n\n')
            (folder/'Configuration.bend').write_text('import ./Size.bend as Size\n' +
                (example/'Configuration.bend').read_text().replace('32768n, 65536n', 'Size.message(), 65536n'))
            (folder/'Seed.bend').write_bytes((example/'Seed.bend').read_bytes())
            (folder/'Client.bend').write_text(code)
            (folder/'ClientProof.bend').write_text(proof)
            # Causal gate: this is the real node until disabled. A later
            # ordinary request MUST fail at the same gate, while handle calls
            # continue with no attempt to enter the checker/compiler pipeline.
            node = folder/'node'
            node.write_text('#!/bin/sh\nprintf x >> "$JAYDB_TEST_NODE_LOG"\n'
                'if [ -f "$JAYDB_TEST_NODE_OFF" ]; then echo admission-disabled >&2; exit 91; fi\n'
                'exec "$JAYDB_TEST_NODE" "$@"\n')
            node.chmod(0o700)
            log, disabled = folder/'node-calls', folder/'disable-node'
            env = dict(os.environ, PATH=str(folder)+os.pathsep+os.environ['PATH'],
                JAYDB_TEST_NODE=shutil.which('node'), JAYDB_TEST_NODE_LOG=str(log),
                JAYDB_TEST_NODE_OFF=str(disabled))
            server = self.server(folder, env)
            receipt = server.prepared(0, code, 'alice-token', 'ignored-at-prepare', proof)
            self.assertEqual(receipt['status'], 'prepared', server.diagnostics())
            handle = receipt['value']
            self.assertRegex(handle, r'^[0-9a-f]{64}$')
            # Real official compilation succeeds; consuming an oversized Nat
            # later fails in the native child after its private write.
            failing = code.replace('S.Finish{value}',
                'S.Finish{D.VInt{0, U32.from_nat(Nat.mul(16777216n, 16777216n))}}')
            bad = server.prepared(0, failing, 'alice-token', proof=proof)
            self.assertEqual(bad['status'], 'prepared', server.diagnostics())
            baseline = log.read_bytes()
            disabled.touch()
            for name in ('Configuration.bend', 'Size.bend', 'Seed.bend', 'Client.bend', 'ClientProof.bend'):
                (folder/name).write_text('changed-original-input')

            self.assertEqual(server.prepared(1, handle, 'alice-token', 'alice-new'),
                {'status': 'success', 'value': 'alice-new'}, server.diagnostics())
            self.assertEqual(server.prepared(1, handle, 'bob-token', 'bob-new'),
                {'status': 'success', 'value': 'bob-new'}, server.diagnostics())
            self.assertEqual(server.prepared(1, handle, 'alice-token', 'stale'),
                {'status': 'authentication', 'value': None})
            self.assertEqual(server.prepared(1, handle, 'alice-new'),
                {'status': 'refusal', 'value': 'cancelled'})
            self.assertEqual(server.prepared(1, bad['value'], 'alice-new', 'never-published'),
                {'status': 'failure', 'value': None}, server.diagnostics())
            self.assertIn('a Nat past the largest immediate', server.diagnostics())
            self.assertEqual(server.prepared(1, handle, 'alice-new', 'alice-final'),
                {'status': 'success', 'value': 'alice-final'}, server.diagnostics())

            # Staging files are diagnostic copies after immutable ELF admission.
            # The exact memfd continues to execute despite on-disk mutations.
            private = next(Path(tempfile.gettempdir()).glob(f'jaydb2-{server.process.pid}-*'))
            self.assertFalse((private/'decode').exists(), 'redundant decoder was compiled')
            # Exercise the checked control executable directly with private
            # admission metadata, bypassing Rust's operation handling.
            control = next((private/'control').glob('*.program'))
            control_root = encode({'tables': [], 'users': [
                {'credential': 'token', 'id': 'alice', 'kind': 'user'}]})
            candidate = '1'*64
            def block(first, rest=b''):
                return len(first).to_bytes(8, 'big') + first + rest
            def run_control(registry, opcode, requested, certificate='', mode='universal',
                            admitted_code=code, admitted_proof=proof, credential='token'):
                metadata = encode([candidate, mode, admitted_code, admitted_proof])
                raw = prepared_frame(opcode, requested, credential, proof=certificate)[8:]
                result = subprocess.run([str(control), '+RTS', '--threads', '1', '--gpu', 'off', '-RTS'],
                    input=block(metadata, block(registry, block(control_root, raw))),
                    capture_output=True, timeout=30)
                self.assertEqual(result.returncode, 0, result.stderr.decode())
                return result.stdout
            # Native text ingress: the checked controller owns the full table,
            # including technical defaults and both formerly Rust-only replies.
            certificate_codes = (
                'IMPORT', 'IMPORT_CYCLE', 'DEPENDENCY', 'PARSE', 'META', 'UNSAFE',
                'FOREIGN', 'IO', 'OPEN_LAW', 'SHADOW', 'REDEFINITION',
                'PRIMARY_CHECK', 'BENDTT_CHECK', 'TARGET', 'SOURCE_BINDING',
                'HOST_CAPTURE', 'KERNEL_CAPTURE')
            for error_code in (*certificate_codes, 'HOST_COMPILE', 'HANDLE',
                               'PREPARED_INTEGRITY', 'NATIVE', '', 'parse', 'FUTURE_CODE'):
                with self.subTest(error_code=error_code):
                    result = subprocess.run(
                        [str(control), '+RTS', '--threads', '1', '--gpu', 'off', '-RTS'],
                        input=block(encode(error_code), block(b'', block(control_root))),
                        capture_output=True, timeout=30)
                    self.assertEqual(result.returncode, 0, result.stderr.decode())
                    status = 'certificate' if error_code in certificate_codes else 'failure'
                    expected = encode({'status': status, 'value': None})
                    self.assertEqual(result.stdout, b'\0' + block(expected))
            def split_control(data):
                size = int.from_bytes(data[:8], 'big')
                return data[8:8+size], data[8+size:]
            for mode, admitted_code, admitted_proof in (
                    ('concrete', code, proof), ('universal', code+'x', proof),
                    ('universal', code, proof+'x')):
                denial = run_control(b'', 0, code, proof, mode, admitted_code, admitted_proof)
                self.assertEqual(denial[0], 0)
                self.assertEqual(unframe(denial[1:])['status'], 'certificate')
            # Inner canonical body fits exactly; the two extension octets
            # alone put the original body above the configured 32768 limit.
            base_size = len(prepared_frame(0, '', 'token')) - 8
            prefix_overflow = 'x'*(32768-base_size+2)
            denied = run_control(b'', 0, prefix_overflow)
            self.assertEqual(unframe(denied[1:])['status'], 'limit')
            added = run_control(b'', 0, code, proof)
            self.assertEqual(added[0], 1)
            returned_handle, rest = split_control(added[1:])
            live_registry, receipt_bytes = split_control(rest)
            self.assertEqual(returned_handle.decode(), candidate)
            self.assertEqual(unframe(receipt_bytes), {'status': 'prepared', 'value': candidate})
            self.assertEqual(unframe(run_control(live_registry, 0, code, proof)[1:])['status'], 'failure')
            removed = run_control(live_registry, 2, candidate)
            self.assertEqual(removed[0], 3)
            _, rest = split_control(removed[1:])
            dead_registry, receipt_bytes = split_control(rest)
            self.assertEqual(unframe(receipt_bytes), {'status': 'invalidated', 'value': None})
            self.assertEqual(unframe(run_control(dead_registry, 0, code, proof)[1:])['status'], 'failure')
            self.assertEqual(unframe(run_control(dead_registry, 2, candidate)[1:])['status'], 'failure')
            foreign = encode([[['other-instance', candidate, code, proof, False, '']], []])
            self.assertEqual(unframe(run_control(foreign, 2, candidate)[1:])['status'], 'failure')
            self.assertEqual(unframe(run_control(foreign, 0, code, proof)[1:])['status'], 'failure')
            prepared = next(p for p in private.glob('request-*') if (p/'Client.bend').read_text() == code)
            self.assertIn('Worker.routed_bytes(', (prepared/'Main.bend').read_text())
            self.assertIn('Bindings.proof_source()', (prepared/'Main.bend').read_text())
            # Exercise Resolve/Gate in the compiled worker directly, bypassing
            # Rust's artifact selection. Only the checked registry and the
            # artifact's frozen source/proof may authorize execution.
            root = encode({'tables': [], 'users': [
                {'credential': 'alice-token', 'id': 'alice', 'kind': 'user'}]})
            def private_packet(first, rest):
                return len(first).to_bytes(8, 'big') + first + rest
            executable = next(prepared.glob('*.program'))
            # The outer prefix parser deliberately defers the suffix scan.
            # Actual compiled workers must still reject incomplete nested
            # frames and malformed private roots before producing metadata.
            raw = prepared_frame(1, candidate, 'alice-token')[8:]
            for label, bad_packet in (
                    ('empty-outer', b''),
                    ('short-outer-header', bytes(7)),
                    ('outer-prefix-truncated', (2**64-1).to_bytes(8, 'big') + live_registry),
                    ('short-inner-header', private_packet(live_registry, bytes(7))),
                    ('inner-prefix-truncated', private_packet(live_registry,
                        (2**64-1).to_bytes(8, 'big') + root + raw)),
                    ('invalid-root', private_packet(live_registry, private_packet(root[:-1], raw))),
                    ('extra-root-byte', private_packet(live_registry, private_packet(root + b'\x00', raw)))):
                with self.subTest(private_transport=label):
                    worker = subprocess.run([str(executable), '+RTS', '--threads', '1', '--gpu', 'off', '-RTS'],
                        input=bad_packet, capture_output=True, timeout=30, check=True)
                    self.assertEqual(worker.stdout, b'\x02', worker.stderr.decode())
            mismatched_code = run_control(b'', 0, failing, proof, admitted_code=failing)
            _, rest = split_control(mismatched_code[1:])
            wrong_program_registry, _ = split_control(rest)
            mismatched_proof = run_control(b'', 0, code, proof+'x', admitted_proof=proof+'x')
            _, rest = split_control(mismatched_proof[1:])
            wrong_proof_registry, _ = split_control(rest)
            # Deliberately locate this executable as Rust's map would, then
            # feed independent checked controller results. Registry authority
            # must survive stale/incorrect artifact selection by the host.
            for registry, requested, credential, supplied_proof, status in (
                    (live_registry, candidate, 'alice-token', '', 'refusal'),
                    (live_registry, 'missing-handle', 'alice-token', '', 'failure'),
                    (live_registry, candidate, 'alice-token', 'not-empty', 'input'),
                    (live_registry, 'missing-handle', 'invalid', 'not-empty', 'authentication'),
                    (dead_registry, candidate, 'alice-token', '', 'failure'),
                    (b'', candidate, 'alice-token', '', 'failure'),
                    (b'malformed-registry', candidate, 'alice-token', '', 'failure'),
                    (foreign, candidate, 'alice-token', '', 'failure'),
                    (wrong_program_registry, candidate, 'alice-token', '', 'failure'),
                    (wrong_proof_registry, candidate, 'alice-token', '', 'failure')):
                with self.subTest(registry=registry[:30], requested=requested, status=status):
                    raw = prepared_frame(1, requested, credential, 'must-not-publish', supplied_proof)[8:]
                    # Successful matching selection can commit; use a refusal
                    # argument to test its Keep path alongside the denials.
                    if status == 'refusal':
                        raw = prepared_frame(1, requested, credential, proof=supplied_proof)[8:]
                    worker = subprocess.run([str(executable), '+RTS', '--threads', '1', '--gpu', 'off', '-RTS'],
                        input=private_packet(registry, private_packet(root, raw)),
                        capture_output=True, timeout=30)
                    self.assertEqual(worker.returncode, 0, worker.stderr.decode())
                    checked = checked_worker_result(worker.stdout)
                    self.assertEqual(checked['route'], requested)
                    self.assertTrue(checked['authentication_ready'])
                    self.assertEqual(checked['matches'], registry not in (wrong_program_registry, wrong_proof_registry))
                    self.assertEqual(checked['principal'], 'alice' if credential == 'alice-token' and not supplied_proof else None)
                    decision = checked['decision']
                    self.assertEqual(decision[0], 0, 'early result must be Keep')
                    self.assertEqual(unframe(decision[1:])['status'], status)
            # All tag-0 authenticator outcomes must equal the complete Keep
            # payload of the prepared worker, including opcode-inclusive bounds.
            authenticator = next((private/'authenticate').glob('*.program'))
            cases = [('empty', b''), ('invalid-opcode', b'\x07\xff'),
                ('truncated-extension', b'\x07'), ('malformed-envelope', b'\x07\x01\xff'),
                ('over-limit', b'\x07\x01'+bytes(32768))]
            for label, credential, requested, raw_proof, args, op in [
                ('valid', 'alice-token', candidate, '', None, 1),
                ('empty-credential', '', candidate, '', None, 1),
                ('bad-credential', 'revoked-token', candidate, '', None, 1),
                ('nonempty-proof', 'alice-token', candidate, 'bad', None, 1),
                ('bad-credential-proof', 'bad', candidate, 'bad', None, 1),
                ('unknown-handle', 'alice-token', 'f'*64, '', None, 1),
                ('malformed-handle', 'alice-token', '?', '', None, 1),
                ('bad-credential-unknown-handle', 'bad', 'f'*64, '', None, 1),
                ('invalid-arguments', 'alice-token', candidate, '', [], 1),
                ('invalidation-control', 'alice-token', candidate, '', None, 2)]:
                cases.append((label, prepared_frame(op, requested, credential, args, raw_proof)[8:]))
            early_count = 0
            for label, raw in cases:
                with self.subTest(early_matrix=label):
                    def run_native(program, private_input):
                        result = subprocess.run([str(program), '+RTS', '--threads', '1', '--gpu', 'off', '-RTS'],
                            input=private_input, capture_output=True, timeout=30, check=True)
                        return result.stdout
                    authenticated = run_native(authenticator, private_packet(root, raw))
                    checked = checked_worker_result(run_native(executable,
                        private_packet(live_registry, private_packet(root, raw))))
                    self.assertTrue(checked['authentication_ready'])
                    if authenticated[0] == 0:
                        early_count += 1
                        self.assertEqual(checked['decision'], authenticated)
                        self.assertIsNone(checked['principal'])
                    if label == 'invalidation-control':
                        self.assertEqual(authenticated[0], 5)
                        self.assertIsNone(checked['route'])
                        self.assertEqual(unframe(checked['decision'][1:])['status'], 'input')
            self.assertEqual(early_count, 10)
            for label, users, principal, status in [
                ('authenticated-empty-id', [dict(credential='alice-token', id='', kind='user')], '', 'refusal'),
                ('revoked-credential-current-root', [], None, 'authentication')]:
                with self.subTest(current_identity=label):
                    current = encode(dict(tables=[], users=users))
                    raw = prepared_frame(1, candidate, 'alice-token')[8:]
                    checked = checked_worker_result(run_native(executable,
                        private_packet(live_registry, private_packet(current, raw))))
                    self.assertEqual(checked['principal'], principal)
                    self.assertEqual(checked['decision'][0], 0)
                    self.assertEqual(unframe(checked['decision'][1:])['status'], status)

            # Compare exact public bytes at the same published root. Map-miss
            # detection remains a physical host duty; its denial
            # bytes now come from the separately checked native controller.
            current_root = encode({'tables': [], 'users': [
                {'credential': 'alice-final', 'id': 'alice', 'kind': 'user'},
                {'credential': 'bob-new', 'id': 'bob', 'kind': 'user'}]})
            def checked_missing_reply(requested):
                raw = prepared_frame(1, requested, 'alice-final', 'tampered')[8:]
                result = subprocess.run([str(executable), '+RTS', '--threads', '1', '--gpu', 'off', '-RTS'],
                    input=private_packet(dead_registry, private_packet(current_root, raw)),
                    capture_output=True, timeout=30)
                self.assertEqual(result.returncode, 0, result.stderr.decode())
                checked = checked_worker_result(result.stdout)
                self.assertEqual(checked['principal'], 'alice')
                decision = checked['decision']
                self.assertEqual(decision[0], 0, 'not-found denial must be Keep')
                self.assertEqual(unframe(decision[1:]), {'status': 'failure', 'value': None})
                return decision[1:]
            def host_reply(requested):
                server.process.stdin.write(prepared_frame(1, requested, 'alice-final', 'alice-final'))
                server.process.stdin.flush()
                header = server.read(8)
                return header + server.read(int.from_bytes(header, 'big'))
            not_found_reply = checked_missing_reply('missing-handle')
            self.assertEqual(host_reply('missing-handle'), not_found_reply, server.diagnostics())
            absent_registration_reply = checked_missing_reply(handle)
            for source in prepared.rglob('*.bend'):
                self.assertNotIn('alice-token', source.read_text())
                self.assertNotIn('bob-token', source.read_text())
            self.assertFalse(list(private.rglob('Seed.bend')))
            offline_control = control.with_suffix('.offline')
            control.rename(offline_control)
            diagnostic_start = len(server.diagnostics())
            try:
                self.assertEqual(host_reply('missing-handle'), not_found_reply)
                for artifact in (next(prepared.glob('*.program')), next(prepared.glob('*.program.json')),
                                 next((private/'authenticate').glob('*.program')), prepared/'Client.bend',
                                 prepared/'Size.bend', private/'runtime/tools/service/stage.mjs'):
                    original = artifact.read_bytes()
                    try:
                        artifact.write_bytes(b'corrupt staged ELF' if artifact.suffix == '.program'
                                             else original+b'\nchanged')
                        # A refill must also execute the admitted fd after this
                        # destructive mutation, not reopen the staging path.
                        for _ in range(2):
                            self.assertEqual(unframe(host_reply(handle)),
                                {'status': 'success', 'value': 'alice-final'}, server.diagnostics())
                        if artifact == private/'runtime/tools/service/stage.mjs':
                            # Future admissions must reject modified shared inputs,
                            # before invoking even the disabled Node/checker path.
                            self.assertEqual(server.prepared(0, code, 'alice-final', proof=proof),
                                {'status': 'failure', 'value': None})
                            self.assertIn('frozen compilation input changed', server.diagnostics())
                            self.assertEqual(log.read_bytes(), baseline)
                    finally:
                        artifact.write_bytes(original)
                self.assertEqual(server.prepared(1, handle, 'alice-final', 'alice-final'),
                    {'status': 'success', 'value': 'alice-final'})
                diagnostics = server.diagnostics()[diagnostic_start:]
                self.assertEqual(diagnostics.count('checked denial memo hit: HANDLE'), 1)
                self.assertEqual(diagnostics.count('checked denial memo hit: PREPARED_INTEGRITY'), 1)
                self.assertNotIn('launching denial controller', diagnostics,
                    'prepared denials attempted to launch the offline controller')
                self.assertEqual(log.read_bytes(), baseline, 'prepared route entered node')
                # The controller also runs its sealed image after its staging
                # path is renamed; an uncached error still gets checked bytes.
                self.assertEqual(server.call(code, (example/'ClientProof.bend').read_text(), 'alice-final'),
                    {'status': 'failure', 'value': None})
                self.assertNotEqual(log.read_bytes(), baseline, 'causal admission gate was not reached')
                diagnostics = server.diagnostics()[diagnostic_start:]
                self.assertIn('admission-disabled', diagnostics)
                self.assertIn('launching denial controller for exact code: HELPER', diagnostics)
                self.assertNotIn('denial controller failed for HELPER:', diagnostics)
                self.assertNotIn('using technical failure fallback (not memoized)', diagnostics)
            finally:
                offline_control.rename(control)

            other = self.server(example)
            self.assertEqual(other.prepared(1, handle, 'alice-token', 'foreign'),
                {'status': 'failure', 'value': None})
            self.assertEqual(other.call(code, (example/'ClientProof.bend').read_text(), 'alice-token', 'other-new'),
                {'status': 'success', 'value': 'other-new'}, other.diagnostics())
            self.assertEqual(server.prepared(2, handle, 'invalid'), {'status': 'authentication', 'value': None})
            # Authentication wins over both unknown handles and bad proof
            # fields, while malformed envelopes still win over authentication.
            for operation in (0, 1, 2):
                self.assertEqual(server.prepared(operation, 'absent', 'invalid', proof='bad proof'),
                    {'status': 'authentication', 'value': None})
                malformed = bytes((7, operation)) + encode({'credential': 'invalid'})
                self.assertEqual(server.exchange(len(malformed).to_bytes(8, 'big')+malformed),
                    {'status': 'input', 'value': None})
            self.assertEqual(server.prepared(1, handle, 'alice-final', proof='replacement'),
                {'status': 'input', 'value': None})
            for operation in (3, 9):
                unknown = bytes((7, operation)) + encode(dict(code=code, proof=proof,
                    credential='alice-final', arguments=None))
                self.assertEqual(server.exchange(len(unknown).to_bytes(8, 'big')+unknown),
                    {'status': 'input', 'value': None})
            self.assertEqual(server.prepared(2, handle, 'alice-final'), {'status': 'invalidated', 'value': None})
            self.assertEqual(host_reply(handle), absent_registration_reply, server.diagnostics())
            self.assertEqual(server.prepared(1, bad['value'], 'alice-final'),
                {'status': 'refusal', 'value': 'cancelled'})
            # Cleanup cannot turn a checked, irrevocable removal into denial.
            # Rename the artifact to make deletion of its old path fail.
            bad_directory = next(p for p in private.glob('request-*')
                if (p/'Client.bend').read_text() == failing)
            bad_directory.rename(bad_directory.with_name(bad_directory.name+'-moved'))
            self.assertEqual(server.prepared(2, bad['value'], 'alice-final'),
                {'status': 'invalidated', 'value': None}, server.diagnostics())
            self.assertIn('invalidated artifact cleanup', server.diagnostics())
            self.assertEqual(server.prepared(1, bad['value'], 'alice-final'),
                {'status': 'failure', 'value': None})
            # The inner record alone fits exactly. Its two control bytes must
            # still trigger the host's terminal message-limit response.
            empty = prepared_frame(1, handle, 'alice-final', '')
            oversized = prepared_frame(1, handle, 'alice-final', 'x'*(32768-(len(empty)-10)))
            self.assertEqual(len(oversized)-8, 32770)
            self.assertEqual(server.exchange(oversized[:8]), {'status': 'limit', 'value': None})
            other.finish()
            server.finish()

    def test_preparation_requires_universal_proof_and_pure_capture_free_sources(self):
        folder = ROOT/'examples/access'
        code, concrete = ((folder/name).read_text() for name in ('Client.bend', 'ClientProof.bend'))
        proof = universal_access_proof(concrete)
        server = self.server(folder)
        cases = [
            (code, concrete, 'HOST_CAPTURE'),
            (code.replace('D.ReadCell{D.Users{}, id,', 'D.ReadCell{D.Users{}, "bob",'), proof, 'PRIMARY_CHECK'),
            ('import ./Instance.bend as Captured\n'+code+
                '\ndef capture() -> D.Context:\n  Captured.context()\n', proof, 'HOST_CAPTURE'),
            ('import ./Instance.bend as Captured\n'+code+
                '\ndef capture() -> D.Value:\n  Captured.arguments()\n', proof, 'HOST_CAPTURE'),
            ('import ./Absent.bend as Absent\n'+code, proof, 'DEPENDENCY'),
            (code+'\ndef foreign() -> Unit:\n  import "./foreign.c"\n', proof, 'FOREIGN'),
        ]
        for source, certificate, diagnostic in cases:
            with self.subTest(diagnostic=diagnostic):
                before = len(server.diagnostics())
                self.assertEqual(server.prepared(0, source, 'alice-token', proof=certificate),
                    {'status': 'certificate', 'value': None}, server.diagnostics())
                self.assertIn(diagnostic, server.diagnostics()[before:])
        # A failed preparation has never invoked the client or changed state.
        self.assertEqual(server.call(code, concrete, 'alice-token', 'ordinary-new'),
            {'status': 'success', 'value': 'ordinary-new'}, server.diagnostics())
        server.finish()

        with tempfile.TemporaryDirectory(prefix='jaydb-prepared-response-') as temporary:
            narrow = Path(temporary)
            (narrow/'Configuration.bend').write_text((folder/'Configuration.bend').read_text().replace(
                'S.Limits{32768n, 65536n, 32768n}', 'S.Limits{32768n, 65536n, 64n}'))
            (narrow/'Seed.bend').write_bytes((folder/'Seed.bend').read_bytes())
            small = self.server(narrow)
            refused = small.prepared(0, code, 'alice-token', proof=proof)
            self.assertEqual(refused, {'status': 'limit', 'value': None}, small.diagnostics())
            self.assertLessEqual(len(encode(refused)), 64)
            private = next(Path(tempfile.gettempdir()).glob(f'jaydb2-{small.process.pid}-*'))
            self.assertFalse(list(private.glob('request-*')), 'oversized receipt registered a worker')
            self.assertEqual(small.call(code, concrete, 'alice-token', 'x'),
                {'status': 'success', 'value': 'x'}, small.diagnostics())
            small.finish()


if __name__ == '__main__':
    unittest.main(verbosity=2)
