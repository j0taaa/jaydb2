"""Host ordering fixtures plus real helper/pipe controls for the three-size API.

Fixtures exercise the Python publication boundary, not Bend admission or a
proof of the complete executable. Real admission/execution has separate E2Es.
"""
from dataclasses import FrozenInstanceError
import os
import hashlib
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

from tools.service.controller import (Database, CompileFailure, IncompleteIntegration,
    Published, RequestProposal, NativeFailure, error_frame, helper, packet, build)
from tools.service.lifecycle import LifecycleRuntime
from tools.client import frame
from tests.service.observation import fixture_loading


def response(status):
    return frame({'status': status, 'valor': None})


class Scope:
    def __init__(self):
        self.live_owners = []


class HostFixture(Database):
    def __init__(self, handler=None):
        self._closed = self._fatal = self._channel_ended = self._busy = False
        self._published = Published(b'initial')
        self._request_libraries, self._permanent_libraries = Scope(), Scope()
        self.lifecycle_runtime = SimpleNamespace(live_processes=(), live_leases=(),
                                                has_live_leases=lambda owner: False)
        self.modules = {}
        self.directory = tempfile.TemporaryDirectory(prefix='jaydb-simple-host-fixture-')
        self.limits = dict(mensagem=100, estado=100, resposta=100)
        self.environment = self.toolchain = self.runtime = None
        self.loading_runtime = None
        self.last_failure = None
        self.handler = handler or (lambda body: RequestProposal(error_frame('dados')))

    def _propose_request(self, body):
        return self.handler(body)


class SimpleServiceTests(unittest.TestCase):
    def setUp(self):
        self.db = HostFixture()
        self.addCleanup(self.db.close)

    def test_success_publishes_complete_immutable_pair_once(self):
        reply = response('sucesso')
        self.db.handler = lambda body: RequestProposal(reply, b'new')
        previous = self.db._published
        with patch.object(self.db, '_publish', wraps=self.db._publish) as publish:
            self.assertEqual(self.db.request(b'request'), reply)
        publish.assert_called_once()
        self.assertEqual(previous.state, b'initial')
        self.assertEqual((self.db.state, self.db.published_response), (b'new', reply))
        with self.assertRaises(FrozenInstanceError):
            self.db._published.state = b'changed'
        with self.assertRaises(AttributeError):
            self.db.state = b'changed'

    def test_refusal_preserves_the_original_root(self):
        previous = self.db._published
        self.db.handler = lambda _: RequestProposal(response('recusa'))
        self.db.request(b'x')
        self.assertIs(self.db._published, previous)

    def test_cleanup_precedes_publication(self):
        scope = self.db._request_libraries
        owner = SimpleNamespace()
        owner.close = lambda: scope.live_owners.remove(owner)
        def propose(_):
            scope.live_owners.append(owner)
            return RequestProposal(response('sucesso'), b'new')
        self.db.handler = propose
        def publish(prepared):
            self.assertEqual(scope.live_owners, [])
            Database._publish(self.db, prepared)
        self.db._publish = publish
        self.db.request(b'x')

    def test_pending_cleanup_cannot_publish_or_return_a_public_error(self):
        scope = self.db._request_libraries
        owner = SimpleNamespace(close=Mock(side_effect=OSError('close failed')))
        def propose(_):
            scope.live_owners.append(owner)
            return RequestProposal(response('sucesso'), b'new')
        self.db.handler = propose
        old = self.db._published
        with self.assertRaises(OSError):
            self.db.request(b'x')
        self.assertIs(self.db._published, old)
        with self.assertRaises(IncompleteIntegration):
            self.db.request(b'y')
        owner.close.side_effect = None
        owner.close.side_effect = lambda: scope.live_owners.remove(owner)

    def test_output_lease_prevents_publication_and_unload(self):
        scope = self.db._request_libraries
        owner = SimpleNamespace(close=Mock())
        self.db.lifecycle_runtime.has_live_leases = lambda _: True
        def propose(_):
            scope.live_owners.append(owner)
            return RequestProposal(response('sucesso'), b'new')
        self.db.handler = propose
        with self.assertRaises(IncompleteIntegration):
            self.db.request(b'x')
        owner.close.assert_not_called()
        self.assertEqual(self.db.state, b'initial')
        self.db.lifecycle_runtime.has_live_leases = lambda _: False
        owner.close.side_effect = lambda: scope.live_owners.remove(owner)

    def test_exception_after_store_keeps_published_state_and_response(self):
        reply = response('sucesso')
        self.db.handler = lambda _: RequestProposal(reply, b'committed')
        def interrupt(prepared):
            Database._publish(self.db, prepared)
            raise KeyboardInterrupt()
        self.db._publish = interrupt
        with self.assertRaises(KeyboardInterrupt):
            self.db.request(b'x')
        self.assertEqual((self.db.state, self.db.published_response), (b'committed', reply))
        self.assertFalse(self.db._busy)

    def test_nested_request_is_rejected_without_a_second_proposal(self):
        def propose(_):
            with self.assertRaisesRegex(RuntimeError, 'already processing'):
                self.db.request(b'nested')
            return RequestProposal(response('recusa'))
        self.db.handler = propose
        self.db.request(b'outer')

    def test_mutable_request_is_not_admitted(self):
        self.db.handler = Mock()
        with self.assertRaises(TypeError):
            self.db.request(bytearray(b'x'))
        self.db.handler.assert_not_called()

    def test_live_helper_blocks_the_next_request(self):
        self.db.lifecycle_runtime.live_processes = (object(),)
        with self.assertRaises(IncompleteIntegration):
            self.db.request(b'x')
        self.db.lifecycle_runtime.live_processes = ()

    def test_classifier_distinguishes_dependency_rejection_and_actual_tool_failure(self):
        self.db.handler = lambda b: Database._propose_request(self.db, b)
        for code, status in [('IMPORT_CYCLE', 'certificado'), ('PRIMARY_CHECK', 'certificado'),
                             ('HELPER', 'falha')]:
            with self.subTest(code=code):
                self.db.preprocess = Mock(side_effect=CompileFailure({'code': code}))
                self.assertEqual(self.db.request(b'x'), error_frame(status))
                self.assertEqual(self.db.state, b'initial')

    def test_actual_native_allocation_failure_ends_instance_without_publishing(self):
        self.db.handler = lambda b: Database._propose_request(self.db, b)
        self.db.preprocess = Mock(side_effect=NativeFailure(5, 12))
        self.assertEqual(self.db.request(b'x'), error_frame('falha'))
        self.assertTrue(self.db._fatal)
        self.assertEqual(self.db.state, b'initial')
        with self.assertRaises(RuntimeError):
            self.db.request(b'next')

    def test_python_memory_failure_is_not_reported_as_a_logical_limit(self):
        self.db.handler = lambda b: Database._propose_request(self.db, b)
        self.db.preprocess = Mock(side_effect=MemoryError())
        with self.assertRaises(MemoryError):
            self.db.request(b'x')
        self.assertTrue(self.db._fatal)
        self.assertEqual(self.db.state, b'initial')

    def test_checked_execution_bytes_and_cleanup_reach_the_proposal(self):
        self.db.handler = lambda b: Database._propose_request(self.db, b)
        code, proof, instance, bindings = b'code\x00\n', b'proof\n', b'instance', b'bindings'
        auth = b'\1' + packet(code, packet(proof, packet(instance, bindings)))
        self.db.preprocess = Mock(side_effect=[b'\1', auth])
        reply = response('sucesso')
        module = SimpleNamespace(run=Mock(return_value=b'\1' + packet(b'new', reply)), close=Mock())
        with patch('tools.service.controller.build', return_value=(module, self.db.limits)) as build:
            self.assertEqual(self.db.request(b'body'), reply)
        self.assertEqual(build.call_args.kwargs['metadata'], (code, proof, instance, bindings))
        module.run.assert_called_once_with(packet(b'initial', b'body'), capacity=217)
        module.close.assert_called_once()
        self.assertEqual(self.db.state, b'new')

    def test_invalid_native_transport_cannot_publish(self):
        self.db.handler = lambda b: Database._propose_request(self.db, b)
        self.db.preprocess = Mock(side_effect=[b'\1', b'\1' + packet(b'c', packet(b'p', packet(b'i', b'b')))])
        module = SimpleNamespace(run=Mock(return_value=b'\1' + packet(b'new', b'not-framed')),
                                 close=Mock())
        with patch('tools.service.controller.build', return_value=(module, self.db.limits)):
            self.assertEqual(self.db.request(b'x'), error_frame('falha'))
        module.close.assert_called_once()
        self.assertEqual(self.db.state, b'initial')

    def exchange(self, incoming):
        r, w = os.pipe()
        out, send = os.pipe()
        try:
            os.write(w, incoming)
            os.close(w); w = None
            self.db.serve(r, send)
            os.close(send); send = None
            return os.read(out, 4096)
        finally:
            for fd in (r, w, out, send):
                if fd is not None:
                    os.close(fd)

    def test_complete_invalid_body_allows_the_next_frame(self):
        seen = []
        def propose(body):
            seen.append(body)
            return RequestProposal(response('entrada' if body == b'bad' else 'recusa'))
        self.db.handler = propose
        incoming = b''.join(len(b).to_bytes(8, 'big') + b for b in [b'bad', b'next'])
        self.assertEqual(self.exchange(incoming), error_frame('entrada') + response('recusa'))
        self.assertEqual(seen, [b'bad', b'next'])

    def test_truncated_header_and_body_do_not_invoke_program(self):
        for incoming in (b'\0\0', (3).to_bytes(8, 'big') + b'x'):
            with self.subTest(incoming=incoming):
                self.db.handler = Mock()
                self.assertEqual(self.exchange(incoming), error_frame('entrada'))
                self.db.handler.assert_not_called()

    def test_message_boundary_is_inclusive_and_oversize_is_not_read(self):
        self.db.limits['mensagem'] = 3
        self.db.handler = Mock(return_value=RequestProposal(response('recusa')))
        self.assertEqual(self.exchange((3).to_bytes(8, 'big') + b'abc'), response('recusa'))
        self.db.handler.assert_called_once_with(b'abc')
        self.db.handler.reset_mock()
        self.assertEqual(self.exchange((4).to_bytes(8, 'big')), error_frame('limite'))
        self.db.handler.assert_not_called()

    def test_unknown_read_consumption_disables_channel_without_retry(self):
        with patch('tools.service.controller.exact_read', side_effect=InterruptedError()) as read:
            with self.assertRaises(InterruptedError):
                self.db.serve(123, 456)
        read.assert_called_once()
        with self.assertRaisesRegex(RuntimeError, 'channel is closed'):
            self.db.serve(123, 456)

    def test_close_resolves_owners_before_removing_private_directory(self):
        folder = Path(self.db.directory.name)
        module = SimpleNamespace(close=Mock())
        self.db.modules['decoder'] = module
        self.db.close()
        module.close.assert_called_once()
        self.assertFalse(folder.exists())
        self.assertIsNone(self.db._published)
        with self.assertRaises(RuntimeError):
            self.db.request(b'x')


class ActualHelperTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        fixture_loading()

    def test_actual_helper_drains_both_pipes_and_reaps(self):
        source = 'import os;os.write(2,b"e"*131072);os.write(1,b"x"*131072)'
        self.assertEqual(helper([sys.executable, '-I', '-S', '-c', source]), b'x' * 131072)
        self.assertFalse(LifecycleRuntime.current().live_processes)

    def test_real_nonzero_exit_is_reported_after_cleanup(self):
        with self.assertRaises(CompileFailure):
            helper([sys.executable, '-I', '-S', '-c', 'raise SystemExit(4)'])
        self.assertFalse(LifecycleRuntime.current().live_processes)


class BuildBindingTests(unittest.TestCase):
    """Mutate independent boundaries; positive fixtures do not admit Bend."""
    def exercise(self, *, alter_source=False, alter_loaded_identity=False):
        with tempfile.TemporaryDirectory() as temp:
            folder = Path(temp)
            source = b'#define CID_Native_write 2\n'
            identity = hashlib.sha256(source).hexdigest()
            report = dict(cSha256=identity,
                limits=dict(mensagem='100', estado='100', resposta='100'))
            calls = []
            def compile_helper(command, *args, **kwargs):
                calls.append(command)
                if len(calls) == 1:
                    (folder/'checked.c').write_bytes(source + (b'changed' if alter_source else b''))
                    (folder/'checked.c.json').write_text(json.dumps(report))
            module = SimpleNamespace(report={'sourceSha256': '0'*64 if alter_loaded_identity else identity},
                                     close=Mock())
            with patch('tools.service.controller.helper', side_effect=compile_helper), \
                    patch('tools.service.controller.Module', return_value=module) as load:
                if alter_source or alter_loaded_identity:
                    with self.assertRaisesRegex(RuntimeError, 'C difere|módulo carregado difere'):
                        build(SimpleNamespace(stage=Mock()), folder, 'initialize', ('source', 'kernel'))
                else:
                    loaded, limits = build(SimpleNamespace(stage=Mock()), folder,
                                           'initialize', ('source', 'kernel'))
                    self.assertIs(loaded, module)
                    self.assertEqual(limits, dict(mensagem=100, estado=100, resposta=100))
            return module, calls, load

    def test_changed_emitted_c_is_rejected_before_native_compilation(self):
        _, calls, load = self.exercise(alter_source=True)
        self.assertEqual(len(calls), 1)
        load.assert_not_called()

    def test_loaded_module_must_match_the_checked_emission(self):
        module, calls, _ = self.exercise(alter_loaded_identity=True)
        self.assertEqual(len(calls), 2)
        module.close.assert_called_once()

    def test_write_only_initialization_has_no_invented_read_effect(self):
        module, calls, _ = self.exercise()
        arguments = calls[1]
        self.assertEqual(arguments[arguments.index('--input-cid')+1], 'none')
        self.assertEqual(arguments[arguments.index('--output-cid')+1], 'CID_Native_write')
        self.assertNotIn('--resources-json', arguments)
        module.close.assert_not_called()


if __name__ == '__main__':
    unittest.main(verbosity=2)
