"""Host publication, framing and artifact identity; no native-budget fixtures."""
from dataclasses import FrozenInstanceError
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import MagicMock, Mock, patch

from tools.client import frame
from tools.service.controller import (Database, CompileFailure, Published,
    RequestProposal, NativeFailure, error_frame, helper, packet, build)


def response(status):
    return frame({'status': status, 'valor': None})


class HostFixture(Database):
    def __init__(self):
        self._closed = self._fatal = self._channel_ended = self._busy = False
        self._published = Published(b'initial')
        self.directory = tempfile.TemporaryDirectory(prefix='jaydb-host-test-')
        self.limits = dict(mensagem=100, estado=100, resposta=100)
        self.modules = {}
        self.environment = self.toolchain = self.runtime = self.last_failure = None
        self.handler = lambda _: RequestProposal(response('recusa'))

    def _propose_request(self, body):
        return self.handler(body)


class HostTests(unittest.TestCase):
    def setUp(self):
        self.db = HostFixture()
        self.addCleanup(self.db.close)

    def test_success_publishes_one_immutable_state_response_pair(self):
        # Only a complete success proposal may replace the published root.
        old, reply = self.db._published, response('sucesso')
        self.db.handler = lambda _: RequestProposal(reply, b'new')
        with patch.object(self.db, '_publish', wraps=self.db._publish) as publish:
            self.assertEqual(self.db.request(b'x'), reply)
        publish.assert_called_once()
        self.assertEqual(old.state, b'initial')
        self.assertEqual((self.db.state, self.db.published_response), (b'new', reply))
        with self.assertRaises(FrozenInstanceError):
            self.db._published.state = b'changed'

    def test_refusal_and_certificate_failure_preserve_root(self):
        # Refusals and mathematical rejections cannot publish a new state.
        old = self.db._published
        self.assertEqual(self.db.request(b'x'), response('recusa'))
        self.assertIs(self.db._published, old)
        self.db.handler = lambda body: Database._propose_request(self.db, body)
        self.db.preprocess = Mock(side_effect=CompileFailure({'code': 'PRIMARY_CHECK'}))
        self.assertEqual(self.db.request(b'x'), error_frame('certificado'))
        self.assertIs(self.db._published, old)

    def test_execution_uses_exact_authenticated_bytes_and_closes_before_publish(self):
        # Native execution consumes the authenticated metadata, then releases
        # its module before the proposal reaches the publication store.
        self.db.handler = lambda body: Database._propose_request(self.db, body)
        code, proof, instance, bindings = b'code\0\n', b'proof', b'instance', b'bindings'
        auth = b'\1' + packet(code, packet(proof, packet(instance, bindings)))
        self.db.preprocess = Mock(side_effect=[b'\1', auth])
        reply = response('sucesso')
        module = MagicMock()
        module.__enter__.return_value = module
        module.run.return_value = b'\1' + packet(b'new', reply)
        def publish(prepared):
            module.__exit__.assert_called_once()
            Database._publish(self.db, prepared)
        self.db._publish = publish
        with patch('tools.service.controller.build', return_value=(module, self.db.limits)) as compile:
            self.assertEqual(self.db.request(b'body'), reply)
        self.assertEqual(compile.call_args.kwargs['metadata'], (code, proof, instance, bindings))
        module.run.assert_called_once_with(packet(b'initial', b'body'), capacity=217)

    def test_invalid_native_framing_cannot_publish(self):
        # Correct publication flags do not authorize an invalid framed response.
        self.db.handler = lambda body: Database._propose_request(self.db, body)
        self.db.preprocess = Mock(side_effect=[b'\1', b'\1' + packet(b'c', packet(b'p', packet(b'i', b'b')))])
        module = MagicMock()
        module.__enter__.return_value = module
        module.run.return_value = b'\1' + packet(b'new', b'not-framed')
        with patch('tools.service.controller.build', return_value=(module, self.db.limits)):
            self.assertEqual(self.db.request(b'x'), error_frame('falha'))
        module.__exit__.assert_called_once()
        self.assertEqual(self.db.state, b'initial')

    def test_actual_native_failure_preserves_state_and_ends_instance(self):
        # Allocation failure is infrastructure, not a logical byte limit.
        self.db.handler = lambda body: Database._propose_request(self.db, body)
        self.db.preprocess = Mock(side_effect=NativeFailure(5, 12))
        self.assertEqual(self.db.request(b'x'), error_frame('falha'))
        self.assertEqual(self.db.state, b'initial')
        with self.assertRaises(RuntimeError):
            self.db.request(b'next')

    def exchange(self, incoming):
        read, write = os.pipe()
        try:
            os.write(write, incoming)
            os.close(write)
            write = None
            with tempfile.TemporaryFile() as output:
                self.db.serve(read, output.fileno())
                output.seek(0)
                return output.read()
        finally:
            os.close(read)
            if write is not None:
                os.close(write)

    def test_complete_invalid_body_preserves_the_next_frame(self):
        # A complete rejected frame has a known extent; the next frame survives.
        seen = []
        def propose(body):
            seen.append(body)
            return RequestProposal(response('entrada' if body == b'bad' else 'recusa'))
        self.db.handler = propose
        data = b''.join(len(body).to_bytes(8, 'big') + body for body in (b'bad', b'next'))
        self.assertEqual(self.exchange(data), error_frame('entrada') + response('recusa'))
        self.assertEqual(seen, [b'bad', b'next'])

    def test_inclusive_size_boundary_and_truncated_body(self):
        # Size is checked from the header; a truncated body never reaches code.
        self.db.limits['mensagem'] = 3
        self.db.handler = Mock(return_value=RequestProposal(response('recusa')))
        self.assertEqual(self.exchange((3).to_bytes(8, 'big') + b'abc'), response('recusa'))
        self.db.handler.assert_called_once_with(b'abc')
        self.db.handler.reset_mock()
        for incoming, status in (((4).to_bytes(8, 'big'), 'limite'),
                                 ((3).to_bytes(8, 'big') + b'x', 'entrada')):
            self.assertEqual(self.exchange(incoming), error_frame(status))
        self.db.handler.assert_not_called()

    def test_delivery_failure_after_publication_does_not_roll_back(self):
        # Publication precedes delivery, including an actual broken output pipe.
        read, write = os.pipe()
        sink_read, sink_write = os.pipe()
        try:
            os.write(write, (1).to_bytes(8, 'big') + b'x')
            os.close(write); write = None
            os.close(sink_read); sink_read = None
            self.db.handler = lambda _: RequestProposal(response('sucesso'), b'committed')
            with self.assertRaises(BrokenPipeError):
                self.db.serve(read, sink_write)
            self.assertEqual(self.db.state, b'committed')
            with self.assertRaisesRegex(RuntimeError, 'closed'):
                self.db.serve(read, sink_write)
        finally:
            for fd in (read, write, sink_read, sink_write):
                if fd is not None:
                    os.close(fd)

    def test_helper_drains_both_pipes_and_reports_exit_failure(self):
        # More than one pipe buffer on each stream must not deadlock a helper.
        command = [sys.executable, '-I', '-S', '-c']
        self.assertEqual(helper(command + ['import os;os.write(2,b"e"*131072);os.write(1,b"x"*131072)']), b'x'*131072)
        with self.assertRaises(CompileFailure):
            helper(command + ['raise SystemExit(4)'])


class BuildBindingTests(unittest.TestCase):
    def test_checked_emission_and_loaded_descriptor_must_match(self):
        # Exercise both independent identity checks; neither checksum proves C.
        for changed_source, changed_module in ((True, False), (False, True), (False, False)):
            with self.subTest(source=changed_source, module=changed_module), tempfile.TemporaryDirectory() as temp:
                folder = Path(temp)
                source = b'#define CID_Native_write 2\n'
                identity = hashlib.sha256(source).hexdigest()
                report = dict(cSha256=identity, limits=dict(mensagem='100', estado='100', resposta='100'))
                calls = []
                def compile_helper(command, *args, **kwargs):
                    calls.append(command)
                    if len(calls) == 1:
                        (folder/'checked.c').write_bytes(source + (b'changed' if changed_source else b''))
                        (folder/'checked.c.json').write_text(json.dumps(report))
                module = SimpleNamespace(report={'sourceSha256': '0'*64 if changed_module else identity}, close=Mock())
                with patch('tools.service.controller.helper', side_effect=compile_helper), \
                        patch('tools.service.controller.Module', return_value=module) as load:
                    if changed_source or changed_module:
                        with self.assertRaisesRegex(RuntimeError, 'C difere|módulo carregado difere'):
                            build(SimpleNamespace(stage=Mock()), folder, 'initialize', ('source', 'kernel'))
                        if changed_source:
                            load.assert_not_called()
                        else:
                            module.close.assert_called_once()
                    else:
                        result, limits = build(SimpleNamespace(stage=Mock()), folder, 'initialize', ('source', 'kernel'))
                        self.assertIs(result, module)
                        self.assertEqual(limits, dict(mensagem=100, estado=100, resposta=100))
                        self.assertEqual(calls[1][calls[1].index('--input-cid')+1], 'none')
                        module.close.assert_not_called()


if __name__ == '__main__':
    unittest.main(verbosity=2)
