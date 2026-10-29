"""Serial JayDB2 host: checked Bend, private proposals and one publication.

Only canonical message/state/response sizes belong to the contract. There is
no physical-memory accounting, request clock, observer or resource deadline.
"""
from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import selectors
import shutil
import tempfile

from .abi_simple import SimpleModule as Module, NativeFailure, NativeOwnershipPending
from .entry import prepare_entry
from .frames import error_frame
from .isolated import command as isolated_python
from .lifecycle import LifecycleRuntime, ProcessOwner
from .loading import Runtime as LoadingRuntime, LibraryScope
from .naturals import parse_decimal
from .staging import Environment, ROOT

# The private byte transport uses uint64 extents. This is a representation
# bound, not a RAM quota, reservation or configured processing budget.
TRANSPORT_MAX = 2**64 - 1


class IncompleteIntegration(Exception):
    """An unresolved owner cannot authorize a public response or publication."""


class CompileFailure(RuntimeError):
    def __init__(self, detail):
        self.detail = detail
        super().__init__(str(detail))


@dataclass(frozen=True, slots=True)
class RequestProposal:
    response: bytes
    state: bytes | None = None


@dataclass(frozen=True, slots=True)
class Published:
    state: bytes
    response: bytes = b''


def packet(first, second):
    return len(first).to_bytes(8, 'big') + first + second


def split(data):
    if len(data) < 8:
        raise RuntimeError('Transporte interno truncado')
    size = int.from_bytes(data[:8], 'big')
    if size > len(data) - 8:
        raise RuntimeError('Comprimento interno inválido')
    return data[8:8+size], data[8+size:]


def helper(command, error_file=None, *, lifecycle_runtime=None):
    runtime = LifecycleRuntime.current() if lifecycle_runtime is None else lifecycle_runtime
    if runtime.live_processes:
        raise IncompleteIntegration('An earlier helper still has unresolved ownership')
    process = None
    try:
        process = ProcessOwner.prepare(runtime, command)
        process.start()
        streams = (process.stdout, process.stderr)
        collected = {stream.fileno(): [] for stream in streams}
        with selectors.DefaultSelector() as ready:
            for stream in streams:
                os.set_blocking(stream.fileno(), False)
                ready.register(stream, selectors.EVENT_READ)
            exited = False
            while True:
                if not exited:
                    exited = process.poll()
                    if exited:
                        # WNOWAIT still pins the leader while descendants are
                        # stopped, so a reused group ID can never be signalled.
                        process.stop_and_wait()
                if exited and not ready.get_map():
                    break
                # Polling observes leader exit even if a descendant keeps its
                # pipe open. This interval is not an execution time budget.
                for event, _ in ready.select(0.05):
                    try:
                        chunk = os.read(event.fd, 65536)
                    except BlockingIOError:
                        continue
                    if chunk:
                        collected[event.fd].append(chunk)
                    else:
                        ready.unregister(event.fileobj)
            out, err = (b''.join(collected[stream.fileno()]) for stream in streams)
    finally:
        try:
            for owner in runtime.live_processes:
                owner.close()
            if runtime.live_processes:
                raise IncompleteIntegration('Helper ownership remains unresolved')
        except BaseException as error:
            if runtime.live_processes:
                raise IncompleteIntegration('Helper cleanup remains unresolved') from error
            raise
    if process.returncode:
        detail = None
        if error_file and error_file.exists():
            detail = json.loads(error_file.read_text())
        if detail is None:
            try:
                reported = json.loads(out)
                if 'error' in reported:
                    detail = {'code': 'NATIVE_BUILD_' + reported['error'],
                              'message': reported.get('message', '')}
            except (ValueError, TypeError):
                pass
        raise CompileFailure(detail or {
            'code': 'HELPER', 'message': err.decode('utf-8', 'replace')[-8000:]})
    return out


def build(environment, directory, purpose, toolchain, *, metadata=None,
          tools_root=ROOT, loading_runtime=None, lifecycle_runtime=None, library_scope=None):
    try:
        environment.stage(directory, purpose, metadata)
    except ValueError as error:
        raise CompileFailure({'code': 'DEPENDENCY', 'message': str(error)}) from error
    source_file = directory / 'checked.c'
    helper(isolated_python(tools_root, 'admission', [
        '--', 'node', str(tools_root / 'tools/service/compile.mjs'),
        str(directory / 'manifest.json'), str(source_file),
        str(toolchain[0]), str(toolchain[1])]),
        Path(str(source_file) + '.error.json'), lifecycle_runtime=lifecycle_runtime)
    report = json.loads(Path(str(source_file) + '.json').read_text())
    limits = {key: parse_decimal(value) for key, value in report['limits'].items()}
    if set(limits) != {'mensagem', 'estado', 'resposta'}:
        raise RuntimeError('A configuração deve conter somente três limites lógicos')
    source_bytes = source_file.read_bytes()
    if hashlib.sha256(source_bytes).hexdigest() != report['cSha256']:
        raise RuntimeError('O C difere da emissão do Book verificado')
    output = directory / (report['cSha256'] + '.so')
    source = source_bytes.decode('utf-8')
    args = [str(source_file), str(output)]
    for name, symbol in [('input', 'read'), ('output', 'write'), ('enter', 'enter')]:
        macro = 'CID_Native_' + symbol
        if re.search(r'^#define ' + macro + r' \d+$', source, re.M):
            args.extend([f'--{name}-cid', macro])
        elif name in ('input', 'output'):
            args.extend([f'--{name}-cid', 'none'])
    if purpose == 'execute':
        for name, symbol in [('loop', 'loop'), ('continue', 'Continuar'),
                             ('prepare', 'Preparar'), ('finish', 'Encerrar'),
                             ('inconsistent', 'Inconsistente')]:
            args.extend([f'--{name}-cid', 'CID_Native_' + symbol])
        states = re.findall(r'^#define (CID_\w*_EstadoExecucao) \d+$', source, re.M)
        if len(states) != 1:
            raise RuntimeError('Layout exato do estado de execução não encontrado')
        args.extend(['--state-cid', states[0]])
    helper(isolated_python(tools_root, 'native_simple', args),
           lifecycle_runtime=lifecycle_runtime)
    module = Module(output, loading_runtime=loading_runtime,
                    lifecycle_runtime=lifecycle_runtime, library_scope=library_scope)
    try:
        if module.report['sourceSha256'] != report['cSha256']:
            raise RuntimeError('O módulo carregado difere do C verificado')
    except BaseException:
        module.close()
        raise
    return module, limits


def exact_read(fd, size):
    data = bytearray()
    while len(data) < size:
        # A raised handler can hide already consumed bytes. Propagate it:
        # serve marks the channel unusable rather than repeat an uncertain read.
        chunk = os.read(fd, min(size - len(data), 65536))
        if not chunk:
            return bytes(data), False
        data.extend(chunk)
    return bytes(data), True


def deliver(fd, data):
    view = memoryview(data)
    while view:
        # Raised handlers may hide a committed prefix; never replay that view.
        quantity = os.write(fd, view)
        if quantity <= 0:
            raise BrokenPipeError('Canal de saída sem progresso')
        view = view[quantity:]


class Database:
    def __init__(self, environment: Environment, toolchain, *,
                 loading_runtime=None, lifecycle_runtime=None):
        prepare_entry()
        self._closed = self._fatal = self._channel_ended = self._busy = False
        self._published = Published(b'')
        self.loading_runtime = LoadingRuntime.current() if loading_runtime is None else loading_runtime
        self.lifecycle_runtime = LifecycleRuntime.current() if lifecycle_runtime is None else lifecycle_runtime
        self._request_libraries = LibraryScope()
        self._permanent_libraries = LibraryScope()
        self.environment, self.toolchain = environment, toolchain
        self.modules = {}
        self.last_failure = None
        self.directory = tempfile.TemporaryDirectory(prefix='jaydb2-')
        root = Path(self.directory.name)
        try:
            self.runtime = environment.materialize_tooling(root / 'runtime')
            for purpose in ('initialize', 'decode', 'authenticate'):
                directory = root / purpose
                directory.mkdir(mode=0o700)
                module, limits = build(environment, directory, purpose, toolchain,
                    tools_root=self.runtime, loading_runtime=self.loading_runtime,
                    lifecycle_runtime=self.lifecycle_runtime, library_scope=self._permanent_libraries)
                if self.modules and limits != self.limits:
                    module.close()
                    raise RuntimeError('A configuração mudou durante a inicialização')
                self.modules[purpose], self.limits = module, limits
            initial = self.modules['initialize']
            result = initial.run(b'', capacity=self.limits['estado'] + 1)
            initial.close()
            del self.modules['initialize']
            if result[:1] != b'\1' or len(result) - 1 > self.limits['estado']:
                raise RuntimeError('Configuração ou estado inicial inválido')
            shutil.rmtree(root / 'initialize')  # seed remains private
            self._published = Published(result[1:])
        except BaseException:
            self.close()
            raise

    @property
    def state(self):
        if self._closed:
            raise RuntimeError('Database is closed')
        return self._published.state

    @property
    def published_response(self):
        """The complete response retained by the most recent publication."""
        return self._published.response

    def _publish(self, prepared):
        # The immutable state AND response already exist; no cleanup, encoding,
        # allocation or helper invocation follows this one publication store.
        self._published = prepared

    def _close_libraries(self, scope):
        for owner in scope.live_owners:
            if self.lifecycle_runtime.has_live_leases(owner):
                raise IncompleteIntegration('A temporary library still owns output')
            owner.close()
        if scope.live_owners:
            raise IncompleteIntegration('Library ownership remains unresolved')

    def _require_resolved_ownership(self):
        runtime = self.lifecycle_runtime
        if runtime.live_processes or runtime.live_leases or self._request_libraries.live_owners:
            raise IncompleteIntegration('Request still owns helper, output or temporary library resources')

    def close(self):
        if self._busy:
            raise IncompleteIntegration('Close must wait until the active request returns')
        self._closed = True
        failure = None
        try:
            for owner in self.lifecycle_runtime.live_processes:
                owner.close()
        except BaseException as error:
            failure = error
        for name in tuple(self.modules):
            try:
                self.modules[name].close()
                del self.modules[name]
            except BaseException as error:
                failure = failure or error
        for scope in (self._request_libraries, self._permanent_libraries):
            try:
                self._close_libraries(scope)
            except BaseException as error:
                failure = failure or error
        if failure is not None:
            raise failure
        self.directory.cleanup()
        self._published = None
        self.environment = self.toolchain = self.runtime = None
        self.last_failure = None

    def preprocess(self, stage, data):
        result = self.modules[stage].run(data, capacity=TRANSPORT_MAX)
        if not result or result[0] not in (0, 1):
            raise RuntimeError('Transporte interno inválido no pré-processamento')
        return result

    def request(self, body):
        if self._closed or self._fatal or self._busy:
            raise RuntimeError('Database is closed, unusable or already processing a request')
        if type(body) is not bytes:
            raise TypeError('Request body must be immutable bytes')
        self._require_resolved_ownership()
        self._busy = True
        try:
            try:
                proposal = self._propose_request(body)
            finally:
                self._close_libraries(self._request_libraries)
            self._require_resolved_ownership()
            if proposal.state is not None:
                prepared = Published(proposal.state, proposal.response)
                self._publish(prepared)
            return proposal.response
        finally:
            self._busy = False

    def _propose_request(self, body):
        self.last_failure = None
        data = packet(self.state, body)
        try:
            decoded = self.preprocess('decode', data)
            if decoded[0] == 0:
                return RequestProposal(decoded[1:])
            auth = self.preprocess('authenticate', data)
            if auth[0] == 0:
                return RequestProposal(auth[1:])
            code, rest = split(auth[1:])
            proof, rest = split(rest)
            instance, bindings = split(rest)
            with tempfile.TemporaryDirectory(prefix='request-', dir=self.directory.name) as temp:
                module, limits = build(self.environment, Path(temp), 'execute', self.toolchain,
                    metadata=(code, proof, instance, bindings), tools_root=self.runtime,
                    loading_runtime=self.loading_runtime, lifecycle_runtime=self.lifecycle_runtime,
                    library_scope=self._request_libraries)
                try:
                    if limits != self.limits:
                        raise RuntimeError('Configuração da requisição divergente')
                    result = module.run(data,
                        capacity=self.limits['estado'] + self.limits['resposta'] + 17)
                    if result[:1] == b'\1':
                        state, response = split(result[1:])
                    elif result[:1] == b'\0':
                        state, response = None, result[1:]
                    else:
                        raise RuntimeError('Sinal de publicação inválido')
                    if state is not None and len(state) > self.limits['estado']:
                        raise RuntimeError('Estado preparado excedeu o limite lógico')
                    if len(response) < 8 or int.from_bytes(response[:8], 'big') != len(response) - 8 \
                            or len(response) - 8 > self.limits['resposta']:
                        raise RuntimeError('Resposta preparada inválida')
                finally:
                    module.close()
            return RequestProposal(response, state)
        except NativeFailure as error:
            self._fatal = error.fatal
            self.last_failure = {'code': 'NATIVE', 'status': error.status,
                                 'runtime_code': error.runtime_code, 'fatal': error.fatal}
            return RequestProposal(error_frame('falha'))
        except CompileFailure as error:
            self.last_failure = error.detail
            refused = {'IMPORT', 'IMPORT_CYCLE', 'DEPENDENCY', 'PARSE', 'META',
                'UNSAFE', 'FOREIGN', 'IO', 'OPEN_LAW', 'SHADOW', 'REDEFINITION',
                'PRIMARY_CHECK', 'BENDTT_CHECK', 'TARGET', 'SOURCE_BINDING',
                'HOST_CAPTURE', 'KERNEL_CAPTURE'}
            status = 'certificado' if error.detail.get('code') in refused else 'falha'
            return RequestProposal(error_frame(status))
        except MemoryError:
            self._fatal = True
            raise
        except (OSError, RuntimeError) as error:
            self.last_failure = {'code': type(error).__name__, 'message': str(error)}
            return RequestProposal(error_frame('falha'))

    def serve(self, input_fd=0, output_fd=1):
        if self._closed or self._fatal or self._channel_ended:
            raise RuntimeError('Database or input channel is closed')
        try:
            while True:
                header, complete = exact_read(input_fd, 8)
                if not header:
                    return
                if not complete:
                    deliver(output_fd, error_frame('entrada'))
                    return
                size = int.from_bytes(header, 'big')
                if size > self.limits['mensagem']:
                    deliver(output_fd, error_frame('limite'))
                    return
                body, complete = exact_read(input_fd, size)
                if not complete:
                    deliver(output_fd, error_frame('entrada'))
                    return
                response = self.request(body)
                deliver(output_fd, response)
                if self._fatal:
                    return
        except BaseException:
            # Unknown consumption or partial delivery cannot be retried. A
            # normal EOF/framing return has a known extent and remains usable
            # by a trusted caller opening a distinct channel for this instance.
            self._channel_ended = True
            raise
