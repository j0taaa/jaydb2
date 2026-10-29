"""Bind one host request to its exact allocation scope and retained C root.

The caller supplies an already-open scope covering the request from its real
start. This module does not substitute a later scope, erase coverage flags or
infer measurement from a returned numeric amount. Whole-entry startup/framing
and native field integration remain separate obligations.
"""
from __future__ import annotations

from .memory import MemoryWindow, InvalidMemoryObservation, validate


class RequestCompletion:
    def __init__(self, root, counter, scope, ceiling):
        self._root = root
        self._monitor = MemoryWindow(counter, scope, ceiling)
        self._prepared = None
        # Do this before accepting any proposal. In particular, the real
        # experimental observer is INCOMPLETE and cannot authorize this path.
        observed = validate(counter.window_read(), scope)
        if not observed.active:
            raise InvalidMemoryObservation('Request completion requires its active scope')

    @property
    def root(self):
        return self._root

    @property
    def monitor(self):
        return self._monitor

    @property
    def prepared(self):
        return self._prepared

    @property
    def state(self):
        return self.root.state

    @property
    def completed(self):
        p = self.prepared
        return p is not None and self.root.native.completed in (
            p.address, p.limited.address)

    @property
    def response(self):
        if not self.completed:
            raise RuntimeError('Request has no durable completed response')
        p = self.prepared
        return (p.response if self.root.native.completed == p.address
                else p.limited.response)

    def finish(self, response, *, state, deadline_ns, instrument_deadline_ns):
        if self.prepared is not None:
            raise RuntimeError('A request may enter the completion boundary only once')
        # All retention/allocation, including the fixed failure alternative,
        # precedes the native barrier. A later Python/FFI exception cannot
        # revoke the C root or change which response was completed.
        p = self.root.prepare(response, state=state, with_limit=True)
        self._prepared = p
        return self.root.finish_or_limit(p, scope=self.monitor.scope,
            ceiling=self.monitor.ceiling, deadline_ns=deadline_ns,
            instrument_deadline_ns=instrument_deadline_ns)
