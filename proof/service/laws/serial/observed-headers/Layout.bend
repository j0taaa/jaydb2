# A derived grammar of actual event lists. Only extension parsing can add the
# two headers; their real quiet prefix and full remaining tail are retained.
# This is an internal source theorem, never a native trace-equality premise.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Semantics.bend as S
import ../../../../../contract/Resources.bend as X
import ../../../../HostTransitions.bend as Host
import ../../../../PreparedDispatch.bend as Cached
import ../../../../SourceService.bend as Source
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../phases/InvalidationPhases.bend as N
import ../../../model/EventObserver.bend as O
import ../../../model/serial/Common.bend as C
import ../../../model/serial/Decode.bend as Decode
import ../../../model/serial/Dispatch.bend as Dispatch
import ../../../model/serial/LocalHistory.bend as J
import ./HeaderData.bend as Header
import ./RuntimeBase.bend as B
import ./RuntimeDispatch.bend as Runtime
import ./PreparationTail.bend as Preparation
import ./InvalidationTail.bend as Invalidation


def Headers(+before: E.Snapshot, +wire: W.WireRequest, -events: List<&2, O.AuditEvent>) -> Type:
  &prefix: List<&2, O.AuditEvent> -> &first: O.AuditEvent -> &second: O.AuditEvent -> &tail: List<&2, O.AuditEvent> ->
    L.E<{events == C.append(prefix, Con{first, Con{second, tail}}) : List<&2, O.AuditEvent>},
      L.E<B.All(prefix), L.E<J.Quiet(prefix),
        L.E<{Header.event(first) == Header.Wire{wire} : Header.View},
          L.E<{O.change(first) == None{} : Maybe<&2, O.Change>},
            L.E<{Header.event(second) == Header.Identity{wire, D.authenticate(E.database(before), I.credential(W.raw(wire)))} : Header.View}, B.All(tail)>>>>>>


def Choice(+before: E.Snapshot, decision: Decode.Decision, +events: List<&2, O.AuditEvent>) -> Type:
  match decision:
    case Decode.Parsed{W.Extension{operation, raw}}: Headers(before, W.Extension{operation, raw}, events)
    case _: B.All(events)


def preparation_headers(+mode: V.Mode, +raw: P.Request, +before: E.Snapshot, run: V.PreparationRun, no_headers: Preparation.Tail(run)) ->
  Headers(before, W.Extension{V.operation(mode), raw}, C.events(C.preparation(V.push(V.WireReceived{W.Extension{V.operation(mode), raw}},
    V.push(V.IdentityEstablished{W.Extension{V.operation(mode), raw}, D.authenticate(E.database(before), I.credential(raw))}, run))))):
  match run:
    case V.PreparationRun{events, result, snapshot, waiting, closed}:
      (Nil{}, O.Preparation{V.WireReceived{W.Extension{V.operation(mode), raw}}},
        O.Preparation{V.IdentityEstablished{W.Extension{V.operation(mode), raw}, D.authenticate(E.database(before), I.credential(raw))}}, C.prepare_events(events),
        L.Both{{==}, L.Both{Unit{}, L.Both{Unit{}, L.Both{{==}, L.Both{{==}, L.Both{{==}, no_headers}}}}}})


def invalidation_headers(+raw: P.Request, +before: E.Snapshot, run: N.InvalidationRun, no_headers: Invalidation.Tail(run)) ->
  Headers(before, W.Extension{W.Invalidate{}, raw}, C.events(C.invalidation(N.push(N.InvalidationBase{V.WireReceived{W.Extension{W.Invalidate{}, raw}}},
    N.push(N.InvalidationBase{V.IdentityEstablished{W.Extension{W.Invalidate{}, raw}, D.authenticate(E.database(before), I.credential(raw))}}, run))))):
  match run:
    case N.InvalidationRun{events, result, snapshot, waiting, closed}:
      (Nil{}, O.Invalidation{N.InvalidationBase{V.WireReceived{W.Extension{W.Invalidate{}, raw}}}},
        O.Invalidation{N.InvalidationBase{V.IdentityEstablished{W.Extension{W.Invalidate{}, raw}, D.authenticate(E.database(before), I.credential(raw))}}}, C.invalidate_events(events),
        L.Both{{==}, L.Both{Unit{}, L.Both{Unit{}, L.Both{{==}, L.Both{{==}, L.Both{{==}, no_headers}}}}}})


def cached_headers(+raw: P.Request, +before: E.Snapshot, run: C.CallRun, no_headers: B.Call(run)) ->
  Headers(before, W.Extension{W.Execute{}, raw}, C.events(C.prefix([O.Preparation{V.WireReceived{W.Extension{W.Execute{}, raw}}},
    O.Preparation{V.IdentityEstablished{W.Extension{W.Execute{}, raw}, D.authenticate(E.database(before), I.credential(raw))}}], run))):
  match run:
    case C.CallRun{events, snapshot, outcome, waiting, closed}:
      (Nil{}, O.Preparation{V.WireReceived{W.Extension{W.Execute{}, raw}}},
        O.Preparation{V.IdentityEstablished{W.Extension{W.Execute{}, raw}, D.authenticate(E.database(before), I.credential(raw))}}, events,
        L.Both{{==}, L.Both{Unit{}, L.Both{Unit{}, L.Both{{==}, L.Both{{==}, L.Both{{==}, no_headers}}}}}})


def extension(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +operation: W.Operation, +before: E.Snapshot, +raw: P.Request, primitives: Dispatch.Primitives) ->
  Headers(before, W.Extension{operation, raw}, C.events(Dispatch.extension(c, binding, public, operation, before, raw, primitives))):
  match operation primitives:
    case W.Prepare{} Dispatch.Primitives{+checker, +allocation, +seal, cleanup, artifact, execution, +send}:
      preparation_headers(V.PrepareMode{}, raw, before,
        V.authenticated(c, D.authenticate(E.database(before), I.credential(raw)), V.PrepareMode{}, raw, before, V.Returns{checker, allocation, seal, send}),
        Preparation.authenticated(c, D.authenticate(E.database(before), I.credential(raw)), V.PrepareMode{}, raw, before, V.Returns{checker, allocation, seal, send}))
    case W.PrepareRead{} Dispatch.Primitives{+checker, +allocation, +seal, cleanup, artifact, execution, +send}:
      preparation_headers(V.ReadMode{}, raw, before,
        V.authenticated(c, D.authenticate(E.database(before), I.credential(raw)), V.ReadMode{}, raw, before, V.Returns{checker, allocation, seal, send}),
        Preparation.authenticated(c, D.authenticate(E.database(before), I.credential(raw)), V.ReadMode{}, raw, before, V.Returns{checker, allocation, seal, send}))
    case W.Invalidate{} Dispatch.Primitives{checker, allocation, seal, +cleanup, artifact, execution, +send}:
      invalidation_headers(raw, before, N.authenticated(c, D.authenticate(E.database(before), I.credential(raw)), before, raw, cleanup, send),
        Invalidation.authenticated(c, D.authenticate(E.database(before), I.credential(raw)), before, raw, cleanup, send))
    case W.Execute{} Dispatch.Primitives{checker, allocation, seal, cleanup, +artifact, +execution, +send}:
      cached_headers(raw, before,
        Dispatch.cached_choice(c, binding, public, Cached.choose(E.instance(before), Host.Published{E.database(before), E.last_response(before), E.registry(before)}, raw), before, raw, artifact, execution, send),
        Runtime.cached_choice(c, binding, public, Cached.choose(E.instance(before), Host.Published{E.database(before), E.last_response(before), E.registry(before)}, raw), before, raw, artifact, execution, send))


def parsed(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +wire: W.WireRequest, +before: E.Snapshot, +primitives: Dispatch.Primitives) ->
  Choice(before, Decode.Parsed{wire}, C.events(Dispatch.parsed(c, binding, public, before, wire, primitives))):
  match wire:
    case W.Ordinary{raw}: Runtime.ordinary(c, binding, public, before, raw, primitives)
    case W.Extension{operation, raw}: extension(c, binding, public, operation, before, raw, primitives)


def decision(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +actual: Decode.Decision, +before: E.Snapshot, +primitives: Dispatch.Primitives) ->
  Choice(before, actual, C.events(Dispatch.decoded_decision(c, binding, public, actual, before, primitives))):
  match actual:
    case Decode.Shutdown{}: L.Both{Unit{}, Unit{}}
    case Decode.TransportStopped{}: Unit{}
    case Decode.Reject{mode, status, closes}: B.error(mode, "", before, status, closes, Dispatch.send(primitives))
    case Decode.Parsed{wire}: parsed(c, binding, public, wire, before, primitives)


def append_associative(+first: List<&2, O.AuditEvent>, +middle: List<&2, O.AuditEvent>, +last: List<&2, O.AuditEvent>) ->
  {C.append(first, C.append(middle, last)) == C.append(C.append(first, middle), last) : List<&2, O.AuditEvent>}:
  match first:
    case Nil{}: {==}
    case Con{+head, +rest}: Equal.cong(List<&2, O.AuditEvent>, List<&2, O.AuditEvent>, tail => Con{head, tail},
      C.append(rest, C.append(middle, last)), C.append(C.append(rest, middle), last), append_associative(rest, middle, last))


def quiet_append(+first: List<&2, O.AuditEvent>, -last: List<&2, O.AuditEvent>, a: J.Quiet(first), b: J.Quiet(last)) -> J.Quiet(C.append(first, last)):
  match first a:
    case Nil{} unit: b
    case Con{head, +rest} L.Both{quiet, later}: L.Both{quiet, quiet_append(rest, last, later, b)}


def prefix_headers(+before: E.Snapshot, +wire: W.WireRequest, +prefix: List<&2, O.AuditEvent>, +events: List<&2, O.AuditEvent>,
  absent: B.All(prefix), quiet: J.Quiet(prefix), existing: Headers(before, wire, events)) -> Headers(before, wire, C.append(prefix, events)):
  match existing:
    case (+old, +first, +second, +tail, L.Both{exact, L.Both{old_absent, L.Both{old_quiet, L.Both{wire_view, L.Both{wire_quiet, L.Both{identity, tail_absent}}}}}}):
      (C.append(prefix, old), first, second, tail,
        L.Both{Equal.trans(List<&2, O.AuditEvent>, C.append(prefix, events), C.append(prefix, C.append(old, Con{first, Con{second, tail}})), C.append(C.append(prefix, old), Con{first, Con{second, tail}}),
          Equal.cong(List<&2, O.AuditEvent>, List<&2, O.AuditEvent>, rest => C.append(prefix, rest), events, C.append(old, Con{first, Con{second, tail}}), exact),
          append_associative(prefix, old, Con{first, Con{second, tail}})),
          L.Both{B.appended(prefix, old, absent, old_absent), L.Both{quiet_append(prefix, old, quiet, old_quiet), L.Both{wire_view, L.Both{wire_quiet, L.Both{identity, tail_absent}}}}}})


def prefix_choice(+before: E.Snapshot, +actual: Decode.Decision, +prefix: List<&2, O.AuditEvent>, +events: List<&2, O.AuditEvent>,
  absent: B.All(prefix), quiet: J.Quiet(prefix), existing: Choice(before, actual, events)) -> Choice(before, actual, C.append(prefix, events)):
  match actual:
    case Decode.Parsed{W.Extension{operation, raw}}: prefix_headers(before, W.Extension{operation, raw}, prefix, events, absent, quiet, existing)
    case Decode.Parsed{W.Ordinary{raw}}: B.appended(prefix, events, absent, existing)
    case Decode.Shutdown{}: B.appended(prefix, events, absent, existing)
    case Decode.TransportStopped{}: B.appended(prefix, events, absent, existing)
    case Decode.Reject{mode, status, closes}: B.appended(prefix, events, absent, existing)


def prefix_events(+prefix: List<&2, O.AuditEvent>, run: C.CallRun) ->
  {C.events(C.prefix(prefix, run)) == C.append(prefix, C.events(run)) : List<&2, O.AuditEvent>}:
  match run:
    case C.CallRun{events, snapshot, outcome, waiting, closed}: {==}


def decoded(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +before: E.Snapshot, actual: Decode.DecodeRun, +primitives: Dispatch.Primitives) ->
  Choice(before, Decode.decision(actual), C.events(Dispatch.decoded(c, binding, public, before, actual, primitives))):
  match actual:
    case Decode.DecodeRun{+result, +frames}:
      %Equal.sym(List<&2, O.AuditEvent>, C.events(C.prefix(C.core(Dispatch.decision_mode(result), Dispatch.decision_code(result), frames), Dispatch.decoded_decision(c, binding, public, result, before, primitives))),
        C.append(C.core(Dispatch.decision_mode(result), Dispatch.decision_code(result), frames), C.events(Dispatch.decoded_decision(c, binding, public, result, before, primitives))),
        prefix_events(C.core(Dispatch.decision_mode(result), Dispatch.decision_code(result), frames), Dispatch.decoded_decision(c, binding, public, result, before, primitives))) : Choice(before, result, _)
      prefix_choice(before, result, C.core(Dispatch.decision_mode(result), Dispatch.decision_code(result), frames), C.events(Dispatch.decoded_decision(c, binding, public, result, before, primitives)),
        B.core(Dispatch.decision_mode(result), Dispatch.decision_code(result), frames), J.core_quiet(Dispatch.decision_mode(result), Dispatch.decision_code(result), frames), decision(c, binding, public, result, before, primitives))


law every_actual_dispatch_derives_the_exact_retained_header_grammar_or_proves_there_are_no_headers:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +before: E.Snapshot
  for +input: X.Reception
  for +primitives: Dispatch.Primitives
  Choice(before, Decode.decision(Decode.run(c, E.database(before), input)), C.events(Dispatch.run(c, binding, public, before, input, primitives)))
def every_actual_dispatch_derives_the_exact_retained_header_grammar_or_proves_there_are_no_headers(c, binding, public, before, input, primitives):
  decoded(c, binding, public, before, Decode.run(c, E.database(before), input), primitives)
