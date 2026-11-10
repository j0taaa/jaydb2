# The history invariant is derived from EVERY actual pure dispatch branch.
# Primitive returns carry no law/Current/final-validity claim. In particular,
# pending invalidation cleanup retains its earlier mutation without a result.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Interface.bend as I
import ../../../../contract/Logic.bend as L
import ../../../../contract/PreparedLaws.bend as H
import ../../../../contract/PreparedProtocol.bend as W
import ../../../../contract/PreparedRegistry.bend as G
import ../../../../contract/Protocol.bend as P
import ../../../../contract/Resources.bend as X
import ../../../../contract/Semantics.bend as S
import ../../../HostTransitions.bend as Host
import ../../../PreparedDispatch.bend as Cached
import ../../../ProtocolService.bend as Q
import ../../../SourceService.bend as Source
import ../../specification/ServiceLaws.bend as E
import ../../phases/PreparePhases.bend as V
import ../../phases/InvalidationPhases.bend as N
import ../EventObserver.bend as O
import ./Binding.bend as Binding
import ./Common.bend as C
import ./CommonHistory.bend as Common
import ./Decode.bend as Decode
import ./Dispatch.bend as Dispatch
import ./ExecutionPhases.bend as Execution
import ./ExecutionHistory.bend as Execute
import ./InvalidationHistory.bend as Invalidation
import ./LocalHistory.bend as J
import ./PrepareHistory.bend as Preparation


def preparation_call(+position: J.Position, +run: V.PreparationRun, +before: E.Snapshot, proof: Preparation.Sound(position, run, before)) -> J.CallSound(position, C.preparation(run), before):
  V.PreparationRun{events, result, snapshot, waiting, closed} = run
  proof


def invalidation_call(+position: J.Position, +run: N.InvalidationRun, +before: E.Snapshot, proof: Invalidation.Sound(position, run, before)) -> J.CallSound(position, C.invalidation(run), before):
  N.InvalidationRun{events, result, snapshot, waiting, closed} = run
  proof


def prep_run(~c: S.Configuration, +position: J.Position, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot, +returns: V.Returns,
  selection: {J.selected(position) == E.database(before) : D.State}) -> Preparation.Sound(position, V.run(c, mode, raw, before, returns), before):
  +identity = D.authenticate(E.database(before), I.credential(raw))
  Preparation.push(position, V.WireReceived{W.Extension{V.operation(mode), raw}},
    V.push(V.IdentityEstablished{W.Extension{V.operation(mode), raw}, identity}, V.authenticated(c, identity, mode, raw, before, returns)), before, {==},
    Preparation.push(position, V.IdentityEstablished{W.Extension{V.operation(mode), raw}, identity}, V.authenticated(c, identity, mode, raw, before, returns), before, {==},
      Preparation.authenticated(c, position, identity, mode, raw, before, returns, selection)))


def invalidation_run(~c: S.Configuration, +position: J.Position, +before: E.Snapshot, +raw: P.Request, +cleanup: N.CleanupReturn, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) -> Invalidation.Sound(position, N.run(c, before, raw, cleanup, send), before):
  +identity = D.authenticate(E.database(before), I.credential(raw))
  Invalidation.push(position, N.InvalidationBase{V.WireReceived{W.Extension{W.Invalidate{}, raw}}},
    N.push(N.InvalidationBase{V.IdentityEstablished{W.Extension{W.Invalidate{}, raw}, identity}}, N.authenticated(c, identity, before, raw, cleanup, send)), before, {==},
    Invalidation.push(position, N.InvalidationBase{V.IdentityEstablished{W.Extension{W.Invalidate{}, raw}, identity}}, N.authenticated(c, identity, before, raw, cleanup, send), before, {==},
      Invalidation.authenticated(c, position, identity, before, raw, cleanup, send, selection)))


def ordinary_bound(~c: S.Configuration, ~binding: Source.Source,
  +position: J.Position, +origin: Maybe<&2, Source.JudgmentSyntactic>, +before: E.Snapshot, +raw: P.Request, +context: D.Context,
  +checker: V.CheckerReturn, +execution: Execution.Request, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) -> J.CallSound(position, Dispatch.ordinary_bound(c, binding, origin, before, raw, context, checker, execution, send), before):
  match origin:
    case None{}: J.no_events(position, before)
    case Some{+origin}:
      match checker:
        case V.CheckerPending{}: J.no_events(position, before)
        case V.CheckerFailed{stage, id, fatal}: Common.failed(position, False{}, I.code(raw), before, stage, id, fatal, send)
        case V.CheckerRefuted{}:
          J.prefix_call(position, [O.BoundCore{False{}, origin, Q.Rejected{raw, context}}], C.error(False{}, I.code(raw), before, S.Certificate{}, False{}, send), before,
            L.Both{{==}, Unit{}}, Common.error(position, False{}, I.code(raw), before, S.Certificate{}, False{}, send))
        case V.CheckerAccepted{}:
          J.prefix_call(position, [O.BoundCore{False{}, origin, Q.Accepts{raw, context}}], Execution.run_bound(c, binding, origin, False{}, raw, context, before, execution, send), before,
            L.Both{{==}, Unit{}}, Execute.run_bound(c, binding, position, origin, False{}, raw, context, before, execution, send, selection))


def ordinary_checked(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +position: J.Position, +before: E.Snapshot, +raw: P.Request, +context: D.Context, +checker: V.CheckerReturn, +execution: Execution.Request, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) -> J.CallSound(position, Dispatch.ordinary_checked(c, binding, public, before, raw, context, checker, execution, send), before):
  ordinary_bound(c, binding, position, Binding.ordinary(public, raw, context), before, raw, context, checker, execution, send, selection)


def ordinary_identity(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +position: J.Position, +identity: Maybe<&2, D.Context>, +before: E.Snapshot, +raw: P.Request, +primitives: Dispatch.Primitives,
  selection: {J.selected(position) == E.database(before) : D.State}) -> J.CallSound(position, Dispatch.ordinary_identity(c, binding, public, identity, before, raw, primitives), before):
  match identity:
    case None{}: Common.error(position, False{}, I.code(raw), before, S.Authentication{}, False{}, Dispatch.send(primitives))
    case Some{context}:
      match primitives:
        case Dispatch.Primitives{checker, allocator, seal, cleanup, artifact, execution, send}: ordinary_checked(c, binding, public, position, before, raw, context, checker, execution, send, selection)


def ordinary(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +position: J.Position, +before: E.Snapshot, +raw: P.Request, +primitives: Dispatch.Primitives,
  selection: {J.selected(position) == E.database(before) : D.State}) -> J.CallSound(position, Dispatch.ordinary(c, binding, public, before, raw, primitives), before):
  +identity = D.authenticate(E.database(before), I.credential(raw))
  J.prefix_call(position, C.core(False{}, I.code(raw), [Q.Received{raw}, Q.Authenticated{raw, identity}]), Dispatch.ordinary_identity(c, binding, public, identity, before, raw, primitives), before,
    J.core_quiet(False{}, I.code(raw), [Q.Received{raw}, Q.Authenticated{raw, identity}]), ordinary_identity(c, binding, public, position, identity, before, raw, primitives, selection))


def cached_artifact(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +position: J.Position, +artifact: Dispatch.ArtifactReturn, +before: E.Snapshot, +raw: P.Request, +entry: G.Entry,
  +context: D.Context, +execution: Execution.Request, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) -> J.CallSound(position, Dispatch.cached_artifact(c, binding, public, artifact, before, raw, entry, context, execution, send), before):
  match artifact:
    case Dispatch.ArtifactPending{}: J.no_events(position, before)
    case Dispatch.ArtifactFailed{id, fatal}: Common.failed(position, True{}, G.code(entry), before, X.Verify{}, id, fatal, send)
    case Dispatch.ArtifactAvailable{}:
      J.prefix_call(position, [O.Resolution{raw, entry, context}], Execution.run(c, binding, public, True{}, H.resolved(raw, entry), context, before, execution, send), before,
        L.Both{{==}, Unit{}}, Execute.run(c, binding, public, position, True{}, H.resolved(raw, entry), context, before, execution, send, selection))


def cached_choice(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +position: J.Position, +choice: Cached.Choice, +before: E.Snapshot, +raw: P.Request, +artifact: Dispatch.ArtifactReturn,
  +execution: Execution.Request, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) -> J.CallSound(position, Dispatch.cached_choice(c, binding, public, choice, before, raw, artifact, execution, send), before):
  match choice:
    case Cached.Unauthenticated{}: Common.error(position, True{}, "", before, S.Authentication{}, False{}, send)
    case Cached.BadProof{context}: Common.error(position, True{}, "", before, S.Input{}, False{}, send)
    case Cached.Missing{context}: Common.error(position, True{}, "", before, S.Failure{}, False{}, send)
    case Cached.Selected{context, entry}: cached_artifact(c, binding, public, position, artifact, before, raw, entry, context, execution, send, selection)


def cached(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +position: J.Position, +before: E.Snapshot, +raw: P.Request, +artifact: Dispatch.ArtifactReturn, +execution: Execution.Request, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) -> J.CallSound(position, Dispatch.cached(c, binding, public, before, raw, artifact, execution, send), before):
  J.prefix_call(position, [O.Preparation{V.WireReceived{W.Extension{W.Execute{}, raw}}}, O.Preparation{V.IdentityEstablished{W.Extension{W.Execute{}, raw}, D.authenticate(E.database(before), I.credential(raw))}}],
    Dispatch.cached_choice(c, binding, public, Cached.choose(E.instance(before), Host.Published{E.database(before), E.last_response(before), E.registry(before)}, raw), before, raw, artifact, execution, send), before,
    L.Both{{==}, L.Both{{==}, Unit{}}},
    cached_choice(c, binding, public, position, Cached.choose(E.instance(before), Host.Published{E.database(before), E.last_response(before), E.registry(before)}, raw), before, raw, artifact, execution, send, selection))


def extension(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +position: J.Position, +operation: W.Operation, +before: E.Snapshot, +raw: P.Request, +primitives: Dispatch.Primitives,
  selection: {J.selected(position) == E.database(before) : D.State}) -> J.CallSound(position, Dispatch.extension(c, binding, public, operation, before, raw, primitives), before):
  match operation primitives:
    case W.Prepare{} Dispatch.Primitives{checker, allocator, seal, cleanup, artifact, execution, send}:
      preparation_call(position, V.run(c, V.PrepareMode{}, raw, before, V.Returns{checker, allocator, seal, send}), before, prep_run(c, position, V.PrepareMode{}, raw, before, V.Returns{checker, allocator, seal, send}, selection))
    case W.PrepareRead{} Dispatch.Primitives{checker, allocator, seal, cleanup, artifact, execution, send}:
      preparation_call(position, V.run(c, V.ReadMode{}, raw, before, V.Returns{checker, allocator, seal, send}), before, prep_run(c, position, V.ReadMode{}, raw, before, V.Returns{checker, allocator, seal, send}, selection))
    case W.Invalidate{} Dispatch.Primitives{checker, allocator, seal, cleanup, artifact, execution, send}:
      invalidation_call(position, N.run(c, before, raw, cleanup, send), before, invalidation_run(c, position, before, raw, cleanup, send, selection))
    case W.Execute{} Dispatch.Primitives{checker, allocator, seal, cleanup, artifact, execution, send}:
      cached(c, binding, public, position, before, raw, artifact, execution, send, selection)


def parsed(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +position: J.Position, +before: E.Snapshot, +wire: W.WireRequest, +primitives: Dispatch.Primitives,
  selection: {J.selected(position) == E.database(before) : D.State}) -> J.CallSound(position, Dispatch.parsed(c, binding, public, before, wire, primitives), before):
  match wire:
    case W.Ordinary{raw}: ordinary(c, binding, public, position, before, raw, primitives, selection)
    case W.Extension{operation, raw}: extension(c, binding, public, position, operation, before, raw, primitives, selection)


def decoded_decision(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +position: J.Position, +decision: Decode.Decision, +before: E.Snapshot, +primitives: Dispatch.Primitives,
  selection: {J.selected(position) == E.database(before) : D.State}) -> J.CallSound(position, Dispatch.decoded_decision(c, binding, public, decision, before, primitives), before):
  match decision:
    case Decode.Shutdown{}: J.quiet_all(position, [O.Core{False{}, "", Q.Closed{}}], before, L.Both{{==}, Unit{}})
    case Decode.TransportStopped{}: J.no_events(position, before)
    case Decode.Reject{mode, status, closes}: Common.error(position, mode, "", before, status, closes, Dispatch.send(primitives))
    case Decode.Parsed{wire}: parsed(c, binding, public, position, before, wire, primitives, selection)


def decoded(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +position: J.Position, +before: E.Snapshot, +decoded: Decode.DecodeRun, +primitives: Dispatch.Primitives,
  selection: {J.selected(position) == E.database(before) : D.State}) -> J.CallSound(position, Dispatch.decoded(c, binding, public, before, decoded, primitives), before):
  Decode.DecodeRun{+decision, +frames} = decoded
  J.prefix_call(position, C.core(Dispatch.decision_mode(decision), Dispatch.decision_code(decision), frames), Dispatch.decoded_decision(c, binding, public, decision, before, primitives), before,
    J.core_quiet(Dispatch.decision_mode(decision), Dispatch.decision_code(decision), frames), decoded_decision(c, binding, public, position, decision, before, primitives, selection))


law every_actual_dispatch_prefix_derives_its_complete_event_history_and_full_snapshot:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +world: Nat
  for +input: X.Reception
  for +before: E.Snapshot
  for +primitives: Dispatch.Primitives
  J.CallSound(J.Position{world, input, E.database(before)}, Dispatch.run(c, binding, public, before, input, primitives), before)
def every_actual_dispatch_prefix_derives_its_complete_event_history_and_full_snapshot(c, binding, public, world, input, before, primitives):
  decoded(c, binding, public, J.Position{world, input, E.database(before)}, before, Decode.run(c, E.database(before), input), primitives, {==})
