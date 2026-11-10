# Actual ordinary dispatch and cached execution tails have no host headers.
# The separate parsed-extension dispatcher adds its two real header events.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedLaws.bend as H
import ../../../../../contract/PreparedRegistry.bend as G
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../../PreparedDispatch.bend as Cached
import ../../../../ProtocolService.bend as Q
import ../../../../SourceService.bend as Source
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../model/EventObserver.bend as O
import ../../../model/serial/Common.bend as C
import ../../../model/serial/Binding.bend as Binding
import ../../../model/serial/Dispatch.bend as Dispatch
import ../../../model/serial/ExecutionPhases.bend as Execution
import ./RuntimeBase.bend as N
import ./RuntimeExecution.bend as Execute


def ordinary_bound(~c: S.Configuration, ~binding: Source.Source, origin: Maybe<&2, Source.JudgmentSyntactic>,
  +before: E.Snapshot, +raw: P.Request, +context: D.Context, checker: V.CheckerReturn, +execution: Execution.Request, +send: V.SendReturn) ->
  N.Call(Dispatch.ordinary_bound(c, binding, origin, before, raw, context, checker, execution, send)):
  match origin:
    case None{}: Unit{}
    case Some{+origin}:
      match checker:
        case V.CheckerPending{}: Unit{}
        case V.CheckerFailed{stage, identifier, fatal}: N.failed(False{}, I.code(raw), before, stage, identifier, fatal, send)
        case V.CheckerRefuted{}:
          N.prefixed([O.BoundCore{False{}, origin, Q.Rejected{raw, context}}], C.error(False{}, I.code(raw), before, S.Certificate{}, False{}, send),
            L.Both{Unit{}, Unit{}}, N.error(False{}, I.code(raw), before, S.Certificate{}, False{}, send))
        case V.CheckerAccepted{}:
          N.prefixed([O.BoundCore{False{}, origin, Q.Accepts{raw, context}}], Execution.run_bound(c, binding, origin, False{}, raw, context, before, execution, send),
            L.Both{Unit{}, Unit{}}, Execute.run_bound(c, binding, origin, False{}, raw, context, before, execution, send))


def ordinary_checked(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, +raw: P.Request, +context: D.Context, +checker: V.CheckerReturn, +execution: Execution.Request, +send: V.SendReturn) ->
  N.Call(Dispatch.ordinary_checked(c, binding, public, before, raw, context, checker, execution, send)):
  ordinary_bound(c, binding, Binding.ordinary(public, raw, context), before, raw, context, checker, execution, send)


def ordinary_identity(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  identity: Maybe<&2, D.Context>, +before: E.Snapshot, +raw: P.Request, primitives: Dispatch.Primitives) ->
  N.Call(Dispatch.ordinary_identity(c, binding, public, identity, before, raw, primitives)):
  match identity:
    case None{}: N.error(False{}, I.code(raw), before, S.Authentication{}, False{}, Dispatch.send(primitives))
    case Some{context}:
      match primitives:
        case Dispatch.Primitives{checker, allocator, seal, cleanup, artifact, execution, send}:
          ordinary_checked(c, binding, public, before, raw, context, checker, execution, send)


def ordinary(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, +raw: P.Request, +primitives: Dispatch.Primitives) -> N.Call(Dispatch.ordinary(c, binding, public, before, raw, primitives)):
  N.prefixed(C.core(False{}, I.code(raw), [Q.Received{raw}, Q.Authenticated{raw, D.authenticate(E.database(before), I.credential(raw))}]),
    Dispatch.ordinary_identity(c, binding, public, D.authenticate(E.database(before), I.credential(raw)), before, raw, primitives),
    N.core(False{}, I.code(raw), [Q.Received{raw}, Q.Authenticated{raw, D.authenticate(E.database(before), I.credential(raw))}]),
    ordinary_identity(c, binding, public, D.authenticate(E.database(before), I.credential(raw)), before, raw, primitives))


def cached_artifact(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  artifact: Dispatch.ArtifactReturn, +before: E.Snapshot, +raw: P.Request, +entry: G.Entry, +context: D.Context,
  +execution: Execution.Request, +send: V.SendReturn) -> N.Call(Dispatch.cached_artifact(c, binding, public, artifact, before, raw, entry, context, execution, send)):
  match artifact:
    case Dispatch.ArtifactPending{}: Unit{}
    case Dispatch.ArtifactFailed{identifier, fatal}: N.failed(True{}, G.code(entry), before, X.Verify{}, identifier, fatal, send)
    case Dispatch.ArtifactAvailable{}:
      N.prefixed([O.Resolution{raw, entry, context}], Execution.run(c, binding, public, True{}, H.resolved(raw, entry), context, before, execution, send),
        L.Both{Unit{}, Unit{}}, Execute.run(c, binding, public, True{}, H.resolved(raw, entry), context, before, execution, send))


def cached_choice(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  choice: Cached.Choice, +before: E.Snapshot, +raw: P.Request, +artifact: Dispatch.ArtifactReturn,
  +execution: Execution.Request, +send: V.SendReturn) -> N.Call(Dispatch.cached_choice(c, binding, public, choice, before, raw, artifact, execution, send)):
  match choice:
    case Cached.Unauthenticated{}: N.error(True{}, "", before, S.Authentication{}, False{}, send)
    case Cached.BadProof{context}: N.error(True{}, "", before, S.Input{}, False{}, send)
    case Cached.Missing{context}: N.error(True{}, "", before, S.Failure{}, False{}, send)
    case Cached.Selected{context, entry}: cached_artifact(c, binding, public, artifact, before, raw, entry, context, execution, send)
