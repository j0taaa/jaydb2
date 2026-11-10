# Full deterministic dispatch context of real execution publications. Ordinary
# code is bound to generated per-call Instance sources; cached code comes from
# the actual current lookup and artifact-available branch, without a new check.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Interface.bend as I
import ../../../../contract/Logic.bend as L
import ../../../../contract/PreparedLaws.bend as H
import ../../../../contract/PreparedProtocol.bend as W
import ../../../../contract/PreparedRegistry.bend as G
import ../../../../contract/Protocol.bend as P
import ../../../../contract/Requirements.bend as R
import ../../../../contract/Resources.bend as X
import ../../../../contract/Semantics.bend as S
import ../../../Foundations.bend as F
import ../../../HostTransitions.bend as Host
import ../../../PreparedDispatch.bend as Cached
import ../../../ProtocolService.bend as Q
import ../../../RoutesService.bend as Route
import ../../../SourceService.bend as Source
import ../../specification/ServiceLaws.bend as E
import ../../phases/PreparePhases.bend as V
import ../../phases/InvalidationPhases.bend as N
import ../EventObserver.bend as O
import ../FrameBounds.bend as B
import ./Binding.bend as Binding
import ./Common.bend as C
import ./Decode.bend as Decode
import ./Dispatch.bend as Dispatch
import ./ExecutionPhases.bend as Execution
import ./PublicationAuthority.bend as Authority


type Cause is Data:
  Ordinary{raw: P.Request, context: D.Context, origin: Source.JudgmentSyntactic}
  Cached{raw: P.Request, context: D.Context, entry: G.Entry}


def mode(cause: Cause) -> Bool:
  match cause:
    case Ordinary{raw, context, origin}: False{}
    case Cached{raw, context, entry}: True{}


def request(cause: Cause) -> P.Request:
  match cause:
    case Ordinary{raw, context, origin}: raw
    case Cached{raw, context, entry}: H.resolved(raw, entry)


def context(cause: Cause) -> D.Context:
  match cause:
    case Ordinary{raw, context, origin}: context
    case Cached{raw, context, entry}: context


def origin(public: List<&2, Source.FileSource>, cause: Cause) -> Source.JudgmentSyntactic:
  match cause:
    case Ordinary{raw, context, origin}: origin
    case Cached{raw, context, entry}: Host.origin(public, I.code(H.resolved(raw, entry)))


def checker(primitives: Dispatch.Primitives) -> V.CheckerReturn:
  Dispatch.Primitives{checker, allocation, seal, cleanup, artifact, execution, send} = primitives
  checker


def artifact(primitives: Dispatch.Primitives) -> Dispatch.ArtifactReturn:
  Dispatch.Primitives{checker, allocation, seal, cleanup, artifact, execution, send} = primitives
  artifact


def Allowed(~c: S.Configuration, ~public: List<&2, Source.FileSource>, +before: E.Snapshot,
  -decision: Decode.Decision, +primitives: Dispatch.Primitives, cause: Cause) -> Type:
  match cause:
    case Ordinary{+raw, context, origin}:
      L.E<{decision == Decode.Parsed{W.Ordinary{raw}} : Decode.Decision},
        L.E<{D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
          L.E<{Binding.ordinary(public, raw, context) == Some{origin} : Maybe<&2, Source.JudgmentSyntactic>}, {checker(primitives) == V.CheckerAccepted{} : V.CheckerReturn}>>>
    case Cached{+raw, context, entry}:
      L.E<{decision == Decode.Parsed{W.Extension{W.Execute{}, raw}} : Decode.Decision},
        L.E<{Cached.choose(E.instance(before), Host.Published{E.database(before), E.last_response(before), E.registry(before)}, raw) == Cached.Selected{context, entry} : Cached.Choice},
          {artifact(primitives) == Dispatch.ArtifactAvailable{} : Dispatch.ArtifactReturn}>>


def Claim(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +before: E.Snapshot,
  -decision: Decode.Decision, -primitives: Dispatch.Primitives, +event: O.AuditEvent) -> Type:
  match event:
    case O.Publication{actual_mode, response, bytes, actual_before, after}:
      &cause: Cause -> L.E<Allowed(c, public, before, decision, primitives, cause),
        Authority.Claim(c, binding, origin(public, cause), mode(cause), request(cause), context(cause), before,
          O.Publication{actual_mode, response, bytes, actual_before, after})>
    case _: Unit


def NoPublication(event: O.AuditEvent) -> Type:
  match event:
    case O.Publication{actual_mode, response, bytes, before, after}: Empty
    case _: Unit


def Quiet(events: List<&2, O.AuditEvent>) -> Type:
  match events:
    case Nil{}: Unit
    case Con{event, rest}: L.E<NoPublication(event), Quiet(rest)>


def quiet_core(+mode: Bool, +code: String, frames: List<&2, Q.Frame>) -> Quiet(C.core(mode, code, frames)):
  match frames:
    case Nil{}: Unit{}
    case Con{frame, rest}: L.Both{Unit{}, quiet_core(mode, code, rest)}


def quiet_bound_core(+mode: Bool, +origin: Source.JudgmentSyntactic, frames: List<&2, Q.Frame>) -> Quiet(C.bound_core(mode, origin, frames)):
  match frames:
    case Nil{}: Unit{}
    case Con{frame, rest}: L.Both{Unit{}, quiet_bound_core(mode, origin, rest)}


def quiet_preparation(events: List<&2, V.PreparationEvent>) -> Quiet(C.prepare_events(events)):
  match events:
    case Nil{}: Unit{}
    case Con{event, rest}: L.Both{Unit{}, quiet_preparation(rest)}


def quiet_invalidation(events: List<&2, N.InvalidationEvent>) -> Quiet(C.invalidate_events(events)):
  match events:
    case Nil{}: Unit{}
    case Con{event, rest}: L.Both{Unit{}, quiet_invalidation(rest)}


def quiet_append(+prefix: List<&2, O.AuditEvent>, +suffix: List<&2, O.AuditEvent>, first: Quiet(prefix), later: Quiet(suffix)) -> Quiet(C.append(prefix, suffix)):
  match prefix first:
    case Nil{} _: later
    case Con{head, rest} L.Both{silent, following}: L.Both{silent, quiet_append(rest, suffix, following, later)}


def quiet_prefix(+events: List<&2, O.AuditEvent>, +run: C.CallRun, first: Quiet(events), later: Quiet(C.events(run))) -> Quiet(C.events(C.prefix(events, run))):
  C.CallRun{suffix, snapshot, result, waiting, closed} = run
  quiet_append(events, suffix, first, later)


def quiet_delivery(+mode: Bool, +code: String, +after: E.Snapshot, result: E.Outcome, +bytes: List<&2, U32>, +closes: Bool, send: V.SendReturn) -> Quiet(C.events(C.delivery(mode, code, after, result, bytes, closes, send))):
  match send:
    case V.SendPending{}: Unit{}
    case V.SendComplete{}: quiet_core(mode, code, Route.render_delivery(E.database(after), bytes, closes, Route.Complete{False{}}))
    case V.SendInterrupted{prefix}: quiet_core(mode, code, Route.render_delivery(E.database(after), bytes, closes, Route.Broken{prefix}))


def quiet_error_framed(+mode: Bool, +code: String, +before: E.Snapshot, +status: S.Status, +closes: Bool, +send: V.SendReturn, frame: Maybe<&2, List<&2, U32>>) -> Quiet(C.events(C.error_framed(mode, code, before, status, closes, send, frame))):
  match frame:
    case None{}: Unit{}
    case Some{+bytes}:
      quiet_prefix(C.core(mode, code, [Q.Prepared{S.response_error(status), bytes}, Q.Completed{S.response_error(status), E.database(before), closes}]),
        C.delivery(mode, code, before, E.Transaction{S.response_error(status)}, bytes, closes, send),
        quiet_core(mode, code, [Q.Prepared{S.response_error(status), bytes}, Q.Completed{S.response_error(status), E.database(before), closes}]),
        quiet_delivery(mode, code, before, E.Transaction{S.response_error(status)}, bytes, closes, send))


def quiet_error(+mode: Bool, code: String, before: E.Snapshot, +status: S.Status, closes: Bool, send: V.SendReturn) -> Quiet(C.events(C.error(mode, code, before, status, closes, send))):
  quiet_error_framed(mode, code, before, status, closes, send, P.frame(S.response_value(S.response_error(status))))


def quiet_failed(+mode: Bool, +code: String, +before: E.Snapshot, +stage: X.Stage, +identifier: String, fatal: Bool, +send: V.SendReturn) -> Quiet(C.events(C.failed(mode, code, before, stage, identifier, fatal, send))):
  match fatal:
    case True{}: quiet_core(mode, code, [Q.Failed{stage, identifier, True{}}, Q.Closed{}])
    case False{}:
      quiet_prefix(C.core(mode, code, [Q.Failed{stage, identifier, False{}}]), C.error(mode, code, before, S.Failure{}, False{}, send), quiet_core(mode, code, [Q.Failed{stage, identifier, False{}}]), quiet_error(mode, code, before, S.Failure{}, False{}, send))



def Run(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +before: E.Snapshot,
  -decision: Decode.Decision, -primitives: Dispatch.Primitives, +run: C.CallRun) -> Type:
  L.Disjunction<Quiet(C.events(run)), &cause: Cause -> L.E<Allowed(c, public, before, decision, primitives, cause),
    Authority.All(c, binding, origin(public, cause), mode(cause), request(cause), context(cause), before, C.events(run))>>


def quiet_authority_event(~c: S.Configuration, ~binding: Source.Source, -origin: Source.JudgmentSyntactic, -mode: Bool,
  -request: P.Request, -context: D.Context, +before: E.Snapshot, +event: O.AuditEvent, silent: NoPublication(event)) ->
  Authority.Claim(c, binding, origin, mode, request, context, before, event):
  match event:
    case O.Core{actual_mode, code, frame}: Unit{}
    case O.BoundCore{actual_mode, origin, frame}: Unit{}
    case O.Preparation{phase}: Unit{}
    case O.Invalidation{phase}: Unit{}
    case O.Selection{snapshot}: Unit{}
    case O.Resolution{raw, entry, context}: Unit{}
    case O.Publication{actual_mode, response, bytes, actual_before, after}:
      L.ex_false(Authority.Claim(c, binding, origin, mode, request, context, before, O.Publication{actual_mode, response, bytes, actual_before, after}), silent)


def quiet_authority_all(~c: S.Configuration, ~binding: Source.Source, -origin: Source.JudgmentSyntactic, -mode: Bool,
  -request: P.Request, -context: D.Context, +before: E.Snapshot, events: List<&2, O.AuditEvent>, silent: Quiet(events)) ->
  Authority.All(c, binding, origin, mode, request, context, before, events):
  match events silent:
    case Nil{} _: Unit{}
    case Con{+event, rest} L.Both{first, later}:
      L.Both{quiet_authority_event(c, binding, origin, mode, request, context, before, event, first), quiet_authority_all(c, binding, origin, mode, request, context, before, rest, later)}


def prefix_run(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +before: E.Snapshot,
  -decision: Decode.Decision, -primitives: Dispatch.Primitives, +events: List<&2, O.AuditEvent>, +run: C.CallRun,
  silent: Quiet(events), actual: Run(c, binding, public, before, decision, primitives, run)) -> Run(c, binding, public, before, decision, primitives, C.prefix(events, run)):
  match actual:
    case L.Left{quiet}: L.Left{quiet_prefix(events, run, silent, quiet)}
    case L.Right{(+cause, L.Both{allowed, all})}:
      L.Right{(cause, L.Both{allowed, Authority.prefix(c, binding, origin(public, cause), mode(cause), request(cause), context(cause), before, events, run,
        quiet_authority_all(c, binding, origin(public, cause), mode(cause), request(cause), context(cause), before, events, silent), all)})}


def execution(primitives: Dispatch.Primitives) -> Execution.Request:
  Dispatch.Primitives{checker, allocation, seal, cleanup, artifact, execution, send} = primitives
  execution


def ordinary_bound(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, +raw: P.Request, +ctx: D.Context, +origin: Maybe<&2, Source.JudgmentSyntactic>, +primitives: Dispatch.Primitives,
  authenticated: {D.authenticate(E.database(before), I.credential(raw)) == Some{ctx} : Maybe<&2, D.Context>},
  generated: {Binding.ordinary(public, raw, ctx) == origin : Maybe<&2, Source.JudgmentSyntactic>}) ->
  Run(c, binding, public, before, Decode.Parsed{W.Ordinary{raw}}, primitives,
    Dispatch.ordinary_bound(c, binding, origin, before, raw, ctx, checker(primitives), execution(primitives), Dispatch.send(primitives))):
  match origin primitives:
    case None{} _: L.Left{Unit{}}
    case Some{+origin} Dispatch.Primitives{checker, allocation, seal, cleanup, artifact, +execution, +send}:
      match checker:
        case V.CheckerPending{}: L.Left{Unit{}}
        case V.CheckerFailed{stage, identifier, fatal}: L.Left{quiet_failed(False{}, I.code(raw), before, stage, identifier, fatal, send)}
        case V.CheckerRefuted{}:
          L.Left{quiet_prefix([O.BoundCore{False{}, origin, Q.Rejected{raw, ctx}}], C.error(False{}, I.code(raw), before, S.Certificate{}, False{}, send),
            L.Both{Unit{}, Unit{}}, quiet_error(False{}, I.code(raw), before, S.Certificate{}, False{}, send))}
        case V.CheckerAccepted{}:
          L.Right{(Ordinary{raw, ctx, origin}, L.Both{L.Both{{==}, L.Both{authenticated, L.Both{generated, {==}}}},
            Authority.prefix(c, binding, origin, False{}, raw, ctx, before, [O.BoundCore{False{}, origin, Q.Accepts{raw, ctx}}],
              Execution.run_bound(c, binding, origin, False{}, raw, ctx, before, execution, send), L.Both{Unit{}, Unit{}},
              Authority.all_bound_execution_publications_reopen_the_exact_actual_core_and_preparation(c, binding, origin, False{}, raw, ctx, before, execution, send))})}


def ordinary_identity(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +authentication: Maybe<&2, D.Context>, +before: E.Snapshot, +raw: P.Request, +primitives: Dispatch.Primitives,
  same: {D.authenticate(E.database(before), I.credential(raw)) == authentication : Maybe<&2, D.Context>}) ->
  Run(c, binding, public, before, Decode.Parsed{W.Ordinary{raw}}, primitives, Dispatch.ordinary_identity(c, binding, public, authentication, before, raw, primitives)):
  match authentication:
    case None{}: L.Left{quiet_error(False{}, I.code(raw), before, S.Authentication{}, False{}, Dispatch.send(primitives))}
    case Some{+ctx}:
      match primitives:
        case Dispatch.Primitives{checker, allocation, seal, cleanup, artifact, execution, send}:
          ordinary_bound(c, binding, public, before, raw, ctx, Binding.ordinary(public, raw, ctx), Dispatch.Primitives{checker, allocation, seal, cleanup, artifact, execution, send}, same, {==})


def ordinary(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, +raw: P.Request, +primitives: Dispatch.Primitives) ->
  Run(c, binding, public, before, Decode.Parsed{W.Ordinary{raw}}, primitives, Dispatch.ordinary(c, binding, public, before, raw, primitives)):
  +identity = D.authenticate(E.database(before), I.credential(raw))
  prefix_run(c, binding, public, before, Decode.Parsed{W.Ordinary{raw}}, primitives,
    C.core(False{}, I.code(raw), [Q.Received{raw}, Q.Authenticated{raw, identity}]), Dispatch.ordinary_identity(c, binding, public, identity, before, raw, primitives),
    quiet_core(False{}, I.code(raw), [Q.Received{raw}, Q.Authenticated{raw, identity}]), ordinary_identity(c, binding, public, identity, before, raw, primitives, {==}))


def cached_artifact(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, +raw: P.Request, +ctx: D.Context, +entry: G.Entry, +primitives: Dispatch.Primitives,
  chosen: {Cached.choose(E.instance(before), Host.Published{E.database(before), E.last_response(before), E.registry(before)}, raw) == Cached.Selected{ctx, entry} : Cached.Choice}) ->
  Run(c, binding, public, before, Decode.Parsed{W.Extension{W.Execute{}, raw}}, primitives,
    Dispatch.cached_artifact(c, binding, public, artifact(primitives), before, raw, entry, ctx, execution(primitives), Dispatch.send(primitives))):
  match primitives:
    case Dispatch.Primitives{checker, allocation, seal, cleanup, artifact, +execution, +send}:
      match artifact:
        case Dispatch.ArtifactPending{}: L.Left{Unit{}}
        case Dispatch.ArtifactFailed{identifier, fatal}: L.Left{quiet_failed(True{}, G.code(entry), before, X.Verify{}, identifier, fatal, send)}
        case Dispatch.ArtifactAvailable{}:
          L.Right{(Cached{raw, ctx, entry}, L.Both{L.Both{{==}, L.Both{chosen, {==}}},
            Authority.prefix(c, binding, Host.origin(public, I.code(H.resolved(raw, entry))), True{}, H.resolved(raw, entry), ctx, before,
              [O.Resolution{raw, entry, ctx}], Execution.run(c, binding, public, True{}, H.resolved(raw, entry), ctx, before, execution, send), L.Both{Unit{}, Unit{}},
              Authority.all_cached_core_publications_reopen_the_original_actual_core_and_preparation(c, binding, public, True{}, H.resolved(raw, entry), ctx, before, execution, send))})}


def cached_choice(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +choice: Cached.Choice, +before: E.Snapshot, +raw: P.Request, +primitives: Dispatch.Primitives,
  chosen: {Cached.choose(E.instance(before), Host.Published{E.database(before), E.last_response(before), E.registry(before)}, raw) == choice : Cached.Choice}) ->
  Run(c, binding, public, before, Decode.Parsed{W.Extension{W.Execute{}, raw}}, primitives,
    Dispatch.cached_choice(c, binding, public, choice, before, raw, artifact(primitives), execution(primitives), Dispatch.send(primitives))):
  match choice:
    case Cached.Unauthenticated{}: L.Left{quiet_error(True{}, "", before, S.Authentication{}, False{}, Dispatch.send(primitives))}
    case Cached.BadProof{ctx}: L.Left{quiet_error(True{}, "", before, S.Input{}, False{}, Dispatch.send(primitives))}
    case Cached.Missing{ctx}: L.Left{quiet_error(True{}, "", before, S.Failure{}, False{}, Dispatch.send(primitives))}
    case Cached.Selected{ctx, entry}: cached_artifact(c, binding, public, before, raw, ctx, entry, primitives, chosen)


def cached(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, +raw: P.Request, +primitives: Dispatch.Primitives) ->
  Run(c, binding, public, before, Decode.Parsed{W.Extension{W.Execute{}, raw}}, primitives,
    Dispatch.cached(c, binding, public, before, raw, artifact(primitives), execution(primitives), Dispatch.send(primitives))):
  prefix_run(c, binding, public, before, Decode.Parsed{W.Extension{W.Execute{}, raw}}, primitives,
    [O.Preparation{V.WireReceived{W.Extension{W.Execute{}, raw}}}, O.Preparation{V.IdentityEstablished{W.Extension{W.Execute{}, raw}, D.authenticate(E.database(before), I.credential(raw))}}],
    Dispatch.cached_choice(c, binding, public, Cached.choose(E.instance(before), Host.Published{E.database(before), E.last_response(before), E.registry(before)}, raw),
      before, raw, artifact(primitives), execution(primitives), Dispatch.send(primitives)), L.Both{Unit{}, L.Both{Unit{}, Unit{}}},
    cached_choice(c, binding, public, Cached.choose(E.instance(before), Host.Published{E.database(before), E.last_response(before), E.registry(before)}, raw), before, raw, primitives, {==}))


def quiet_preparation_run(run: V.PreparationRun) -> Quiet(C.events(C.preparation(run))):
  V.PreparationRun{events, result, snapshot, waiting, closed} = run
  quiet_preparation(events)


def quiet_invalidation_run(run: N.InvalidationRun) -> Quiet(C.events(C.invalidation(run))):
  N.InvalidationRun{events, result, snapshot, waiting, closed} = run
  quiet_invalidation(events)


def extension(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +operation: W.Operation, +before: E.Snapshot, +raw: P.Request, +primitives: Dispatch.Primitives) ->
  Run(c, binding, public, before, Decode.Parsed{W.Extension{operation, raw}}, primitives, Dispatch.extension(c, binding, public, operation, before, raw, primitives)):
  match operation primitives:
    case W.Prepare{} Dispatch.Primitives{checker, allocation, seal, cleanup, artifact, execution, send}:
      L.Left{quiet_preparation_run(V.run(c, V.PrepareMode{}, raw, before, V.Returns{checker, allocation, seal, send}))}
    case W.PrepareRead{} Dispatch.Primitives{checker, allocation, seal, cleanup, artifact, execution, send}:
      L.Left{quiet_preparation_run(V.run(c, V.ReadMode{}, raw, before, V.Returns{checker, allocation, seal, send}))}
    case W.Invalidate{} Dispatch.Primitives{checker, allocation, seal, cleanup, artifact, execution, send}:
      L.Left{quiet_invalidation_run(N.run(c, before, raw, cleanup, send))}
    case W.Execute{} Dispatch.Primitives{checker, allocation, seal, cleanup, artifact, execution, send}:
      cached(c, binding, public, before, raw, Dispatch.Primitives{checker, allocation, seal, cleanup, artifact, execution, send})


def parsed(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, +wire: W.WireRequest, +primitives: Dispatch.Primitives) ->
  Run(c, binding, public, before, Decode.Parsed{wire}, primitives, Dispatch.parsed(c, binding, public, before, wire, primitives)):
  match wire:
    case W.Ordinary{raw}: ordinary(c, binding, public, before, raw, primitives)
    case W.Extension{operation, raw}: extension(c, binding, public, operation, before, raw, primitives)


def decoded_decision(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +decision: Decode.Decision, +before: E.Snapshot, +primitives: Dispatch.Primitives) ->
  Run(c, binding, public, before, decision, primitives, Dispatch.decoded_decision(c, binding, public, decision, before, primitives)):
  match decision:
    case Decode.Shutdown{}: L.Left{L.Both{Unit{}, Unit{}}}
    case Decode.TransportStopped{}: L.Left{Unit{}}
    case Decode.Reject{mode, status, closes}: L.Left{quiet_error(mode, "", before, status, closes, Dispatch.send(primitives))}
    case Decode.Parsed{wire}: parsed(c, binding, public, before, wire, primitives)


def decoded(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, +value: Decode.DecodeRun, +primitives: Dispatch.Primitives) ->
  Run(c, binding, public, before, Decode.decision(value), primitives, Dispatch.decoded(c, binding, public, before, value, primitives)):
  Decode.DecodeRun{+decision, +frames} = value
  prefix_run(c, binding, public, before, decision, primitives, C.core(Dispatch.decision_mode(decision), Dispatch.decision_code(decision), frames),
    Dispatch.decoded_decision(c, binding, public, decision, before, primitives), quiet_core(Dispatch.decision_mode(decision), Dispatch.decision_code(decision), frames),
    decoded_decision(c, binding, public, decision, before, primitives))


law every_actual_dispatch_preserves_its_real_bound_or_current_cached_execution_context:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +before: E.Snapshot
  for +input: X.Reception
  for +primitives: Dispatch.Primitives
  Run(c, binding, public, before, Decode.decision(Decode.run(c, E.database(before), input)), primitives, Dispatch.run(c, binding, public, before, input, primitives))
def every_actual_dispatch_preserves_its_real_bound_or_current_cached_execution_context(c, binding, public, before, input, primitives):
  decoded(c, binding, public, before, Decode.run(c, E.database(before), input), primitives)


def quiet_query(events: List<&2, O.AuditEvent>, index: Nat, -event: O.AuditEvent, silent: Quiet(events),
  found: {B.query(O.AuditEvent, events, index) == Some{event} : Maybe<&2, O.AuditEvent>}) -> NoPublication(event):
  match events index silent:
    case Nil{} _ _: L.ex_false(NoPublication(event), F.none_negative_some(O.AuditEvent, event, found))
    case Con{head, rest} 0n L.Both{first, later}:
      %F.some_injective(O.AuditEvent, head, event, found) : NoPublication(_)
      first
    case Con{head, rest} 1n+k L.Both{first, later}: quiet_query(rest, k, event, later, found)


def query_run(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +before: E.Snapshot,
  -decision: Decode.Decision, -primitives: Dispatch.Primitives, +run: C.CallRun, +index: Nat,
  +actual_mode: Bool, +response: S.Response, +bytes: List<&2, U32>, +actual_before: E.Snapshot, +after: E.Snapshot,
  actual: Run(c, binding, public, before, decision, primitives, run),
  found: {B.query(O.AuditEvent, C.events(run), index) == Some{O.Publication{actual_mode, response, bytes, actual_before, after}} : Maybe<&2, O.AuditEvent>}) ->
  Claim(c, binding, public, before, decision, primitives, O.Publication{actual_mode, response, bytes, actual_before, after}):
  match actual:
    case L.Left{silent}:
      L.ex_false(Claim(c, binding, public, before, decision, primitives, O.Publication{actual_mode, response, bytes, actual_before, after}),
        quiet_query(C.events(run), index, O.Publication{actual_mode, response, bytes, actual_before, after}, silent, found))
    case L.Right{(+cause, L.Both{allowed, all})}:
      (cause, L.Both{allowed, Authority.query_claim(c, binding, origin(public, cause), mode(cause), request(cause), context(cause), before, C.events(run), index,
        O.Publication{actual_mode, response, bytes, actual_before, after}, all, found)})


law every_actual_dispatch_publication_has_its_original_source_and_actual_core_preparation:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +before: E.Snapshot
  for +input: X.Reception
  for +primitives: Dispatch.Primitives
  for +index: Nat
  for +actual_mode: Bool
  for +response: S.Response
  for +bytes: List<&2, U32>
  for +actual_before: E.Snapshot
  for +after: E.Snapshot
  for found: {B.query(O.AuditEvent, C.events(Dispatch.run(c, binding, public, before, input, primitives)), index) ==
    Some{O.Publication{actual_mode, response, bytes, actual_before, after}} : Maybe<&2, O.AuditEvent>}
  Claim(c, binding, public, before, Decode.decision(Decode.run(c, E.database(before), input)), primitives,
    O.Publication{actual_mode, response, bytes, actual_before, after})
def every_actual_dispatch_publication_has_its_original_source_and_actual_core_preparation(c, binding, public, before, input, primitives, index, actual_mode, response, bytes, actual_before, after, found):
  query_run(c, binding, public, before, Decode.decision(Decode.run(c, E.database(before), input)), primitives, Dispatch.run(c, binding, public, before, input, primitives), index,
    actual_mode, response, bytes, actual_before, after, every_actual_dispatch_preserves_its_real_bound_or_current_cached_execution_context(c, binding, public, before, input, primitives), found)


def selected_context(choice: Cached.Choice) -> Maybe<&2, D.Context>:
  match choice:
    case Cached.Unauthenticated{}: None{}
    case Cached.BadProof{ctx}: Some{ctx}
    case Cached.Missing{ctx}: Some{ctx}
    case Cached.Selected{ctx, entry}: Some{ctx}


def lookup_context(+ctx: D.Context, found: Maybe<&2, G.Entry>) -> {selected_context(Cached.choose_lookup(ctx, found)) == Some{ctx} : Maybe<&2, D.Context>}:
  match found:
    case None{}: {==}
    case Some{entry}: {==}


def proof_context(empty: Bool, instance: String, entries: List<&2, G.Entry>, +raw: P.Request, +ctx: D.Context) ->
  {selected_context(Cached.choose_proof(empty, instance, entries, raw, ctx)) == Some{ctx} : Maybe<&2, D.Context>}:
  match empty:
    case False{}: {==}
    case True{}: lookup_context(ctx, G.lookup(instance, I.code(raw), entries))


def authentication_context(+identity: Maybe<&2, D.Context>, instance: String, entries: List<&2, G.Entry>, +raw: P.Request) ->
  {selected_context(Cached.choose_auth(identity, instance, entries, raw)) == identity : Maybe<&2, D.Context>}:
  match identity:
    case None{}: {==}
    case Some{ctx}: proof_context(String.eq(I.proof(raw), ""), instance, entries, raw, ctx)


def cached_selection_authenticates(+before: E.Snapshot, +raw: P.Request, +ctx: D.Context, +entry: G.Entry,
  chosen: {Cached.choose(E.instance(before), Host.Published{E.database(before), E.last_response(before), E.registry(before)}, raw) == Cached.Selected{ctx, entry} : Cached.Choice}) ->
  {D.authenticate(E.database(before), I.credential(raw)) == Some{ctx} : Maybe<&2, D.Context>}:
  Equal.trans(Maybe<&2, D.Context>, D.authenticate(E.database(before), I.credential(raw)),
    selected_context(Cached.choose(E.instance(before), Host.Published{E.database(before), E.last_response(before), E.registry(before)}, raw)), Some{ctx},
    Equal.sym(Maybe<&2, D.Context>, selected_context(Cached.choose(E.instance(before), Host.Published{E.database(before), E.last_response(before), E.registry(before)}, raw)),
      D.authenticate(E.database(before), I.credential(raw)),
      authentication_context(D.authenticate(E.database(before), I.credential(raw)), E.instance(before), E.registry(before), raw)),
    Equal.cong(Cached.Choice, Maybe<&2, D.Context>, selected_context,
      Cached.choose(E.instance(before), Host.Published{E.database(before), E.last_response(before), E.registry(before)}, raw), Cached.Selected{ctx, entry}, chosen))


def resolved_credential(+raw: P.Request, +entry: G.Entry) -> {I.credential(H.resolved(raw, entry)) == I.credential(raw) : String}:
  P.Request{credential, code, arguments, proof} = raw
  {==}


# These are ORIGINAL source declarations. The ordinary branch is the exact
# generated closure checked for this call; cached execution specializes its
# registered original universal certificate, rather than admitting new code.
def Original(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +cause: Cause) -> Type:
  match cause:
    case Ordinary{raw, ctx, origin}: Source.JudgmentAccepted(binding, c, raw, ctx, origin)
    case Cached{+raw, +ctx, +entry}:
      R.Certifies(c, I.code(H.resolved(raw, entry)), Source.program(binding, Host.origin(public, I.code(H.resolved(raw, entry)))), ctx, I.arguments(H.resolved(raw, entry)))


# Internal composition only. The complete source query theorem above DERIVES
# both Allowed and the actual Core/prepare/conclude Claim. No field certifies
# an arbitrary runtime result; only prior-state validity is assumed here.
def publication_preserves_validity_from_its_original_source_context(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, -decision: Decode.Decision, -primitives: Dispatch.Primitives, +cause: Cause,
  +actual_mode: Bool, +response: S.Response, +bytes: List<&2, U32>, +actual_before: E.Snapshot, +after: E.Snapshot,
  allowed: Allowed(c, public, before, decision, primitives, cause), original: Original(c, binding, public, cause),
  actual: Authority.Claim(c, binding, origin(public, cause), mode(cause), request(cause), context(cause), before, O.Publication{actual_mode, response, bytes, actual_before, after}),
  valid: R.Valid(c, E.database(before))) -> R.Valid(c, E.database(after)):
  match cause allowed:
    case Ordinary{raw, ctx, origin} L.Both{wire, L.Both{authenticated, L.Both{generated, checked}}}:
      Authority.an_actual_checked_publication_is_valid_from_the_prior_state_and_original_declaration(c, binding, origin, False{}, raw, ctx, before, actual_mode, response, bytes, actual_before, after,
        original, authenticated, valid, actual)
    case Cached{+raw, +ctx, +entry} L.Both{wire, L.Both{chosen, available}}:
      Authority.certified_publication_preserves_validity(c, binding, Host.origin(public, I.code(H.resolved(raw, entry))), True{}, H.resolved(raw, entry), ctx, before,
        actual_mode, response, bytes, actual_before, after, original,
        Equal.trans(Maybe<&2, D.Context>, D.authenticate(E.database(before), I.credential(H.resolved(raw, entry))), D.authenticate(E.database(before), I.credential(raw)), Some{ctx},
          Equal.cong(String, Maybe<&2, D.Context>, credential => D.authenticate(E.database(before), credential), I.credential(H.resolved(raw, entry)), I.credential(raw), resolved_credential(raw, entry)),
          cached_selection_authenticates(before, raw, ctx, entry, chosen)), valid, actual)
