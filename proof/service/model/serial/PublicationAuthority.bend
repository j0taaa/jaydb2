# Publication authority from the actual Core/prepare/conclude dispatcher,
# including fatal post-store prefixes with no completed result. No arbitrary
# runtime result certification, final validity or target law is a premise.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Interface.bend as I
import ../../../../contract/Logic.bend as L
import ../../../../contract/Protocol.bend as P
import ../../../../contract/Requirements.bend as R
import ../../../../contract/Resources.bend as X
import ../../../../contract/Semantics.bend as S
import ../../../../src/Core.bend as Core
import ../../../ExecutionService.bend as Execute
import ../../../Foundations.bend as F
import ../../../HistoryService.bend as History
import ../../../Publication.bend as Publication
import ../../../HostTransitions.bend as Host
import ../../../ProtocolService.bend as Q
import ../../../RoutesService.bend as Route
import ../../../SourceService.bend as Source
import ../../specification/ServiceLaws.bend as E
import ../../phases/PreparePhases.bend as V
import ../EventObserver.bend as O
import ../FrameBounds.bend as B
import ./Common.bend as C
import ./ExecutionPhases.bend as Execution


type Finished is Data:
  Finished{steps: Nat, working: D.State, events: List<&2, S.OperationEvent>, proposal: S.Response, prepared: Core.Prepared}


def prepared(finished: Finished) -> Core.Prepared:
  Finished{steps, working, events, proposal, prepared} = finished
  prepared


def response_status(response: S.Response) -> S.Status:
  S.Response{status, value} = response
  status


def Real(~c: S.Configuration, ~binding: Source.Source, -origin: Source.JudgmentSyntactic,
  -request: P.Request, -context: D.Context, -before: E.Snapshot, finished: Finished) -> Type:
  Finished{steps, working, events, proposal, prepared} = finished
  L.E<{Core.traverse(steps, Core.start(Source.program(binding, origin), context, I.arguments(request), E.database(before)), S.schema(c)) == S.Final{working, events, proposal} : S.Trace},
    {Core.prepare(Core.Stopped{working, events, proposal}, c) == Some{prepared} : Maybe<&2, Core.Prepared>}>


def Claim(~c: S.Configuration, ~binding: Source.Source, -origin: Source.JudgmentSyntactic,
  -mode: Bool, -request: P.Request, -context: D.Context, +before: E.Snapshot, event: O.AuditEvent) -> Type:
  match event:
    case O.Publication{actual_mode, response, bytes, actual_before, +after}:
      &finished: Finished -> L.E<Real(c, binding, origin, request, context, before, finished),
        L.E<{actual_mode == mode : Bool}, L.E<{actual_before == before : E.Snapshot},
          L.E<{Core.conclude(prepared(finished), E.database(before)) == Core.Conclusion{E.database(after), response, bytes} : Core.Conclusion},
            L.E<{response_status(response) == S.Success{} : S.Status},
              {after == E.Snapshot{E.instance(before), E.database(after), bytes, E.registry(before)} : E.Snapshot}>>>>>
    case _: Unit


def All(~c: S.Configuration, ~binding: Source.Source, -origin: Source.JudgmentSyntactic,
  -mode: Bool, -request: P.Request, -context: D.Context, +before: E.Snapshot, events: List<&2, O.AuditEvent>) -> Type:
  match events:
    case Nil{}: Unit
    case Con{event, rest}: L.E<Claim(c, binding, origin, mode, request, context, before, event), All(c, binding, origin, mode, request, context, before, rest)>


def append(~c: S.Configuration, ~binding: Source.Source, -origin: Source.JudgmentSyntactic, -mode: Bool, -request: P.Request, -context: D.Context, +before: E.Snapshot,
  +prefix: List<&2, O.AuditEvent>, +suffix: List<&2, O.AuditEvent>, first: All(c, binding, origin, mode, request, context, before, prefix), later: All(c, binding, origin, mode, request, context, before, suffix)) ->
  All(c, binding, origin, mode, request, context, before, C.append(prefix, suffix)):
  match prefix first:
    case Nil{} _: later
    case Con{head, rest} L.Both{claim, following}: L.Both{claim, append(c, binding, origin, mode, request, context, before, rest, suffix, following, later)}


def prefix(~c: S.Configuration, ~binding: Source.Source, -origin: Source.JudgmentSyntactic, -mode: Bool, -request: P.Request, -context: D.Context, +before: E.Snapshot,
  +events: List<&2, O.AuditEvent>, +run: C.CallRun, first: All(c, binding, origin, mode, request, context, before, events), later: All(c, binding, origin, mode, request, context, before, C.events(run))) ->
  All(c, binding, origin, mode, request, context, before, C.events(C.prefix(events, run))):
  C.CallRun{suffix, snapshot, result, waiting, closed} = run
  append(c, binding, origin, mode, request, context, before, events, suffix, first, later)


def core(~c: S.Configuration, ~binding: Source.Source, -origin: Source.JudgmentSyntactic, -mode: Bool, -request: P.Request, -context: D.Context, +before: E.Snapshot,
  +actual_mode: Bool, +code: String, frames: List<&2, Q.Frame>) -> All(c, binding, origin, mode, request, context, before, C.core(actual_mode, code, frames)):
  match frames:
    case Nil{}: Unit{}
    case Con{frame, rest}: L.Both{Unit{}, core(c, binding, origin, mode, request, context, before, actual_mode, code, rest)}


def bound_core(~c: S.Configuration, ~binding: Source.Source, -origin: Source.JudgmentSyntactic, -mode: Bool, -request: P.Request, -context: D.Context, +before: E.Snapshot,
  +actual_mode: Bool, +actual_origin: Source.JudgmentSyntactic, frames: List<&2, Q.Frame>) -> All(c, binding, origin, mode, request, context, before, C.bound_core(actual_mode, actual_origin, frames)):
  match frames:
    case Nil{}: Unit{}
    case Con{frame, rest}: L.Both{Unit{}, bound_core(c, binding, origin, mode, request, context, before, actual_mode, actual_origin, rest)}


def delivery(~c: S.Configuration, ~binding: Source.Source, -origin: Source.JudgmentSyntactic, -mode: Bool, -request: P.Request, -context: D.Context, +before: E.Snapshot,
  +actual_mode: Bool, +code: String, +after: E.Snapshot, result: E.Outcome, +bytes: List<&2, U32>, +closes: Bool, send: V.SendReturn) ->
  All(c, binding, origin, mode, request, context, before, C.events(C.delivery(actual_mode, code, after, result, bytes, closes, send))):
  match send:
    case V.SendPending{}: Unit{}
    case V.SendComplete{}: core(c, binding, origin, mode, request, context, before, actual_mode, code, Route.render_delivery(E.database(after), bytes, closes, Route.Complete{False{}}))
    case V.SendInterrupted{prefix}: core(c, binding, origin, mode, request, context, before, actual_mode, code, Route.render_delivery(E.database(after), bytes, closes, Route.Broken{prefix}))


def error_framed(~c: S.Configuration, ~binding: Source.Source, -origin: Source.JudgmentSyntactic, -mode: Bool, -request: P.Request, -context: D.Context, +before: E.Snapshot,
  +actual_mode: Bool, +code: String, +snapshot: E.Snapshot, +status: S.Status, +closes: Bool, +send: V.SendReturn, frame: Maybe<&2, List<&2, U32>>) ->
  All(c, binding, origin, mode, request, context, before, C.events(C.error_framed(actual_mode, code, snapshot, status, closes, send, frame))):
  match frame:
    case None{}: Unit{}
    case Some{+bytes}:
      prefix(c, binding, origin, mode, request, context, before, C.core(actual_mode, code, [Q.Prepared{S.response_error(status), bytes}, Q.Completed{S.response_error(status), E.database(snapshot), closes}]),
        C.delivery(actual_mode, code, snapshot, E.Transaction{S.response_error(status)}, bytes, closes, send),
        core(c, binding, origin, mode, request, context, before, actual_mode, code, [Q.Prepared{S.response_error(status), bytes}, Q.Completed{S.response_error(status), E.database(snapshot), closes}]),
        delivery(c, binding, origin, mode, request, context, before, actual_mode, code, snapshot, E.Transaction{S.response_error(status)}, bytes, closes, send))


def failed(~c: S.Configuration, ~binding: Source.Source, -origin: Source.JudgmentSyntactic, -mode: Bool, -request: P.Request, -context: D.Context, +before: E.Snapshot,
  +actual_mode: Bool, +code: String, +snapshot: E.Snapshot, +stage: X.Stage, +identifier: String, fatal: Bool, +send: V.SendReturn) ->
  All(c, binding, origin, mode, request, context, before, C.events(C.failed(actual_mode, code, snapshot, stage, identifier, fatal, send))):
  match fatal:
    case True{}: core(c, binding, origin, mode, request, context, before, actual_mode, code, [Q.Failed{stage, identifier, True{}}, Q.Closed{}])
    case False{}:
      prefix(c, binding, origin, mode, request, context, before, C.core(actual_mode, code, [Q.Failed{stage, identifier, False{}}]), C.error(actual_mode, code, snapshot, S.Failure{}, False{}, send),
        core(c, binding, origin, mode, request, context, before, actual_mode, code, [Q.Failed{stage, identifier, False{}}]),
        error_framed(c, binding, origin, mode, request, context, before, actual_mode, code, snapshot, S.Failure{}, False{}, send, P.frame(S.response_value(S.response_error(S.Failure{})))))


def conclusion_response(conclusion: Core.Conclusion) -> S.Response:
  Core.Conclusion{state, response, bytes} = conclusion
  response


def conclusion_bytes(conclusion: Core.Conclusion) -> List<&2, U32>:
  Core.Conclusion{state, response, bytes} = conclusion
  bytes


def emitted_publication(~c: S.Configuration, ~binding: Source.Source, +origin: Source.JudgmentSyntactic, +mode: Bool, +request: P.Request, +context: D.Context, +before: E.Snapshot,
  +finished: Finished, +conclusion: Core.Conclusion, real: Real(c, binding, origin, request, context, before, finished),
  concluded: {Core.conclude(prepared(finished), E.database(before)) == conclusion : Core.Conclusion}) ->
  All(c, binding, origin, mode, request, context, before,
    Execution.publication(mode, before, Execution.published(before, conclusion), conclusion_response(conclusion), conclusion_bytes(conclusion))):
  match conclusion:
    case Core.Conclusion{state, S.Response{status, value}, bytes}:
      match status:
        case S.Success{}:
          L.Both{(finished, L.Both{real, L.Both{{==}, L.Both{{==}, L.Both{concluded, L.Both{{==}, {==}}}}}}), Unit{}}
        case S.Input{}: Unit{}
        case S.Authentication{}: Unit{}
        case S.Certificate{}: Unit{}
        case S.DataError{}: Unit{}
        case S.Limit{}: Unit{}
        case S.Failure{}: Unit{}
        case S.Refusal{}: Unit{}


def concluded_claims(~c: S.Configuration, ~binding: Source.Source, +origin: Source.JudgmentSyntactic, +mode: Bool, +request: P.Request, +context: D.Context, +before: E.Snapshot,
  +code: String, +finished: Finished, +conclusion: Core.Conclusion, +send: V.SendReturn, real: Real(c, binding, origin, request, context, before, finished),
  obtained: {Core.conclude(prepared(finished), E.database(before)) == conclusion : Core.Conclusion}) ->
  All(c, binding, origin, mode, request, context, before, C.events(Execution.concluded(mode, code, before, conclusion, send))):
  match conclusion:
    case Core.Conclusion{+state, +response, +bytes}:
      +after = Execution.published(before, Core.Conclusion{state, response, bytes})
      prefix(c, binding, origin, mode, request, context, before,
        C.append([O.Core{mode, code, Q.Prepared{response, bytes}}], C.append(Execution.publication(mode, before, after, response, bytes), [O.Core{mode, code, Q.Completed{response, E.database(after), False{}}}])),
        C.delivery(mode, code, after, E.Transaction{response}, bytes, False{}, send),
        append(c, binding, origin, mode, request, context, before, [O.Core{mode, code, Q.Prepared{response, bytes}}],
          C.append(Execution.publication(mode, before, after, response, bytes), [O.Core{mode, code, Q.Completed{response, E.database(after), False{}}}]), L.Both{Unit{}, Unit{}},
          append(c, binding, origin, mode, request, context, before, Execution.publication(mode, before, after, response, bytes), [O.Core{mode, code, Q.Completed{response, E.database(after), False{}}}],
            emitted_publication(c, binding, origin, mode, request, context, before, finished, Core.Conclusion{state, response, bytes}, real, obtained), L.Both{Unit{}, Unit{}})),
        delivery(c, binding, origin, mode, request, context, before, mode, code, after, E.Transaction{response}, bytes, False{}, send))


def fatal_after_store_claims(~c: S.Configuration, ~binding: Source.Source, +origin: Source.JudgmentSyntactic, +mode: Bool, +request: P.Request, +context: D.Context, +before: E.Snapshot,
  +code: String, +finished: Finished, +conclusion: Core.Conclusion, +stage: X.Stage, +identifier: String,
  real: Real(c, binding, origin, request, context, before, finished), obtained: {Core.conclude(prepared(finished), E.database(before)) == conclusion : Core.Conclusion}) ->
  All(c, binding, origin, mode, request, context, before, C.events(Execution.fatal_after_store(mode, code, before, conclusion, stage, identifier))):
  match conclusion:
    case Core.Conclusion{+state, +response, +bytes}:
      +after = Execution.published(before, Core.Conclusion{state, response, bytes})
      append(c, binding, origin, mode, request, context, before, [O.Core{mode, code, Q.Prepared{response, bytes}}],
        C.append(Execution.publication(mode, before, after, response, bytes), C.core(mode, code, [Q.Failed{stage, identifier, True{}}, Q.Closed{}])), L.Both{Unit{}, Unit{}},
        append(c, binding, origin, mode, request, context, before, Execution.publication(mode, before, after, response, bytes), C.core(mode, code, [Q.Failed{stage, identifier, True{}}, Q.Closed{}]),
          emitted_publication(c, binding, origin, mode, request, context, before, finished, Core.Conclusion{state, response, bytes}, real, obtained),
          core(c, binding, origin, mode, request, context, before, mode, code, [Q.Failed{stage, identifier, True{}}, Q.Closed{}])))


def cleanup_claims(~c: S.Configuration, ~binding: Source.Source, +origin: Source.JudgmentSyntactic, +mode: Bool, +request: P.Request, +context: D.Context, +before: E.Snapshot,
  +code: String, +finished: Finished, +cleanup: Route.Cleanup, +send: V.SendReturn, real: Real(c, binding, origin, request, context, before, finished)) ->
  All(c, binding, origin, mode, request, context, before, C.events(Execution.cleanup(mode, code, before, prepared(finished), cleanup, send))):
  match cleanup:
    case Route.Clears{}:
      concluded_claims(c, binding, origin, mode, request, context, before, code, finished, Core.conclude(prepared(finished), E.database(before)), send, real, {==})
    case Route.FatalAfterStore{stage, identifier}:
      fatal_after_store_claims(c, binding, origin, mode, request, context, before, code, finished, Core.conclude(prepared(finished), E.database(before)), stage, identifier, real, {==})
    case Route.PendingCleanup{}:
      prefix(c, binding, origin, mode, request, context, before, C.core(mode, code, [Route.frame_prepared(prepared(finished))]), C.pending(before),
        core(c, binding, origin, mode, request, context, before, mode, code, [Route.frame_prepared(prepared(finished))]), Unit{})
    case Route.ErrorCleanup{identifier, fatal}:
      prefix(c, binding, origin, mode, request, context, before, C.core(mode, code, [Route.frame_prepared(prepared(finished))]), C.failed(mode, code, before, X.Prepare{}, identifier, fatal, send),
        core(c, binding, origin, mode, request, context, before, mode, code, [Route.frame_prepared(prepared(finished))]),
        failed(c, binding, origin, mode, request, context, before, mode, code, before, X.Prepare{}, identifier, fatal, send))


def prepared_result_claims(~c: S.Configuration, ~binding: Source.Source, +origin: Source.JudgmentSyntactic, +mode: Bool, +request: P.Request, +context: D.Context, +before: E.Snapshot,
  +code: String, +steps: Nat, +working: D.State, +events: List<&2, S.OperationEvent>, +proposal: S.Response, +result: Maybe<&2, Core.Prepared>, +cleanup: Route.Cleanup, +send: V.SendReturn,
  traced: {Core.traverse(steps, Core.start(Source.program(binding, origin), context, I.arguments(request), E.database(before)), S.schema(c)) == S.Final{working, events, proposal} : S.Trace},
  framed: {Core.prepare(Core.Stopped{working, events, proposal}, c) == result : Maybe<&2, Core.Prepared>}) ->
  All(c, binding, origin, mode, request, context, before, C.events(Execution.prepared_result(mode, code, before, result, cleanup, send))):
  match result:
    case None{}: Unit{}
    case Some{prepared}:
      cleanup_claims(c, binding, origin, mode, request, context, before, code, Finished{steps, working, events, proposal, prepared}, cleanup, send, L.Both{traced, framed})


def trace_result_claims(~c: S.Configuration, ~binding: Source.Source, +origin: Source.JudgmentSyntactic, +mode: Bool, +request: P.Request, +context: D.Context, +before: E.Snapshot,
  +code: String, +steps: Nat, +end: Execution.End, +trace: S.Trace, +send: V.SendReturn,
  traced: {Core.traverse(steps, Core.start(Source.program(binding, origin), context, I.arguments(request), E.database(before)), S.schema(c)) == trace : S.Trace}) ->
  All(c, binding, origin, mode, request, context, before, C.events(Execution.trace_result(c, mode, code, before, end, trace, send))):
  match end:
    case Execution.PrefixPending{}: Unit{}
    case Execution.PrefixFailed{identifier, fatal}: failed(c, binding, origin, mode, request, context, before, mode, code, before, X.Execute{}, identifier, fatal, send)
    case Execution.FinishPrefix{cleanup}:
      match trace:
        case S.Prefix{working, events}: Unit{}
        case S.Final{+working, +events, +proposal}:
          prepared_result_claims(c, binding, origin, mode, request, context, before, code, steps, working, events, proposal, Core.prepare(Core.Stopped{working, events, proposal}, c), cleanup, send, traced, {==})


def executed_bound_prefix_claims(~c: S.Configuration, ~binding: Source.Source, +origin: Source.JudgmentSyntactic, +mode: Bool,
  +request: P.Request, +context: D.Context, +before: E.Snapshot, +steps: Nat, +end: Execution.End, +send: V.SendReturn) ->
  All(c, binding, origin, mode, request, context, before, C.events(Execution.executed_bound_prefix(c, binding, origin, mode, request, context, before, steps, end, send))):
  prefix(c, binding, origin, mode, request, context, before,
    C.bound_core(mode, origin, Con{Q.Started{request, context}, Q.expand_exec(request, context, Execute.generate(steps, Core.start(Source.program(binding, origin), context, I.arguments(request), E.database(before)), S.schema(c)))}),
    Execution.trace_result(c, mode, I.code(request), before, end, Core.traverse(steps, Core.start(Source.program(binding, origin), context, I.arguments(request), E.database(before)), S.schema(c)), send),
    bound_core(c, binding, origin, mode, request, context, before, mode, origin, Con{Q.Started{request, context}, Q.expand_exec(request, context, Execute.generate(steps, Core.start(Source.program(binding, origin), context, I.arguments(request), E.database(before)), S.schema(c)))}),
    trace_result_claims(c, binding, origin, mode, request, context, before, I.code(request), steps, end,
      Core.traverse(steps, Core.start(Source.program(binding, origin), context, I.arguments(request), E.database(before)), S.schema(c)), send, {==}))


law all_bound_execution_publications_reopen_the_exact_actual_core_and_preparation:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for +origin: Source.JudgmentSyntactic
  for +mode: Bool
  for +request: P.Request
  for +context: D.Context
  for +before: E.Snapshot
  for +execution: Execution.Request
  for +send: V.SendReturn
  All(c, binding, origin, mode, request, context, before, C.events(Execution.run_bound(c, binding, origin, mode, request, context, before, execution, send)))
def all_bound_execution_publications_reopen_the_exact_actual_core_and_preparation(c, binding, origin, mode, request, context, before, execution, send):
  match execution:
    case Execution.StartPending{}: Unit{}
    case Execution.StartFailed{identifier, fatal}: failed(c, binding, origin, mode, request, context, before, mode, I.code(request), before, X.Execute{}, identifier, fatal, send)
    case Execution.RunPrefix{steps, end}: executed_bound_prefix_claims(c, binding, origin, mode, request, context, before, steps, end, send)


def executed_prefix_claims(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +mode: Bool,
  +request: P.Request, +context: D.Context, +before: E.Snapshot, +steps: Nat, +end: Execution.End, +send: V.SendReturn) ->
  All(c, binding, Host.origin(public, I.code(request)), mode, request, context, before, C.events(Execution.executed_prefix(c, binding, public, mode, request, context, before, steps, end, send))):
  +origin = Host.origin(public, I.code(request))
  prefix(c, binding, origin, mode, request, context, before,
    C.core(mode, I.code(request), Con{Q.Started{request, context}, Q.expand_exec(request, context, Execute.generate(steps, Core.start(Source.program(binding, origin), context, I.arguments(request), E.database(before)), S.schema(c)))}),
    Execution.trace_result(c, mode, I.code(request), before, end, Core.traverse(steps, Core.start(Source.program(binding, origin), context, I.arguments(request), E.database(before)), S.schema(c)), send),
    core(c, binding, origin, mode, request, context, before, mode, I.code(request), Con{Q.Started{request, context}, Q.expand_exec(request, context, Execute.generate(steps, Core.start(Source.program(binding, origin), context, I.arguments(request), E.database(before)), S.schema(c)))}),
    trace_result_claims(c, binding, origin, mode, request, context, before, I.code(request), steps, end,
      Core.traverse(steps, Core.start(Source.program(binding, origin), context, I.arguments(request), E.database(before)), S.schema(c)), send, {==}))


law all_cached_core_publications_reopen_the_original_actual_core_and_preparation:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +mode: Bool
  for +request: P.Request
  for +context: D.Context
  for +before: E.Snapshot
  for +execution: Execution.Request
  for +send: V.SendReturn
  All(c, binding, Host.origin(public, I.code(request)), mode, request, context, before, C.events(Execution.run(c, binding, public, mode, request, context, before, execution, send)))
def all_cached_core_publications_reopen_the_original_actual_core_and_preparation(c, binding, public, mode, request, context, before, execution, send):
  match execution:
    case Execution.StartPending{}: Unit{}
    case Execution.StartFailed{identifier, fatal}: failed(c, binding, Host.origin(public, I.code(request)), mode, request, context, before, mode, I.code(request), before, X.Execute{}, identifier, fatal, send)
    case Execution.RunPrefix{steps, end}: executed_prefix_claims(c, binding, public, mode, request, context, before, steps, end, send)


def query_claim(~c: S.Configuration, ~binding: Source.Source, -origin: Source.JudgmentSyntactic, -mode: Bool, -request: P.Request, -context: D.Context, +before: E.Snapshot,
  events: List<&2, O.AuditEvent>, index: Nat, -event: O.AuditEvent, all: All(c, binding, origin, mode, request, context, before, events),
  found: {B.query(O.AuditEvent, events, index) == Some{event} : Maybe<&2, O.AuditEvent>}) -> Claim(c, binding, origin, mode, request, context, before, event):
  match events index all:
    case Nil{} _ _: L.ex_false(Claim(c, binding, origin, mode, request, context, before, event), F.none_negative_some(O.AuditEvent, event, found))
    case Con{head, rest} 0n L.Both{first, later}:
      %F.some_injective(O.AuditEvent, head, event, found) : Claim(c, binding, origin, mode, request, context, before, _)
      first
    case Con{head, rest} 1n+k L.Both{first, later}: query_claim(c, binding, origin, mode, request, context, before, rest, k, event, later, found)


law every_bound_publication_query_has_the_exact_actual_core_origin:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for +origin: Source.JudgmentSyntactic
  for +mode: Bool
  for +request: P.Request
  for +context: D.Context
  for +before: E.Snapshot
  for +execution: Execution.Request
  for +send: V.SendReturn
  for +index: Nat
  for -event: O.AuditEvent
  for found: {B.query(O.AuditEvent, C.events(Execution.run_bound(c, binding, origin, mode, request, context, before, execution, send)), index) == Some{event} : Maybe<&2, O.AuditEvent>}
  Claim(c, binding, origin, mode, request, context, before, event)
def every_bound_publication_query_has_the_exact_actual_core_origin(c, binding, origin, mode, request, context, before, execution, send, index, event, found):
  query_claim(c, binding, origin, mode, request, context, before, C.events(Execution.run_bound(c, binding, origin, mode, request, context, before, execution, send)), index, event,
    all_bound_execution_publications_reopen_the_exact_actual_core_and_preparation(c, binding, origin, mode, request, context, before, execution, send), found)


law every_cached_core_publication_query_has_the_exact_actual_core_origin:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +mode: Bool
  for +request: P.Request
  for +context: D.Context
  for +before: E.Snapshot
  for +execution: Execution.Request
  for +send: V.SendReturn
  for +index: Nat
  for -event: O.AuditEvent
  for found: {B.query(O.AuditEvent, C.events(Execution.run(c, binding, public, mode, request, context, before, execution, send)), index) == Some{event} : Maybe<&2, O.AuditEvent>}
  Claim(c, binding, Host.origin(public, I.code(request)), mode, request, context, before, event)
def every_cached_core_publication_query_has_the_exact_actual_core_origin(c, binding, public, mode, request, context, before, execution, send, index, event, found):
  query_claim(c, binding, Host.origin(public, I.code(request)), mode, request, context, before, C.events(Execution.run(c, binding, public, mode, request, context, before, execution, send)), index, event,
    all_cached_core_publications_reopen_the_original_actual_core_and_preparation(c, binding, public, mode, request, context, before, execution, send), found)


def record(request: P.Request, context: D.Context, finished: Finished) -> History.Record:
  Finished{steps, working, events, proposal, prepared} = finished
  History.Record{request, context, steps, working, events, proposal, prepared}


# A source certificate is the original checked declaration, not a proposition
# about the result of an arbitrary native computation. The Core equations above
# are derived independently from its actual dispatch before this composition.
def certified_origin(~c: S.Configuration, ~binding: Source.Source, +origin: Source.JudgmentSyntactic,
  +request: P.Request, +context: D.Context, +before: E.Snapshot, +finished: Finished,
  certificate: R.Certifies(c, I.code(request), Source.program(binding, origin), context, I.arguments(request)),
  authenticated: {D.authenticate(E.database(before), I.credential(request)) == Some{context} : Maybe<&2, D.Context>},
  real: Real(c, binding, origin, request, context, before, finished)) -> History.Origin(c, E.database(before), record(request, context, finished)):
  match finished real:
    case Finished{steps, working, events, proposal, prepared} L.Both{traced, framed}:
      (Source.program(binding, origin), L.Both{certificate, L.Both{authenticated, L.Both{traced, framed}}})


def checked_origin(~c: S.Configuration, ~binding: Source.Source, +origin: Source.JudgmentSyntactic,
  +request: P.Request, +context: D.Context, +before: E.Snapshot, +finished: Finished,
  checked: Source.JudgmentAccepted(binding, c, request, context, origin),
  authenticated: {D.authenticate(E.database(before), I.credential(request)) == Some{context} : Maybe<&2, D.Context>},
  real: Real(c, binding, origin, request, context, before, finished)) -> History.Origin(c, E.database(before), record(request, context, finished)):
  match checked:
    case L.Both{elaboration, L.Both{derived, L.Both{certificate, L.Both{termination_derived, termination}}}}:
      certified_origin(c, binding, origin, request, context, before, finished, certificate, authenticated, real)


def checked_finish_preserves_prior_state_validity(~c: S.Configuration, ~binding: Source.Source, +origin: Source.JudgmentSyntactic,
  +request: P.Request, +context: D.Context, +before: E.Snapshot, +finished: Finished,
  checked: Source.JudgmentAccepted(binding, c, request, context, origin),
  authenticated: {D.authenticate(E.database(before), I.credential(request)) == Some{context} : Maybe<&2, D.Context>},
  real: Real(c, binding, origin, request, context, before, finished), valid: R.Valid(c, E.database(before))) ->
  R.Valid(c, History.next(E.database(before), record(request, context, finished))):
  History.step_preserves_validity(c, E.database(before), record(request, context, finished), valid, checked_origin(c, binding, origin, request, context, before, finished, checked, authenticated, real))


def next_record(+request: P.Request, +context: D.Context, +before: E.Snapshot, +finished: Finished) ->
  {History.next(E.database(before), record(request, context, finished)) == Publication.published(Core.conclude(prepared(finished), E.database(before))) : D.State}:
  Finished{steps, working, events, proposal, prepared} = finished
  {==}


law an_actual_checked_publication_is_valid_from_the_prior_state_and_original_declaration:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for +origin: Source.JudgmentSyntactic
  for +mode: Bool
  for +request: P.Request
  for +context: D.Context
  for +before: E.Snapshot
  for +actual_mode: Bool
  for +response: S.Response
  for +bytes: List<&2, U32>
  for +actual_before: E.Snapshot
  for +after: E.Snapshot
  for checked: Source.JudgmentAccepted(binding, c, request, context, origin)
  for authenticated: {D.authenticate(E.database(before), I.credential(request)) == Some{context} : Maybe<&2, D.Context>}
  for valid: R.Valid(c, E.database(before))
  for actual: Claim(c, binding, origin, mode, request, context, before, O.Publication{actual_mode, response, bytes, actual_before, after})
  R.Valid(c, E.database(after))
def an_actual_checked_publication_is_valid_from_the_prior_state_and_original_declaration(c, binding, origin, mode, request, context, before, actual_mode, response, bytes, actual_before, after, checked, authenticated, valid, actual):
  match actual:
    case (+finished, L.Both{real, L.Both{same_mode, L.Both{same_before, L.Both{concluded, L.Both{success, exact_pair}}}}}):
      %Equal.trans(D.State, History.next(E.database(before), record(request, context, finished)), Publication.published(Core.conclude(prepared(finished), E.database(before))), E.database(after),
        next_record(request, context, before, finished), Equal.cong(Core.Conclusion, D.State, Publication.published,
          Core.conclude(prepared(finished), E.database(before)), Core.Conclusion{E.database(after), response, bytes}, concluded)) : R.Valid(c, _)
      checked_finish_preserves_prior_state_validity(c, binding, origin, request, context, before, finished, checked, authenticated, real, valid)


law every_queried_checked_bound_publication_preserves_validity_without_a_runtime_result_premise:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for +origin: Source.JudgmentSyntactic
  for +mode: Bool
  for +request: P.Request
  for +context: D.Context
  for +before: E.Snapshot
  for +execution: Execution.Request
  for +send: V.SendReturn
  for +index: Nat
  for +actual_mode: Bool
  for +response: S.Response
  for +bytes: List<&2, U32>
  for +actual_before: E.Snapshot
  for +after: E.Snapshot
  for checked: Source.JudgmentAccepted(binding, c, request, context, origin)
  for authenticated: {D.authenticate(E.database(before), I.credential(request)) == Some{context} : Maybe<&2, D.Context>}
  for valid: R.Valid(c, E.database(before))
  for found: {B.query(O.AuditEvent, C.events(Execution.run_bound(c, binding, origin, mode, request, context, before, execution, send)), index) ==
    Some{O.Publication{actual_mode, response, bytes, actual_before, after}} : Maybe<&2, O.AuditEvent>}
  R.Valid(c, E.database(after))
def every_queried_checked_bound_publication_preserves_validity_without_a_runtime_result_premise(c, binding, origin, mode, request, context, before, execution, send, index, actual_mode, response, bytes, actual_before, after, checked, authenticated, valid, found):
  an_actual_checked_publication_is_valid_from_the_prior_state_and_original_declaration(c, binding, origin, mode, request, context, before, actual_mode, response, bytes, actual_before, after, checked, authenticated, valid,
    every_bound_publication_query_has_the_exact_actual_core_origin(c, binding, origin, mode, request, context, before, execution, send, index,
      O.Publication{actual_mode, response, bytes, actual_before, after}, found))


# Cached reuse supplies this certificate by specializing the ORIGINAL universal
# declaration from current entry provenance. It does not rerun a client checker
# or grant validity of a runtime result. Only prior-state validity is required.
def certified_finish_preserves_prior_state_validity(~c: S.Configuration, ~binding: Source.Source, +origin: Source.JudgmentSyntactic,
  +request: P.Request, +context: D.Context, +before: E.Snapshot, +finished: Finished,
  certificate: R.Certifies(c, I.code(request), Source.program(binding, origin), context, I.arguments(request)),
  authenticated: {D.authenticate(E.database(before), I.credential(request)) == Some{context} : Maybe<&2, D.Context>},
  real: Real(c, binding, origin, request, context, before, finished), valid: R.Valid(c, E.database(before))) ->
  R.Valid(c, History.next(E.database(before), record(request, context, finished))):
  History.step_preserves_validity(c, E.database(before), record(request, context, finished), valid,
    certified_origin(c, binding, origin, request, context, before, finished, certificate, authenticated, real))


def certified_publication_preserves_validity(~c: S.Configuration, ~binding: Source.Source, +origin: Source.JudgmentSyntactic,
  +mode: Bool, +request: P.Request, +context: D.Context, +before: E.Snapshot, +actual_mode: Bool, +response: S.Response, +bytes: List<&2, U32>, +actual_before: E.Snapshot, +after: E.Snapshot,
  certificate: R.Certifies(c, I.code(request), Source.program(binding, origin), context, I.arguments(request)),
  authenticated: {D.authenticate(E.database(before), I.credential(request)) == Some{context} : Maybe<&2, D.Context>}, valid: R.Valid(c, E.database(before)),
  actual: Claim(c, binding, origin, mode, request, context, before, O.Publication{actual_mode, response, bytes, actual_before, after})) -> R.Valid(c, E.database(after)):
  match actual:
    case (+finished, L.Both{real, L.Both{same_mode, L.Both{same_before, L.Both{concluded, L.Both{success, exact_pair}}}}}):
      %Equal.trans(D.State, History.next(E.database(before), record(request, context, finished)), Publication.published(Core.conclude(prepared(finished), E.database(before))), E.database(after),
        next_record(request, context, before, finished), Equal.cong(Core.Conclusion, D.State, Publication.published,
          Core.conclude(prepared(finished), E.database(before)), Core.Conclusion{E.database(after), response, bytes}, concluded)) : R.Valid(c, _)
      certified_finish_preserves_prior_state_validity(c, binding, origin, request, context, before, finished, certificate, authenticated, real, valid)


law every_queried_cached_core_publication_preserves_validity_from_its_original_specialized_certificate:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +mode: Bool
  for +request: P.Request
  for +context: D.Context
  for +before: E.Snapshot
  for +execution: Execution.Request
  for +send: V.SendReturn
  for +index: Nat
  for +actual_mode: Bool
  for +response: S.Response
  for +bytes: List<&2, U32>
  for +actual_before: E.Snapshot
  for +after: E.Snapshot
  for certificate: R.Certifies(c, I.code(request), Source.program(binding, Host.origin(public, I.code(request))), context, I.arguments(request))
  for authenticated: {D.authenticate(E.database(before), I.credential(request)) == Some{context} : Maybe<&2, D.Context>}
  for valid: R.Valid(c, E.database(before))
  for found: {B.query(O.AuditEvent, C.events(Execution.run(c, binding, public, mode, request, context, before, execution, send)), index) ==
    Some{O.Publication{actual_mode, response, bytes, actual_before, after}} : Maybe<&2, O.AuditEvent>}
  R.Valid(c, E.database(after))
def every_queried_cached_core_publication_preserves_validity_from_its_original_specialized_certificate(c, binding, public, mode, request, context, before, execution, send, index, actual_mode, response, bytes, actual_before, after, certificate, authenticated, valid, found):
  certified_publication_preserves_validity(c, binding, Host.origin(public, I.code(request)), mode, request, context, before, actual_mode, response, bytes, actual_before, after, certificate, authenticated, valid,
    every_cached_core_publication_query_has_the_exact_actual_core_origin(c, binding, public, mode, request, context, before, execution, send, index,
      O.Publication{actual_mode, response, bytes, actual_before, after}, found))
