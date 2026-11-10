# Actual pure execution prefixes and actual preparation/conclusion functions.
# steps is a mathematical prefix witness, not a runtime quota. No completed
# trace, arbitrary Prepared value or final-state validity is an input field.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Interface.bend as I
import ../../../../contract/Protocol.bend as P
import ../../../../contract/Resources.bend as X
import ../../../../contract/Semantics.bend as S
import ../../../../src/Core.bend as Core
import ../../../ExecutionService.bend as Execution
import ../../../HostTransitions.bend as Host
import ../../../ProtocolService.bend as Q
import ../../../RoutesService.bend as Route
import ../../../SourceService.bend as Source
import ../../specification/ServiceLaws.bend as E
import ../../phases/PreparePhases.bend as V
import ../EventObserver.bend as O
import ./Common.bend as C

type End is Data:
  FinishPrefix{cleanup: Route.Cleanup}
  PrefixPending{}
  PrefixFailed{identifier: String, fatal: Bool}

type Request is Data:
  StartPending{}
  StartFailed{identifier: String, fatal: Bool}
  RunPrefix{steps: Nat, end: End}

def published_status(success: Bool, +before: E.Snapshot, state: D.State, bytes: List<&2, U32>) -> E.Snapshot:
  match success:
    case False{}: before
    case True{}: E.Snapshot{E.instance(before), state, bytes, E.registry(before)}

def published(+before: E.Snapshot, conclusion: Core.Conclusion) -> E.Snapshot:
  Core.Conclusion{state, S.Response{status, value}, bytes} = conclusion
  published_status(S.is_success(status), before, state, bytes)

def publication(mode: Bool, +before: E.Snapshot, +after: E.Snapshot, response: S.Response, bytes: List<&2, U32>) -> List<&2, O.AuditEvent>:
  match response:
    case S.Response{S.Success{}, value}: [O.Publication{mode, S.Response{S.Success{}, value}, bytes, before, after}]
    case _: Nil{}

def concluded(+mode: Bool, +code: String, +before: E.Snapshot, +conclusion: Core.Conclusion, send: V.SendReturn) -> C.CallRun:
  match conclusion:
    case Core.Conclusion{state, +response, +bytes}:
      +after = published(before, Core.Conclusion{state, response, bytes})
      C.prefix(C.append([O.Core{mode, code, Q.Prepared{response, bytes}}],
        C.append(publication(mode, before, after, response, bytes), [O.Core{mode, code, Q.Completed{response, E.database(after), False{}}}])),
        C.delivery(mode, code, after, E.Transaction{response}, bytes, False{}, send))

def fatal_after_store(+mode: Bool, +code: String, +before: E.Snapshot, +conclusion: Core.Conclusion, stage: X.Stage, identifier: String) -> C.CallRun:
  match conclusion:
    case Core.Conclusion{state, +response, +bytes}:
      +after = published(before, Core.Conclusion{state, response, bytes})
      C.CallRun{C.append([O.Core{mode, code, Q.Prepared{response, bytes}}],
        C.append(publication(mode, before, after, response, bytes), C.core(mode, code, [Q.Failed{stage, identifier, True{}}, Q.Closed{}]))),
        after, None{}, False{}, True{}}

def cleanup(+mode: Bool, +code: String, +before: E.Snapshot, +prepared: Core.Prepared, cleanup: Route.Cleanup, send: V.SendReturn) -> C.CallRun:
  match cleanup:
    case Route.Clears{}: concluded(mode, code, before, Core.conclude(prepared, E.database(before)), send)
    case Route.FatalAfterStore{stage, identifier}: fatal_after_store(mode, code, before, Core.conclude(prepared, E.database(before)), stage, identifier)
    case Route.PendingCleanup{}:
      C.prefix(C.core(mode, code, [Route.frame_prepared(prepared)]), C.pending(before))
    case Route.ErrorCleanup{identifier, fatal}:
      C.prefix(C.core(mode, code, [Route.frame_prepared(prepared)]), C.failed(mode, code, before, X.Prepare{}, identifier, fatal, send))

def prepared_result(mode: Bool, code: String, before: E.Snapshot, prepared: Maybe<&2, Core.Prepared>, cleanup_result: Route.Cleanup, send: V.SendReturn) -> C.CallRun:
  match prepared:
    case None{}: C.stopped(before)
    case Some{prepared}: cleanup(mode, code, before, prepared, cleanup_result, send)

def trace_result(~c: S.Configuration, mode: Bool, code: String, +before: E.Snapshot,
  end: End, trace: S.Trace, send: V.SendReturn) -> C.CallRun:
  match end:
    case PrefixPending{}: C.pending(before)
    case PrefixFailed{identifier, fatal}: C.failed(mode, code, before, X.Execute{}, identifier, fatal, send)
    case FinishPrefix{cleanup}:
      match trace:
        case S.Prefix{working, events}: C.pending(before)
        case S.Final{working, events, response}:
          prepared_result(mode, code, before, Core.prepare(Core.Stopped{working, events, response}, c), cleanup, send)

def executed_prefix(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +mode: Bool, +request: P.Request, +context: D.Context, +before: E.Snapshot,
  +steps: Nat, end: End, send: V.SendReturn) -> C.CallRun:
  C.prefix(C.core(mode, I.code(request), Con{Q.Started{request, context},
      Q.expand_exec(request, context,
        Execution.generate(steps, Core.start(Source.program(binding, Host.origin(public, I.code(request))), context, I.arguments(request), E.database(before)), S.schema(c)))}),
    trace_result(c, mode, I.code(request), before, end,
      Core.traverse(steps, Core.start(Source.program(binding, Host.origin(public, I.code(request))), context, I.arguments(request), E.database(before)), S.schema(c)), send))

def run(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +mode: Bool, +request: P.Request, context: D.Context, before: E.Snapshot,
  execution: Request, send: V.SendReturn) -> C.CallRun:
  match execution:
    case StartPending{}: C.pending(before)
    case StartFailed{identifier, fatal}: C.failed(mode, I.code(request), before, X.Execute{}, identifier, fatal, send)
    case RunPrefix{steps, end}: executed_prefix(c, binding, public, mode, request, context, before, steps, end, send)

# Ordinary execution uses the exact per-call generated source. The syntax
# origin is DATA, so both evaluators reopen the original closed program through
# Source.program rather than copying a live affine Program value.
def executed_bound_prefix(~c: S.Configuration, ~binding: Source.Source,
  +origin: Source.JudgmentSyntactic, +mode: Bool, +request: P.Request,
  +context: D.Context, +before: E.Snapshot, +steps: Nat, end: End, send: V.SendReturn) -> C.CallRun:
  C.prefix(C.bound_core(mode, origin, Con{Q.Started{request, context},
      Q.expand_exec(request, context,
        Execution.generate(steps, Core.start(Source.program(binding, origin), context, I.arguments(request), E.database(before)), S.schema(c)))}),
    trace_result(c, mode, I.code(request), before, end,
      Core.traverse(steps, Core.start(Source.program(binding, origin), context, I.arguments(request), E.database(before)), S.schema(c)), send))

def run_bound(~c: S.Configuration, ~binding: Source.Source,
  origin: Source.JudgmentSyntactic, +mode: Bool, +request: P.Request,
  context: D.Context, before: E.Snapshot, execution: Request, send: V.SendReturn) -> C.CallRun:
  match execution:
    case StartPending{}: C.pending(before)
    case StartFailed{identifier, fatal}: C.failed(mode, I.code(request), before, X.Execute{}, identifier, fatal, send)
    case RunPrefix{steps, end}: executed_bound_prefix(c, binding, origin, mode, request, context, before, steps, end, send)


law a_non_successful_conclusion_keeps_the_complete_published_pair_and_registry:
  for -before: E.Snapshot
  for -state: D.State
  for -value: D.Value
  for -bytes: List<&2, U32>
  {published(before, Core.Conclusion{state, S.Response{S.Refusal{}, value}, bytes}) == before : E.Snapshot}
def a_non_successful_conclusion_keeps_the_complete_published_pair_and_registry(before, state, value, bytes):
  {==}
