# Actual ordinary/cached execution has only the runtime syntax constructors.
# Publications and every failure/cleanup/delivery return remain present.
import Base
import ../../../../contract/Logic.bend as L
import ../../../../contract/Data.bend as D
import ../../../../contract/Interface.bend as I
import ../../../../contract/Protocol.bend as P
import ../../../../contract/Resources.bend as X
import ../../../../contract/Semantics.bend as S
import ../../../../src/Core.bend as Core
import ../../../ExecutionService.bend as Execute
import ../../../HostTransitions.bend as Host
import ../../../ProtocolService.bend as Q
import ../../../RoutesService.bend as Route
import ../../../SourceService.bend as Source
import ../../specification/ServiceLaws.bend as E
import ../../phases/PreparePhases.bend as V
import ../../model/EventObserver.bend as O
import ../../model/serial/Common.bend as C
import ../../model/serial/ExecutionPhases.bend as Execution
import ./RuntimeSourceBase.bend as N


def publication(+mode: Bool, +before: E.Snapshot, +after: E.Snapshot, response: S.Response, +bytes: List<&2, U32>) ->
  N.All(Execution.publication(mode, before, after, response, bytes)):
  match response:
    case S.Response{S.Success{}, value}: L.Both{Unit{}, Unit{}}
    case S.Response{S.Input{}, value}: Unit{}
    case S.Response{S.Authentication{}, value}: Unit{}
    case S.Response{S.Certificate{}, value}: Unit{}
    case S.Response{S.DataError{}, value}: Unit{}
    case S.Response{S.Limit{}, value}: Unit{}
    case S.Response{S.Failure{}, value}: Unit{}
    case S.Response{S.Refusal{}, value}: Unit{}


def concluded(+mode: Bool, +code: String, +before: E.Snapshot, conclusion: Core.Conclusion, +send: V.SendReturn) ->
  N.Call(Execution.concluded(mode, code, before, conclusion, send)):
  match conclusion:
    case Core.Conclusion{+state, +response, +bytes}:
      +after = Execution.published(before, Core.Conclusion{state, response, bytes})
      N.prefixed(C.append([O.Core{mode, code, Q.Prepared{response, bytes}}],
          C.append(Execution.publication(mode, before, after, response, bytes), [O.Core{mode, code, Q.Completed{response, E.database(after), False{}}}])),
        C.delivery(mode, code, after, E.Transaction{response}, bytes, False{}, send),
        N.appended([O.Core{mode, code, Q.Prepared{response, bytes}}],
          C.append(Execution.publication(mode, before, after, response, bytes), [O.Core{mode, code, Q.Completed{response, E.database(after), False{}}}]),
          L.Both{Unit{}, Unit{}}, N.appended(Execution.publication(mode, before, after, response, bytes), [O.Core{mode, code, Q.Completed{response, E.database(after), False{}}}],
            publication(mode, before, after, response, bytes), L.Both{Unit{}, Unit{}})),
        N.delivery(mode, code, after, E.Transaction{response}, bytes, False{}, send))


def fatal_after_store(+mode: Bool, +code: String, +before: E.Snapshot, conclusion: Core.Conclusion, +stage: X.Stage, +identifier: String) ->
  N.Call(Execution.fatal_after_store(mode, code, before, conclusion, stage, identifier)):
  match conclusion:
    case Core.Conclusion{+state, +response, +bytes}:
      +after = Execution.published(before, Core.Conclusion{state, response, bytes})
      N.appended([O.Core{mode, code, Q.Prepared{response, bytes}}],
        C.append(Execution.publication(mode, before, after, response, bytes), C.core(mode, code, [Q.Failed{stage, identifier, True{}}, Q.Closed{}])),
        L.Both{Unit{}, Unit{}}, N.appended(Execution.publication(mode, before, after, response, bytes), C.core(mode, code, [Q.Failed{stage, identifier, True{}}, Q.Closed{}]),
          publication(mode, before, after, response, bytes), N.core(mode, code, [Q.Failed{stage, identifier, True{}}, Q.Closed{}])))


def cleanup(+mode: Bool, +code: String, +before: E.Snapshot, +prepared: Core.Prepared, cleanup: Route.Cleanup, +send: V.SendReturn) ->
  N.Call(Execution.cleanup(mode, code, before, prepared, cleanup, send)):
  match cleanup:
    case Route.Clears{}: concluded(mode, code, before, Core.conclude(prepared, E.database(before)), send)
    case Route.FatalAfterStore{stage, identifier}: fatal_after_store(mode, code, before, Core.conclude(prepared, E.database(before)), stage, identifier)
    case Route.PendingCleanup{}:
      N.prefixed(C.core(mode, code, [Route.frame_prepared(prepared)]), C.pending(before), N.core(mode, code, [Route.frame_prepared(prepared)]), Unit{})
    case Route.ErrorCleanup{+identifier, +fatal}:
      N.prefixed(C.core(mode, code, [Route.frame_prepared(prepared)]), C.failed(mode, code, before, X.Prepare{}, identifier, fatal, send),
        N.core(mode, code, [Route.frame_prepared(prepared)]), N.failed(mode, code, before, X.Prepare{}, identifier, fatal, send))


def prepared_result(+mode: Bool, +code: String, +before: E.Snapshot, prepared: Maybe<&2, Core.Prepared>, +clean: Route.Cleanup, +send: V.SendReturn) ->
  N.Call(Execution.prepared_result(mode, code, before, prepared, clean, send)):
  match prepared:
    case None{}: Unit{}
    case Some{prepared}: cleanup(mode, code, before, prepared, clean, send)


def trace_result(~c: S.Configuration, +mode: Bool, +code: String, +before: E.Snapshot,
  end: Execution.End, trace: S.Trace, +send: V.SendReturn) -> N.Call(Execution.trace_result(c, mode, code, before, end, trace, send)):
  match end:
    case Execution.PrefixPending{}: Unit{}
    case Execution.PrefixFailed{identifier, fatal}: N.failed(mode, code, before, X.Execute{}, identifier, fatal, send)
    case Execution.FinishPrefix{clean}:
      match trace:
        case S.Prefix{working, events}: Unit{}
        case S.Final{working, events, response}: prepared_result(mode, code, before, Core.prepare(Core.Stopped{working, events, response}, c), clean, send)


def executed_prefix(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +mode: Bool, +request: P.Request, +context: D.Context, +before: E.Snapshot, +steps: Nat, +end: Execution.End, +send: V.SendReturn) ->
  N.Call(Execution.executed_prefix(c, binding, public, mode, request, context, before, steps, end, send)):
  N.prefixed(C.core(mode, I.code(request), Con{Q.Started{request, context}, Q.expand_exec(request, context,
      Execute.generate(steps, Core.start(Source.program(binding, Host.origin(public, I.code(request))), context, I.arguments(request), E.database(before)), S.schema(c)))}),
    Execution.trace_result(c, mode, I.code(request), before, end,
      Core.traverse(steps, Core.start(Source.program(binding, Host.origin(public, I.code(request))), context, I.arguments(request), E.database(before)), S.schema(c)), send),
    N.core(mode, I.code(request), Con{Q.Started{request, context}, Q.expand_exec(request, context,
      Execute.generate(steps, Core.start(Source.program(binding, Host.origin(public, I.code(request))), context, I.arguments(request), E.database(before)), S.schema(c)))}),
    trace_result(c, mode, I.code(request), before, end,
      Core.traverse(steps, Core.start(Source.program(binding, Host.origin(public, I.code(request))), context, I.arguments(request), E.database(before)), S.schema(c)), send))


def run(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +mode: Bool, +request: P.Request, +context: D.Context, +before: E.Snapshot, execution: Execution.Request, +send: V.SendReturn) ->
  N.Call(Execution.run(c, binding, public, mode, request, context, before, execution, send)):
  match execution:
    case Execution.StartPending{}: Unit{}
    case Execution.StartFailed{identifier, fatal}: N.failed(mode, I.code(request), before, X.Execute{}, identifier, fatal, send)
    case Execution.RunPrefix{steps, end}: executed_prefix(c, binding, public, mode, request, context, before, steps, end, send)


def executed_bound_prefix(~c: S.Configuration, ~binding: Source.Source,
  +origin: Source.JudgmentSyntactic, +mode: Bool, +request: P.Request, +context: D.Context, +before: E.Snapshot,
  +steps: Nat, +end: Execution.End, +send: V.SendReturn) ->
  N.Call(Execution.executed_bound_prefix(c, binding, origin, mode, request, context, before, steps, end, send)):
  N.prefixed(C.bound_core(mode, origin, Con{Q.Started{request, context}, Q.expand_exec(request, context,
      Execute.generate(steps, Core.start(Source.program(binding, origin), context, I.arguments(request), E.database(before)), S.schema(c)))}),
    Execution.trace_result(c, mode, I.code(request), before, end,
      Core.traverse(steps, Core.start(Source.program(binding, origin), context, I.arguments(request), E.database(before)), S.schema(c)), send),
    N.bound_core(mode, origin, Con{Q.Started{request, context}, Q.expand_exec(request, context,
      Execute.generate(steps, Core.start(Source.program(binding, origin), context, I.arguments(request), E.database(before)), S.schema(c)))}),
    trace_result(c, mode, I.code(request), before, end,
      Core.traverse(steps, Core.start(Source.program(binding, origin), context, I.arguments(request), E.database(before)), S.schema(c)), send))


def run_bound(~c: S.Configuration, ~binding: Source.Source, +origin: Source.JudgmentSyntactic,
  +mode: Bool, +request: P.Request, +context: D.Context, +before: E.Snapshot, execution: Execution.Request, +send: V.SendReturn) ->
  N.Call(Execution.run_bound(c, binding, origin, mode, request, context, before, execution, send)):
  match execution:
    case Execution.StartPending{}: Unit{}
    case Execution.StartFailed{identifier, fatal}: N.failed(mode, I.code(request), before, X.Execute{}, identifier, fatal, send)
    case Execution.RunPrefix{steps, end}: executed_bound_prefix(c, binding, origin, mode, request, context, before, steps, end, send)
