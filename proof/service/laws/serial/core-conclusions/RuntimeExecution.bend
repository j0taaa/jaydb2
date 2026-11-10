# Every actual execution prefix and every end/cleanup return derives Shape.
# A nonfinal traversal is pending; fatal store cleanup has no conclusion;
# nonfatal cleanup may add a SECOND Prepared before its one error conclusion.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../../../src/Core.bend as Core
import ../../../../RoutesService.bend as Route
import ../../../../SourceService.bend as Source
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../model/serial/Common.bend as C
import ../../../model/serial/ExecutionPhases.bend as Exec
import ../../../model/serial/ExecutionFinalWitness.bend as W
import ./Meaning.bend as M
import ./Algebra.bend as A
import ./RuntimeBase.bend as R
import ./RuntimeConclude.bend as Done
import ./Headers.bend as Headers

def prepared_frame_quiet(+mode: Bool, +code: String, prepared: Core.Prepared) ->
  {M.quiet(C.core(mode, code, [Route.frame_prepared(prepared)])) == True{} : Bool}:
  match prepared:
    case Core.Prepared{working, events, response, bytes}: {==}

def cleanup(+mode: Bool, +code: String, +before: E.Snapshot, +prepared: Core.Prepared, cleanup: Route.Cleanup, +send: V.SendReturn) ->
  M.Shape<C.events(Exec.cleanup(mode, code, before, prepared, cleanup, send))>:
  match cleanup:
    case Route.Clears{}: Done.concluded(mode, code, before, Core.conclude(prepared, E.database(before)), send)
    case Route.FatalAfterStore{stage, identifier}: Done.fatal_after_store(mode, code, before, Core.conclude(prepared, E.database(before)), stage, identifier)
    case Route.PendingCleanup{}:
      A.prefix_run(C.core(mode, code, [Route.frame_prepared(prepared)]), C.pending(before), prepared_frame_quiet(mode, code, prepared), R.pending(before))
    case Route.ErrorCleanup{+identifier, +fatal}:
      A.prefix_run(C.core(mode, code, [Route.frame_prepared(prepared)]), C.failed(mode, code, before, X.Prepare{}, identifier, fatal, send),
        prepared_frame_quiet(mode, code, prepared), R.failed(mode, code, before, X.Prepare{}, identifier, fatal, send))

def prepared_result(+mode: Bool, +code: String, +before: E.Snapshot, prepared: Maybe<&2, Core.Prepared>, +cleanup_result: Route.Cleanup, +send: V.SendReturn) ->
  M.Shape<C.events(Exec.prepared_result(mode, code, before, prepared, cleanup_result, send))>:
  match prepared:
    case None{}: R.stopped(before)
    case Some{prepared}: cleanup(mode, code, before, prepared, cleanup_result, send)

def trace_result(~c: S.Configuration, +mode: Bool, +code: String, +before: E.Snapshot, end: Exec.End, trace: S.Trace, +send: V.SendReturn) ->
  M.Shape<C.events(Exec.trace_result(c, mode, code, before, end, trace, send))>:
  match end trace:
    case Exec.PrefixPending{} trace: R.pending(before)
    case Exec.PrefixFailed{identifier, fatal} trace: R.failed(mode, code, before, X.Execute{}, identifier, fatal, send)
    case Exec.FinishPrefix{cleanup} S.Prefix{working, events}: R.pending(before)
    case Exec.FinishPrefix{cleanup} S.Final{working, events, response}:
      prepared_result(mode, code, before, Core.prepare(Core.Stopped{working, events, response}, c), cleanup, send)

def executed_prefix(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +mode: Bool, +request: P.Request, +context: D.Context, +before: E.Snapshot, +steps: Nat, +end: Exec.End, +send: V.SendReturn) ->
  M.Shape<C.events(Exec.executed_prefix(c, binding, public, mode, request, context, before, steps, end, send))>:
  A.prefix_run(W.header(c, binding, public, W.Canonical{I.code(request)}, mode, request, context, E.database(before), steps),
    Exec.trace_result(c, mode, I.code(request), before, end, Core.traverse(steps, Core.start(Source.program(binding, W.origin(public, W.Canonical{I.code(request)})), context, I.arguments(request), E.database(before)), S.schema(c)), send),
    Headers.header(c, binding, public, W.Canonical{I.code(request)}, mode, request, context, E.database(before), steps),
    trace_result(c, mode, I.code(request), before, end, Core.traverse(steps, Core.start(Source.program(binding, W.origin(public, W.Canonical{I.code(request)})), context, I.arguments(request), E.database(before)), S.schema(c)), send))

def run(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +mode: Bool, +request: P.Request, +context: D.Context, +before: E.Snapshot, execution: Exec.Request, +send: V.SendReturn) ->
  M.Shape<C.events(Exec.run(c, binding, public, mode, request, context, before, execution, send))>:
  match execution:
    case Exec.StartPending{}: R.pending(before)
    case Exec.StartFailed{identifier, fatal}: R.failed(mode, I.code(request), before, X.Execute{}, identifier, fatal, send)
    case Exec.RunPrefix{steps, end}: executed_prefix(c, binding, public, mode, request, context, before, steps, end, send)

def executed_bound_prefix(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +origin: Source.JudgmentSyntactic, +mode: Bool, +request: P.Request, +context: D.Context, +before: E.Snapshot, +steps: Nat, +end: Exec.End, +send: V.SendReturn) ->
  M.Shape<C.events(Exec.executed_bound_prefix(c, binding, origin, mode, request, context, before, steps, end, send))>:
  A.prefix_run(W.header(c, binding, public, W.Bound{origin}, mode, request, context, E.database(before), steps),
    Exec.trace_result(c, mode, I.code(request), before, end, Core.traverse(steps, Core.start(Source.program(binding, origin), context, I.arguments(request), E.database(before)), S.schema(c)), send),
    Headers.header(c, binding, public, W.Bound{origin}, mode, request, context, E.database(before), steps),
    trace_result(c, mode, I.code(request), before, end, Core.traverse(steps, Core.start(Source.program(binding, origin), context, I.arguments(request), E.database(before)), S.schema(c)), send))

def run_bound(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +origin: Source.JudgmentSyntactic, +mode: Bool, +request: P.Request, +context: D.Context, +before: E.Snapshot, execution: Exec.Request, +send: V.SendReturn) ->
  M.Shape<C.events(Exec.run_bound(c, binding, origin, mode, request, context, before, execution, send))>:
  match execution:
    case Exec.StartPending{}: R.pending(before)
    case Exec.StartFailed{identifier, fatal}: R.failed(mode, I.code(request), before, X.Execute{}, identifier, fatal, send)
    case Exec.RunPrefix{steps, end}: executed_bound_prefix(c, binding, public, origin, mode, request, context, before, steps, end, send)
