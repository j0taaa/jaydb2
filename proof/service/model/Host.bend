# Operational CALL transition model, not the native observer interpretation.
# Every state change below calls the project's actual pure function. Cached
# calls obtain certificates from original preparation provenance in the current
# registry; they are not given a fresh per-execution certificate.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Interface.bend as I
import ../../../contract/Logic.bend as L
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/PreparedRegistry.bend as G
import ../../../contract/Protocol.bend as P
import ../../../contract/Requirements.bend as R
import ../../../contract/Resources.bend as X
import ../../../contract/Semantics.bend as S
import ../../../contract/ReadOnlyContract.bend as RO
import ../../../src/Core.bend as N
import ../../Foundations.bend as F
import ../../HistoryService.bend as Database
import ../../Publication.bend as Publication
import ../../ProtocolService.bend as Q
import ../../SourceService.bend as Source

type Published is Data:
  Published{database: D.State, response: List<&2, U32>, entries: List<&2, G.Entry>}

def database(s: Published) -> D.State:
  Published{d, r, es} = s
  d

def response(s: Published) -> List<&2, U32>:
  Published{d, r, es} = s
  r

def entries(s: Published) -> List<&2, G.Entry>:
  Published{d, r, es} = s
  es

type Execution is Data:
  Execution{context: D.Context, steps: Nat, working: D.State,
    events: List<&2, S.OperationEvent>, proposal: S.Response, prepared: N.Prepared}

def execution_context(execution: Execution) -> D.Context:
  match execution:
    case Execution{context, steps, working, events, proposal, prepared}: context

def execution_prepared(execution: Execution) -> N.Prepared:
  Execution{context, n, w, ts, prop, prepared} = execution
  prepared

type Command is Data:
  Ordinary{request: P.Request, execution: Execution}
  Prepare{raw: P.Request, context: D.Context, read_only: Bool, handle: String, seal: String}
  Execute{raw: P.Request, entry: G.Entry, execution: Execution}
  Invalidate{raw: P.Request, context: D.Context, cleanup_failed: Bool}
  Unchanged{}

type Invocation is Data:
  Invocation{world: Nat, selected: D.State, input: X.Reception, command: Command}

# Denotation of a closed Client.program under the fixed public modules. This
# data does not assert that parsing/checking/compilation succeeded.
def origin(modules: List<&2, Source.FileSource>, code: String) -> Source.JudgmentSyntactic:
  Source.JudgmentSyntactic{Con{Source.FileSource{"Client.bend", code}, modules},
    "Client.bend", "Client:program"}

def operation(read_only: Bool) -> W.Operation:
  match read_only:
    case False{}: W.Prepare{}
    case True{}: W.PrepareRead{}

def candidate(instance: String, call: Invocation) -> Maybe<&2, G.Entry>:
  match call:
    case Invocation{world, selected, input, Prepare{+raw, context, read_only, handle, seal}}:
      Some{G.Entry{instance, handle, I.code(raw), I.proof(raw), read_only, seal}}
    case _: None{}

def ReadChecked(~source: Source.Source, ~c: S.Configuration, -raw: P.Request,
  -program: S.Program, read_only: Bool) -> Type:
  match read_only:
    case False{}: Unit
    case True{}: L.E<I.Derives(Source.environment(source), c, I.proof(raw), RO.Program(program)), RO.Program(program)>

# Exact accepted ORIGINAL declarations are the checker primitive. This is not
# a validity judgment on a runtime state, entry or published result.
def PreparationChecked(~source: Source.Source, ~c: S.Configuration,
  ~modules: List<&2, Source.FileSource>, -raw: P.Request, read_only: Bool) -> Type:
  L.E<I.Bound(Source.environment(source), c, I.code(raw), Source.program(source, origin(modules, I.code(raw)))),
    L.E<I.Derives(Source.environment(source), c, I.proof(raw),
      H.Universal(c, I.code(raw), Source.program(source, origin(modules, I.code(raw))))),
      L.E<H.Universal(c, I.code(raw), Source.program(source, origin(modules, I.code(raw)))),
        ReadChecked(source, c, raw, Source.program(source, origin(modules, I.code(raw))), read_only)>>>

def Checked(~source: Source.Source, ~c: S.Configuration,
  ~modules: List<&2, Source.FileSource>, call: Invocation) -> Type:
  match call:
    case Invocation{world, selected, input, Ordinary{request, execution}}:
      Source.JudgmentAccepted(source, c, request, execution_context(execution), origin(modules, I.code(request)))
    case Invocation{world, selected, input, Prepare{+raw, context, read_only, handle, seal}}:
      PreparationChecked(source, c, modules, raw, read_only)
    case _: Unit

def CoreReal(~source: Source.Source, ~c: S.Configuration,
  ~modules: List<&2, Source.FileSource>, -selected: D.State,
  -request: P.Request, execution: Execution) -> Type:
  match execution:
    case Execution{context, n, w, ts, prop, prepared}:
      L.E<{N.traverse(n, N.start(Source.program(source, origin(modules, I.code(request))),
        context, I.arguments(request), selected), S.schema(c)) == S.Final{w, ts, prop} : S.Trace},
        {N.prepare(N.Stopped{w, ts, prop}, c) == Some{prepared} : Maybe<&2, N.Prepared>}>

def Executed(~source: Source.Source, ~c: S.Configuration,
  ~modules: List<&2, Source.FileSource>, call: Invocation) -> Type:
  match call:
    case Invocation{world, selected, input, Ordinary{request, execution}}:
      CoreReal(source, c, modules, selected, request, execution)
    case Invocation{world, selected, input, Execute{raw, entry, execution}}:
      CoreReal(source, c, modules, selected, H.resolved(raw, entry), execution)
    case _: Unit

# A CLOSED book reopens original declarations/equations. It must correspond to
# the exact source/primitive results of those invocations. No observer, history
# equality, final-state invariant or arbitrary target eliminator is a field.
type InputBook is Type:
  InputBook{calls: Nat -> Invocation}

def call(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  book: InputBook, index: Nat) -> Invocation:
  InputBook{calls} = book
  calls(index)

def Checks(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: InputBook) -> Type:
  @index: Nat -> Checked(binding, c, public, call(c, binding, public, book, index))

def Executions(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: InputBook) -> Type:
  @index: Nat -> Executed(binding, c, public, call(c, binding, public, book, index))

def record(request: P.Request, execution: Execution) -> Database.Record:
  Execution{context, n, w, ts, prop, prepared} = execution
  Database.Record{request, context, n, w, ts, prop, prepared}

def transaction_status(success: Bool, state: D.State, bytes: List<&2, U32>, previous: List<&2, U32>, es: List<&2, G.Entry>) -> Published:
  match success:
    case True{}: Published{state, bytes, es}
    case False{}: Published{state, previous, es}

def transaction(result: N.Conclusion, previous: List<&2, U32>, es: List<&2, G.Entry>) -> Published:
  match result:
    case N.Conclusion{state, S.Response{status, value}, bytes}:
      transaction_status(S.is_success(status), state, bytes, previous, es)

def control(result: H.ControlResult, previous: List<&2, U32>) -> Published:
  H.ControlResult{state, es, outcome} = result
  Published{state, previous, es}

def next(~c: S.Configuration, +instance: String, before: Published, call: Invocation) -> Published:
  Published{state, previous, es} = before
  match call:
    case Invocation{world, selected, input, Ordinary{request, execution}}:
      transaction(N.conclude(execution_prepared(execution), state), previous, es)
    case Invocation{world, selected, input, Execute{raw, entry, execution}}:
      transaction(N.conclude(execution_prepared(execution), state), previous, es)
    case Invocation{world, selected, input, Prepare{+raw, context, read_only, handle, seal}}:
      control(H.register(c, state, instance,
        G.Entry{instance, handle, I.code(raw), I.proof(raw), read_only, seal}, es), previous)
    case Invocation{world, selected, input, Invalidate{raw, context, failed}}:
      control(H.cleanup_invalidation(failed, H.invalidate(c, state, instance, I.code(raw), es)), previous)
    case Invocation{world, selected, input, Unchanged{}}: Published{state, previous, es}

# This is recoverable DATA provenance. The logical declaration is reopened at
# its original index only after lookup, rather than copied as a captured proof.
def EntryOrigin(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: InputBook, -entry: G.Entry) -> Type:
  &index: Nat -> {candidate(G.instance(entry), call(c, binding, public, book, index)) == Some{entry} : Maybe<&2, G.Entry>}

def EntryProperty(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: InputBook) -> G.Entry -> Type:
  entry => EntryOrigin(c, binding, public, book, entry)

def Valid(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: InputBook, +instance: String, state: Published) -> Type:
  Published{database, response, es} = state
  L.E<R.Valid(c, database), G.AllEntries(EntryProperty(c, binding, public, book), es)>

def StepCommand(~c: S.Configuration, +instance: String, +before: Published,
  +world: Nat, +input: X.Reception, command: Command) -> Type:
  match command:
    case Ordinary{+request, +execution}:
      L.E<W.Received(c, input, W.Ordinary{request}),
        {D.authenticate(database(before), I.credential(request)) == Some{execution_context(execution)} : Maybe<&2, D.Context>}>
    case Prepare{+raw, context, read_only, handle, seal}:
      L.E<W.Received(c, input, W.Extension{operation(read_only), raw}),
        {D.authenticate(database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>}>
    case Execute{+raw, +entry, +execution}:
      L.E<W.Received(c, input, W.Extension{W.Execute{}, raw}),
        L.E<{D.authenticate(database(before), I.credential(raw)) == Some{execution_context(execution)} : Maybe<&2, D.Context>},
          L.E<H.HandleFields(raw, entry), {G.lookup(instance, I.code(raw), entries(before)) == Some{entry} : Maybe<&2, G.Entry>}>>>
    case Invalidate{+raw, context, failed}:
      L.E<W.Received(c, input, W.Extension{W.Invalidate{}, raw}),
        L.E<{D.authenticate(database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>}, {I.proof(raw) == "" : String}>>
    case Unchanged{}: Unit

def Step(~c: S.Configuration, +instance: String, +before: Published, invocation: Invocation) -> Type:
  match invocation:
    case Invocation{world, selected, input, command}:
      L.E<{selected == database(before) : D.State}, StepCommand(c, instance, before, world, input, command)>

def registry_cons_copy(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: InputBook, +instance: String,
  -entry: G.Entry, -rest: List<&2, G.Entry>, +index: Nat,
  exact: L.E<{candidate(G.instance(entry), call(c, binding, public, book, index)) == Some{entry} : Maybe<&2, G.Entry>},
    {candidate(G.instance(entry), call(c, binding, public, book, index)) == Some{entry} : Maybe<&2, G.Entry>}>,
  later: L.E<G.AllEntries(EntryProperty(c, binding, public, book), rest), G.AllEntries(EntryProperty(c, binding, public, book), rest)>) ->
  L.E<G.AllEntries(EntryProperty(c, binding, public, book), Con{entry, rest}), G.AllEntries(EntryProperty(c, binding, public, book), Con{entry, rest})>:
  match exact later:
    case L.Both{left, right} L.Both{first, second}:
      L.Both{L.Both{(index, left), first}, L.Both{(index, right), second}}

def registry_copy(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: InputBook, +instance: String,
  es: List<&2, G.Entry>, origins: G.AllEntries(EntryProperty(c, binding, public, book), es)) ->
  L.E<G.AllEntries(EntryProperty(c, binding, public, book), es), G.AllEntries(EntryProperty(c, binding, public, book), es)>:
  match es origins:
    case Nil{} _: L.Both{Unit{}, Unit{}}
    case Con{+entry, +rest} L.Both{(index, exact), later}:
      registry_cons_copy(c, binding, public, book, instance, entry, rest, index,
        Q.equality_reopenable(Maybe<&2, G.Entry>, candidate(G.instance(entry), call(c, binding, public, book, index)), Some{entry}, exact),
        registry_copy(c, binding, public, book, instance, rest, later))

def preparation_certificate(~source: Source.Source, ~c: S.Configuration,
  ~mods: List<&2, Source.FileSource>, +instance: String, +raw: P.Request,
  read_only: Bool, +handle: String, +seal: String,
  checked: PreparationChecked(source, c, mods, raw, read_only)) ->
  H.ModeCertificateValid(Source.environment(source), c,
    G.Entry{instance, handle, I.code(raw), I.proof(raw), read_only, seal},
    Source.program(source, origin(mods, I.code(raw)))):
  match read_only checked:
    case False{} L.Both{bound, L.Both{derived, L.Both{universal, read}}}:
      L.Both{bound, L.Both{derived, universal}}
    case True{} L.Both{bound, L.Both{derived, L.Both{universal, read}}}:
      L.Both{L.Both{bound, L.Both{derived, universal}}, read}

def absent_candidate_certificate(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: InputBook, +entry: G.Entry,
  exact: {None{} == Some{entry} : Maybe<&2, G.Entry>}) ->
  H.ModeCertificateValid(Source.environment(binding), c, entry,
    Source.program(binding, origin(public, G.code(entry)))):
  L.ex_false(H.ModeCertificateValid(Source.environment(binding), c, entry,
    Source.program(binding, origin(public, G.code(entry)))), F.none_negative_some(G.Entry, entry, exact))

def certificate_from_candidate(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: InputBook, +instance: String,
  invocation: Invocation, +entry: G.Entry,
  checked: Checked(binding, c, public, invocation),
  exact: {candidate(instance, invocation) == Some{entry} : Maybe<&2, G.Entry>}) ->
  H.ModeCertificateValid(Source.environment(binding), c, entry,
    Source.program(binding, origin(public, G.code(entry)))):
  match invocation:
    case Invocation{world, selected, input, Prepare{+raw, context, +read_only, +handle, +seal}}:
      %F.some_injective(G.Entry,
        G.Entry{instance, handle, I.code(raw), I.proof(raw), read_only, seal}, entry, exact) :
        H.ModeCertificateValid(Source.environment(binding), c, _,
          Source.program(binding, origin(public, G.code(_))))
      preparation_certificate(binding, c, public, instance, raw, read_only, handle, seal, checked)
    case Invocation{world, selected, input, Ordinary{request, execution}}: absent_candidate_certificate(c, binding, public, book, entry, exact)
    case Invocation{world, selected, input, Execute{raw, stored, execution}}: absent_candidate_certificate(c, binding, public, book, entry, exact)
    case Invocation{world, selected, input, Invalidate{raw, context, failed}}: absent_candidate_certificate(c, binding, public, book, entry, exact)
    case Invocation{world, selected, input, Unchanged{}}: absent_candidate_certificate(c, binding, public, book, entry, exact)

law current_origin_reopens_original_universal_certificate:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~book: InputBook
  for checks: Checks(c, binding, public, book)
  for +instance: String
  for +entry: G.Entry
  for provenance: EntryOrigin(c, binding, public, book, entry)
  H.ModeCertificateValid(Source.environment(binding), c, entry,
    Source.program(binding, origin(public, G.code(entry))))
def current_origin_reopens_original_universal_certificate(c, binding, public, book, checks, instance, entry, provenance):
  match provenance:
    case (+index, exact): certificate_from_candidate(c, binding, public, book, G.instance(entry), call(c, binding, public, book, index), entry, checks(index), exact)

def universal_from_mode(~a: I.Environment, ~c: S.Configuration, +entry: G.Entry, -program: S.Program,
  certificate: H.ModeCertificateValid(a, c, entry, program)) -> H.Universal(c, G.code(entry), program):
  match entry:
    case G.Entry{i, h, code, proof, False{}, seal}:
      match certificate:
        case L.Both{bound, L.Both{derived, universal}}: universal
    case G.Entry{i, h, code, proof, True{}, seal}:
      match certificate:
        case L.Both{L.Both{bound, L.Both{derived, universal}}, read}: universal

def core_origin(~source: Source.Source, ~c: S.Configuration,
  ~mods: List<&2, Source.FileSource>, -state: D.State, +request: P.Request, execution: Execution,
  certificate: R.Certifies(c, I.code(request), Source.program(source, origin(mods, I.code(request))),
    execution_context(execution), I.arguments(request)),
  authenticated: {D.authenticate(state, I.credential(request)) == Some{execution_context(execution)} : Maybe<&2, D.Context>},
  real: CoreReal(source, c, mods, state, request, execution)) -> Database.Origin(c, state, record(request, execution)):
  match execution real:
    case Execution{context, n, w, ts, prop, prepared} L.Both{obtained, framed}:
      (Source.program(source, origin(mods, I.code(request))), L.Both{certificate, L.Both{authenticated, L.Both{obtained, framed}}})

def transaction_status_valid(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: InputBook, +instance: String,
  success: Bool, -state: D.State, -bytes: List<&2, U32>, -previous: List<&2, U32>, -es: List<&2, G.Entry>,
  valid: R.Valid(c, state), origins: G.AllEntries(EntryProperty(c, binding, public, book), es)) ->
  Valid(c, binding, public, book, instance, transaction_status(success, state, bytes, previous, es)):
  match success:
    case False{}: L.Both{valid, origins}
    case True{}: L.Both{valid, origins}

def transaction_valid(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: InputBook, +instance: String,
  result: N.Conclusion, -previous: List<&2, U32>, -es: List<&2, G.Entry>,
  valid: R.Valid(c, Publication.published(result)),
  origins: G.AllEntries(EntryProperty(c, binding, public, book), es)) -> Valid(c, binding, public, book, instance, transaction(result, previous, es)):
  match result:
    case N.Conclusion{state, S.Response{status, value}, bytes}:
      transaction_status_valid(c, binding, public, book, instance, S.is_success(status), state, bytes, previous, es, valid, origins)

def register_fits_valid(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: InputBook, +instance: String,
  fits: Bool, -state: D.State, -previous: List<&2, U32>, -entry: G.Entry, -es: List<&2, G.Entry>,
  valid: R.Valid(c, state), origin: EntryOrigin(c, binding, public, book, entry),
  origins: G.AllEntries(EntryProperty(c, binding, public, book), es)) ->
  Valid(c, binding, public, book, instance, control(H.register_fits(fits, state, entry, es), previous)):
  match fits:
    case False{}: L.Both{valid, origins}
    case True{}: L.Both{valid, L.Both{origin, origins}}

def register_found_valid(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: InputBook, +instance: String,
  found: Maybe<&2, G.Entry>, -state: D.State, -previous: List<&2, U32>, +entry: G.Entry, -es: List<&2, G.Entry>,
  valid: R.Valid(c, state), origin: EntryOrigin(c, binding, public, book, entry),
  origins: G.AllEntries(EntryProperty(c, binding, public, book), es)) ->
  Valid(c, binding, public, book, instance, control(H.register_found(found, c, state, entry, es), previous)):
  match found:
    case Some{old}: L.Both{valid, origins}
    case None{}:
      register_fits_valid(c, binding, public, book, instance,
        R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{G.handle(entry)})),
        state, previous, entry, es, valid, origin, origins)

def invalidate_fits_valid(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: InputBook, +instance: String,
  fits: Bool, -state: D.State, -previous: List<&2, U32>, +handle: String, +es: List<&2, G.Entry>,
  valid: R.Valid(c, state), origins: G.AllEntries(EntryProperty(c, binding, public, book), es)) ->
  Valid(c, binding, public, book, instance, control(H.invalidate_fits(fits, state, instance, handle, es), previous)):
  match fits:
    case False{}: L.Both{valid, origins}
    case True{}:
      L.Both{valid, G.removal_preserves_registered_entry_properties(EntryProperty(c, binding, public, book), instance, handle, es, origins)}

def invalidate_found_valid(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: InputBook, +instance: String,
  found: Maybe<&2, G.Entry>, -state: D.State, -previous: List<&2, U32>, +handle: String, +es: List<&2, G.Entry>,
  valid: R.Valid(c, state), origins: G.AllEntries(EntryProperty(c, binding, public, book), es)) ->
  Valid(c, binding, public, book, instance, control(H.invalidate_found(found, c, state, instance, handle, es), previous)):
  match found:
    case None{}: L.Both{valid, origins}
    case Some{entry}:
      invalidate_fits_valid(c, binding, public, book, instance,
        R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})),
        state, previous, handle, es, valid, origins)

law cleanup_keeps_complete_published_pair:
  for failed: Bool
  for result: H.ControlResult
  for -previous: List<&2, U32>
  {control(H.cleanup_invalidation(failed, result), previous) == control(result, previous) : Published}
def cleanup_keeps_complete_published_pair(failed, result, previous):
  match failed result:
    case False{} _: {==}
    case True{} H.ControlResult{s, es, H.Metadata{W.InvalidatedReceipt{}}}: {==}
    case True{} H.ControlResult{s, es, H.Metadata{W.PreparedReceipt{handle}}}: {==}
    case True{} H.ControlResult{s, es, H.Error{status}}: {==}

def ordinary_certificate(~source: Source.Source, ~c: S.Configuration, -request: P.Request,
  -context: D.Context, +declaration: Source.JudgmentSyntactic,
  checked: Source.JudgmentAccepted(source, c, request, context, declaration)) ->
  R.Certifies(c, I.code(request), Source.program(source, declaration), context, I.arguments(request)):
  match checked:
    case L.Both{elaborated, L.Both{derived, L.Both{certificate, termination}}}: certificate

law record_next_is_exact_actual_conclusion:
  for -request: P.Request
  for -state: D.State
  for execution: Execution
  {Database.next(state, record(request, execution)) == Publication.published(N.conclude(execution_prepared(execution), state)) : D.State}
def record_next_is_exact_actual_conclusion(request, state, execution):
  match execution:
    case Execution{context, n, w, ts, prop, prepared}: {==}

def certified_transaction_valid(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: InputBook, +instance: String,
  +state: D.State, -previous: List<&2, U32>, -es: List<&2, G.Entry>,
  +request: P.Request, +execution: Execution,
  valid: R.Valid(c, state), origins: G.AllEntries(EntryProperty(c, binding, public, book), es),
  origin: Database.Origin(c, state, record(request, execution))) ->
  Valid(c, binding, public, book, instance, transaction(N.conclude(execution_prepared(execution), state), previous, es)):
  transaction_valid(c, binding, public, book, instance, N.conclude(execution_prepared(execution), state), previous, es,
    (%record_next_is_exact_actual_conclusion(request, state, execution) : R.Valid(c, _)
      Database.step_preserves_validity(c, state, record(request, execution), valid, origin)), origins)

def ordinary_valid(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: InputBook, +instance: String,
  +state: D.State, -previous: List<&2, U32>, -es: List<&2, G.Entry>,
  +request: P.Request, +execution: Execution,
  valid: R.Valid(c, state), origins: G.AllEntries(EntryProperty(c, binding, public, book), es),
  checked: Source.JudgmentAccepted(binding, c, request, execution_context(execution), origin(public, I.code(request))),
  authenticated: {D.authenticate(state, I.credential(request)) == Some{execution_context(execution)} : Maybe<&2, D.Context>},
  real: CoreReal(binding, c, public, state, request, execution)) ->
  Valid(c, binding, public, book, instance, transaction(N.conclude(execution_prepared(execution), state), previous, es)):
  certified_transaction_valid(c, binding, public, book, instance, state, previous, es, request, execution, valid, origins,
    core_origin(binding, c, public, state, request, execution,
        ordinary_certificate(binding, c, request, execution_context(execution),
          origin(public, I.code(request)), checked), authenticated, real))

def cached_with_origins(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: InputBook, checks: Checks(c, binding, public, book), +instance: String,
  +state: D.State, -previous: List<&2, U32>, +es: List<&2, G.Entry>,
  +raw: P.Request, +entry: G.Entry, +execution: Execution,
  valid: R.Valid(c, state),
  origins: L.E<G.AllEntries(EntryProperty(c, binding, public, book), es), G.AllEntries(EntryProperty(c, binding, public, book), es)>,
  present: {G.lookup(instance, I.code(raw), es) == Some{entry} : Maybe<&2, G.Entry>},
  authenticated: {D.authenticate(state, I.credential(raw)) == Some{execution_context(execution)} : Maybe<&2, D.Context>},
  real: CoreReal(binding, c, public, state, H.resolved(raw, entry), execution)) ->
  Valid(c, binding, public, book, instance, transaction(N.conclude(execution_prepared(execution), state), previous, es)):
  match raw origins:
    case P.Request{+credential, +handle, +arguments, +unused} L.Both{retained, queried}:
      certified_transaction_valid(c, binding, public, book, instance, state, previous, es, H.resolved(raw, entry), execution, valid, retained,
        core_origin(binding, c, public, state, H.resolved(raw, entry), execution,
            universal_from_mode(Source.environment(binding), c, entry,
              Source.program(binding, origin(public, G.code(entry))),
              current_origin_reopens_original_universal_certificate(c, binding, public, book, checks, instance, entry,
                G.lookup_recovers_registered_entry_property(EntryProperty(c, binding, public, book), instance, I.code(raw), es, entry, queried, present)))(execution_context(execution), I.arguments(raw)),
            authenticated, real))

law cached_execution_uses_only_current_registry_original_check_and_actual_core:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~book: InputBook
  for checks: Checks(c, binding, public, book)
  for +instance: String
  for +state: D.State
  for -previous: List<&2, U32>
  for +es: List<&2, G.Entry>
  for +raw: P.Request
  for +entry: G.Entry
  for +execution: Execution
  for valid: R.Valid(c, state)
  for origins: G.AllEntries(EntryProperty(c, binding, public, book), es)
  for present: {G.lookup(instance, I.code(raw), es) == Some{entry} : Maybe<&2, G.Entry>}
  for authenticated: {D.authenticate(state, I.credential(raw)) == Some{execution_context(execution)} : Maybe<&2, D.Context>}
  for real: CoreReal(binding, c, public, state, H.resolved(raw, entry), execution)
  Valid(c, binding, public, book, instance, transaction(N.conclude(execution_prepared(execution), state), previous, es))
def cached_execution_uses_only_current_registry_original_check_and_actual_core(c, binding, public, book, checks, instance,
  state, previous, es, raw, entry, execution, valid, origins, present, authenticated, real):
  cached_with_origins(c, binding, public, book, checks, instance, state, previous, es, raw, entry, execution, valid,
    registry_copy(c, binding, public, book, instance, es, origins), present, authenticated, real)

def step_selected(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: InputBook, checks: Checks(c, binding, public, book), +instance: String,
  before: Published, +index: Nat, invocation: Invocation,
  named: {call(c, binding, public, book, index) == invocation : Invocation},
  valid: Valid(c, binding, public, book, instance, before),
  real: Executed(binding, c, public, invocation),
  step: Step(c, instance, before, invocation)) -> Valid(c, binding, public, book, instance, next(c, instance, before, invocation)):
  match before invocation:
    case Published{+state, previous, +es} Invocation{world, +selected, input, Ordinary{+request, +execution}}:
      match valid step:
        case L.Both{state_valid, origins} L.Both{selected_state, L.Both{received, authenticated}}:
          ordinary_valid(c, binding, public, book, instance, state, previous, es, request, execution, state_valid, origins,
            (%named : Checked(binding, c, public, _) checks(index)), authenticated, (%selected_state : CoreReal(binding, c, public, _, request, execution) real))
    case Published{+state, previous, +es} Invocation{+world, +selected, +input, Prepare{+raw, +context, +read_only, +handle, +seal}}:
      match valid:
        case L.Both{state_valid, origins}:
          register_found_valid(c, binding, public, book, instance, G.lookup(instance, handle, es), state, previous,
            G.Entry{instance, handle, I.code(raw), I.proof(raw), read_only, seal}, es, state_valid,
            (index, Equal.cong(Invocation, Maybe<&2, G.Entry>, v => candidate(instance, v), call(c, binding, public, book, index),
              Invocation{world, selected, input, Prepare{raw, context, read_only, handle, seal}}, named)), origins)
    case Published{+state, previous, +es} Invocation{world, +selected, input, Execute{+raw, +entry, +execution}}:
      match valid step:
        case L.Both{state_valid, origins} L.Both{selected_state, L.Both{received, L.Both{authenticated, L.Both{fields, present}}}}:
          cached_execution_uses_only_current_registry_original_check_and_actual_core(c, binding, public, book, checks, instance,
            state, previous, es, raw, entry, execution, state_valid, origins, present, authenticated,
            (%selected_state : CoreReal(binding, c, public, _, H.resolved(raw, entry), execution) real))
    case Published{+state, previous, +es} Invocation{world, selected, input, Invalidate{+raw, context, +failed}}:
      match valid:
        case L.Both{state_valid, origins}:
          %Equal.sym(Published,
            control(H.cleanup_invalidation(failed, H.invalidate(c, state, instance, I.code(raw), es)), previous),
            control(H.invalidate(c, state, instance, I.code(raw), es), previous),
            cleanup_keeps_complete_published_pair(failed, H.invalidate(c, state, instance, I.code(raw), es), previous)) : Valid(c, binding, public, book, instance, _)
          invalidate_found_valid(c, binding, public, book, instance, G.lookup(instance, I.code(raw), es), state, previous,
            I.code(raw), es, state_valid, origins)
    case Published{state, previous, es} Invocation{world, selected, input, Unchanged{}}: valid

law operational_transition_preserves_shared_database_and_registry:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~book: InputBook
  for checks: Checks(c, binding, public, book)
  for executions: Executions(c, binding, public, book)
  for +instance: String
  for +before: Published
  for +index: Nat
  for valid: Valid(c, binding, public, book, instance, before)
  for step: Step(c, instance, before, call(c, binding, public, book, index))
  Valid(c, binding, public, book, instance, next(c, instance, before, call(c, binding, public, book, index)))
def operational_transition_preserves_shared_database_and_registry(c, binding, public, book, checks, executions, instance, before, index, valid, step):
  step_selected(c, binding, public, book, checks, instance, before, index, call(c, binding, public, book, index), {==}, valid,
    executions(index), step)
