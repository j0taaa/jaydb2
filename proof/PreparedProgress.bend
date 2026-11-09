# Completion for an entry chosen from the CURRENT operational registry. The
# original universal/termination declarations are recovered and specialized;
# no per-execution certificate or completed adapter result is a premise.
# Source-family reopening avoids treating a runtime entry/program as a ~template.
import Base
import ../contract/Data.bend as D
import ../contract/Interface.bend as I
import ../contract/Logic.bend as L
import ../contract/PreparedLaws.bend as H
import ../contract/PreparedRegistry.bend as G
import ../contract/Protocol.bend as P
import ../contract/Requirements.bend as R
import ../contract/Semantics.bend as S
import ../src/Core.bend as N
import ../src/Execution.bend as X
import ./Call.bend as Call
import ./ExecutionAdapter.bend as Adapter
import ./Preparation.bend as Preparation
import ./Publication.bend as Publication
import ./SourceService.bend as Source
import ./HostTransitions.bend as Host

def Productive(~c: S.Configuration, ~binding: Source.Source,
  ~public: List<&2, Source.FileSource>, -code: String,
  -context: D.Context, -arguments: D.Value, -initial: D.State, -n: Nat,
  -w: D.State, -events: List<&2, S.OperationEvent>, -response: S.Response) -> Type:
  &prepared: N.Prepared -> &output: List<&2, U32> ->
    L.E<{Adapter.drive(c, Succ{n}, X.Continue{X.start(Source.program(binding, Host.origin(public, code)), context, arguments, initial)}) == X.FinishOutput{output} : X.Iteration},
      L.E<{X.conclude(N.conclude(prepared, initial)) == X.FinishOutput{output} : X.Iteration},
        L.E<Preparation.Faithful(w, events, R.finalize(response, c, w), prepared),
          R.Valid(c, Publication.published(N.conclude(prepared, initial)))>>>

def output_faithful(~c: S.Configuration, ~binding: Source.Source,
  ~public: List<&2, Source.FileSource>, +code: String,
  +context: D.Context, +arguments: D.Value, +initial: D.State, +n: Nat,
  +w: D.State, +events: List<&2, S.OperationEvent>, +response: S.Response, +prepared: N.Prepared,
  result: {N.traverse(n, N.start(Source.program(binding, Host.origin(public, code)), context, arguments, initial), S.schema(c)) == S.Final{w, events, response} : S.Trace},
  preparation: {N.prepare(N.Stopped{w, events, response}, c) == Some{prepared} : Maybe<&2, N.Prepared>},
  faithful: Preparation.Faithful(w, events, R.finalize(response, c, w), prepared),
  output: &bytes: List<&2, U32> -> L.E<{X.conclude(N.conclude(prepared, initial)) == X.FinishOutput{bytes} : X.Iteration},
    R.Valid(c, Publication.published(N.conclude(prepared, initial)))>) ->
  Productive(c, binding, public, code, context, arguments, initial, n, w, events, response):
  match output:
    case (+bytes, L.Both{+exact, valid}):
      (prepared, bytes,
        L.Both{Equal.trans(X.Iteration,
          Adapter.drive(c, Succ{n}, X.Continue{X.start(Source.program(binding, Host.origin(public, code)), context, arguments, initial)}),
          X.prepared(N.prepare(N.Stopped{w, events, response}, c), initial), X.FinishOutput{bytes},
          Adapter.finite_execution_reaches_exact_adapter_result(c, n, initial,
            N.start(Source.program(binding, Host.origin(public, code)), context, arguments, initial), w, events, response, result),
          Equal.trans(X.Iteration,
            X.prepared(N.prepare(N.Stopped{w, events, response}, c), initial),
            X.conclude(N.conclude(prepared, initial)), X.FinishOutput{bytes},
            Equal.cong(Maybe<&2, N.Prepared>, X.Iteration, p => X.prepared(p, initial),
              N.prepare(N.Stopped{w, events, response}, c), Some{prepared}, preparation), exact)),
          L.Both{exact, L.Both{faithful, valid}}})

def finish_certified(~c: S.Configuration, ~binding: Source.Source,
  ~public: List<&2, Source.FileSource>, +code: String,
  +context: D.Context, +arguments: D.Value, +initial: D.State, +n: Nat,
  +w: D.State, +events: List<&2, S.OperationEvent>, +response: S.Response,
  result: {N.traverse(n, N.start(Source.program(binding, Host.origin(public, code)), context, arguments, initial), S.schema(c)) == S.Final{w, events, response} : S.Trace},
  configured: {R.configuration_is_valid(c) == True{} : Bool},
  integral: Call.ConclusionIntegral(c, initial, w, events, response)) ->
  Productive(c, binding, public, code, context, arguments, initial, n, w, events, response):
  match integral:
    case (+prepared, L.Both{preparation, L.Both{faithful, published_valid}}):
      output_faithful(c, binding, public, code, context, arguments, initial, n, w, events, response, prepared,
        result, preparation, faithful,
        Adapter.valid_conclusion_has_complete_output(c, N.conclude(prepared, initial), configured, published_valid))

law closed_source_family_certification_and_termination_give_actual_adapter_completion:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +code: String
  for +context: D.Context
  for +arguments: D.Value
  for certificate: R.Certifies(c, code, Source.program(binding, Host.origin(public, code)), context, arguments)
  for +initial: D.State
  for valid: R.Valid(c, initial)
  for credential: String
  for authenticated: {D.authenticate(initial, credential) == Some{context} : Maybe<&2, D.Context>}
  for +configured: {R.configuration_is_valid(c) == True{} : Bool}
  for terminates: I.Terminates(Source.program(binding, Host.origin(public, code)), S.schema(c), initial, context, arguments)
  exs n: Nat
  exs w: D.State
  exs events: List<&2, S.OperationEvent>
  exs response: S.Response
  Productive(c, binding, public, code, context, arguments, initial, n, w, events, response)
def closed_source_family_certification_and_termination_give_actual_adapter_completion(c, binding, public, code, context, arguments,
  certificate, initial, valid, credential, authenticated, configured, terminates):
  match terminates:
    case (+n, +w, +events, +response, reference):
      +result = Equal.trans(S.Trace,
        N.traverse(n, N.start(Source.program(binding, Host.origin(public, code)), context, arguments, initial), S.schema(c)),
        S.execute(n, Source.program(binding, Host.origin(public, code)), S.schema(c), initial, context, arguments), S.Final{w, events, response},
        N.fidelity_of_all_os_prefixes(n, Source.program(binding, Host.origin(public, code)), context, arguments, S.schema(c), initial), reference)
      (n, w, events, response,
        finish_certified(c, binding, public, code, context, arguments, initial, n, w, events, response, result, configured,
          Call.call_authenticated_prepares_and_concludes(c, code, Source.program(binding, Host.origin(public, code)), context, arguments,
            certificate, initial, valid, credential, authenticated, n, w, events, response, result, configured)))

def mode_execution(-a: I.Environment, -c: S.Configuration, entry: G.Entry, -program: S.Program,
  certificate: H.ModeCertificateValid(a, c, entry, program)) ->
  L.E<I.ProgramTerminates(c, program), H.Universal(c, G.code(entry), program)>:
  match entry:
    case G.Entry{i, h, code, proof, False{}, seal}:
      match certificate:
        case L.Both{L.Both{elaborated, terminates}, L.Both{derived, universal}}: L.Both{terminates, universal}
    case G.Entry{i, h, code, proof, True{}, seal}:
      match certificate:
        case L.Both{L.Both{L.Both{elaborated, terminates}, L.Both{derived, universal}}, read}: L.Both{terminates, universal}

def cached_from_original(~c: S.Configuration, ~binding: Source.Source,
  ~public: List<&2, Source.FileSource>, +state: D.State,
  +raw: P.Request, +entry: G.Entry, +context: D.Context,
  valid: R.Valid(c, state),
  authenticated: {D.authenticate(state, I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
  configured: {R.configuration_is_valid(c) == True{} : Bool},
  evidence: L.E<I.ProgramTerminates(c, Source.program(binding, Host.origin(public, G.code(entry)))),
    H.Universal(c, G.code(entry), Source.program(binding, Host.origin(public, G.code(entry))))>) ->
  &n: Nat -> &w: D.State -> &events: List<&2, S.OperationEvent> -> &response: S.Response ->
    Productive(c, binding, public, G.code(entry), context, I.arguments(raw), state, n, w, events, response):
  match raw evidence:
    case P.Request{credential, handle, +arguments, unused} L.Both{terminates, universal}:
      closed_source_family_certification_and_termination_give_actual_adapter_completion(c, binding, public, G.code(entry),
        context, arguments, universal(context, arguments), state, valid, credential, authenticated, configured,
        terminates(state, context, arguments))

law current_registered_original_declarations_force_cached_adapter_completion:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~book: Host.InputBook
  for checks: Host.Checks(c, binding, public, book)
  for +instance: String
  for before: Host.Published
  for +raw: P.Request
  for +entry: G.Entry
  for +context: D.Context
  for valid: Host.Valid(c, binding, public, book, instance, before)
  for present: {G.lookup(instance, I.code(raw), Host.entries(before)) == Some{entry} : Maybe<&2, G.Entry>}
  for authenticated: {D.authenticate(Host.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>}
  for configured: {R.configuration_is_valid(c) == True{} : Bool}
  exs n: Nat
  exs w: D.State
  exs events: List<&2, S.OperationEvent>
  exs response: S.Response
  Productive(c, binding, public, G.code(entry), context, I.arguments(raw), Host.database(before), n, w, events, response)
def current_registered_original_declarations_force_cached_adapter_completion(c, binding, public, book, checks,
  instance, before, raw, entry, context, valid, present, authenticated, configured):
  match before valid:
    case Host.Published{+state, previous, +es} L.Both{state_valid, origins}:
      cached_from_original(c, binding, public, state, raw, entry, context, state_valid, authenticated, configured,
        mode_execution(Source.environment(binding), c, entry, Source.program(binding, Host.origin(public, G.code(entry))),
          Host.current_origin_reopens_original_universal_certificate(c, binding, public, book, checks, instance, entry,
            G.lookup_recovers_registered_entry_property(Host.EntryProperty(c, binding, public, book), instance, I.code(raw), es, entry, origins, present))))
