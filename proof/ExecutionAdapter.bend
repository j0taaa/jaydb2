# Finite unrolling of the generated execution wrapper's real step function.
# Continue and Prepare both pass their owned state to Execution.advance;
# FinishOutput and Inconsistent stop the foreign loop. Fuel is a proof index,
# not a runtime limit. This does not assert C/OS/compiler correspondence.
import Base
import ../contract/Data.bend as D
import ../contract/Interface.bend as I
import ../contract/Logic.bend as L
import ../contract/Protocol.bend as P
import ../contract/Requirements.bend as R
import ../contract/Semantics.bend as S
import ../src/Core.bend as N
import ../src/Execution.bend as X
import ../src/Transport.bend as T
import ./Foundations.bend as F
import ./Call.bend as C
import ./Proposal.bend as Proposal
import ./Preparation.bend as Q
import ./Publication.bend as U

def drive(~c: S.Configuration, n: Nat, iteration: X.Iteration) -> X.Iteration:
  match n iteration:
    case 0n i: i
    case 1n+k X.Continue{state}: drive(c, k, X.advance(state, c))
    case 1n+k X.Prepare{state}: drive(c, k, X.advance(state, c))
    case 1n+k X.FinishOutput{bytes}: X.FinishOutput{bytes}
    case 1n+k X.Inconsistent{}: X.Inconsistent{}

def Terminal(i: X.Iteration) -> Type:
  match i:
    case X.FinishOutput{bytes}: Unit
    case X.Inconsistent{}: Unit
    case _: Empty

law terminal_iteration_cannot_resume:
  for ~c: S.Configuration
  for n: Nat
  for i: X.Iteration
  for terminal: Terminal(i)
  {drive(c, n, i) == i : X.Iteration}
def terminal_iteration_cannot_resume(c, n, i, terminal):
  match n i:
    case 0n _: {==}
    case 1n+k X.FinishOutput{bytes}: {==}
    case 1n+k X.Inconsistent{}: {==}
    case 1n+k X.Continue{state}:
      L.ex_false({drive(c, 1n+k, X.Continue{state}) == X.Continue{state} : X.Iteration}, terminal)
    case 1n+k X.Prepare{state}:
      L.ex_false({drive(c, 1n+k, X.Prepare{state}) == X.Prepare{state} : X.Iteration}, terminal)

def packet_terminal(result: Maybe<&2, List<&2, U32>>) -> Terminal(X.packet_ready(result)):
  match result:
    case None{}: Unit{}
    case Some{bytes}: Unit{}

def state_terminal(state: Maybe<&2, List<&2, U32>>, +bytes: List<&2, U32>) ->
  Terminal(X.state_encoded(state, bytes)):
  match state:
    case None{}: Unit{}
    case Some{bs}: packet_terminal(T.join(bs, bytes))

law conclusion_is_terminal:
  for conclusion: N.Conclusion
  Terminal(X.conclude(conclusion))
def conclusion_is_terminal(conclusion):
  match conclusion:
    case N.Conclusion{state, S.Response{S.Success{}, value}, bytes}:
      state_terminal(P.encode(D.state_value(state)), bytes)
    case N.Conclusion{state, S.Response{S.Refusal{}, value}, bytes}: Unit{}
    case N.Conclusion{state, S.Response{S.Input{}, value}, bytes}: Unit{}
    case N.Conclusion{state, S.Response{S.Authentication{}, value}, bytes}: Unit{}
    case N.Conclusion{state, S.Response{S.Certificate{}, value}, bytes}: Unit{}
    case N.Conclusion{state, S.Response{S.DataError{}, value}, bytes}: Unit{}
    case N.Conclusion{state, S.Response{S.Limit{}, value}, bytes}: Unit{}
    case N.Conclusion{state, S.Response{S.Failure{}, value}, bytes}: Unit{}

law preparation_is_terminal:
  for +prepared: Maybe<&2, N.Prepared>
  for +initial: D.State
  Terminal(X.prepared(prepared, initial))
def preparation_is_terminal(prepared, initial):
  match prepared:
    case None{}: Unit{}
    case Some{p}: conclusion_is_terminal(N.conclude(p, initial))

def is_final(trace: S.Trace) -> Bool:
  match trace:
    case S.Prefix{s, ts}: False{}
    case S.Final{s, ts, r}: True{}

def final_impossible(-w: D.State, -events: List<&2, S.OperationEvent>, -response: S.Response,
  -other: D.State, -previous: List<&2, S.OperationEvent>,
  wrong: {S.Prefix{other, previous} == S.Final{w, events, response} : S.Trace}) -> Empty:
  F.absurd_boolean(Empty, Equal.cong(S.Trace, Bool, t => is_final(t),
    S.Prefix{other, previous}, S.Final{w, events, response}, wrong))

# A final reference trace determines the full actual adapter result. Prefixes
# have no final packet; their case is used only to define a total projection.
def final_output(~c: S.Configuration, initial: D.State, trace: S.Trace) -> X.Iteration:
  match trace:
    case S.Prefix{s, ts}: X.Inconsistent{}
    case S.Final{s, ts, r}: X.prepared(N.prepare(N.Stopped{s, ts, r}, c), initial)

# next is consumed only once. The induction hypothesis is universally
# quantified, rather than copying a machine with linear continuations.
def next_complete(~c: S.Configuration, +n: Nat, +initial: D.State,
  next: N.Machine, +w: D.State, +events: List<&2, S.OperationEvent>, +response: S.Response,
  obtained: {N.traverse(n, next, S.schema(c)) == S.Final{w, events, response} : S.Trace},
  recur: @machine: N.Machine ->
    {N.traverse(n, machine, S.schema(c)) == S.Final{w, events, response} : S.Trace} ->
    {drive(c, Succ{n}, X.Continue{X.StateExecution{initial, machine}}) ==
      X.prepared(N.prepare(N.Stopped{w, events, response}, c), initial) : X.Iteration}) ->
  {drive(c, Succ{n}, X.after_step(next, initial)) ==
    X.prepared(N.prepare(N.Stopped{w, events, response}, c), initial) : X.Iteration}:
  match next:
    case N.Running{s, action, ts}: recur(N.Running{s, action, ts}, obtained)
    case N.Stopped{s, ts, r}: recur(N.Stopped{s, ts, r}, obtained)

law finite_execution_reaches_exact_adapter_result:
  for ~c: S.Configuration
  for n: Nat
  for +initial: D.State
  for machine: N.Machine
  for +w: D.State
  for +events: List<&2, S.OperationEvent>
  for +response: S.Response
  for obtained: {N.traverse(n, machine, S.schema(c)) == S.Final{w, events, response} : S.Trace}
  {drive(c, Succ{n}, X.Continue{X.StateExecution{initial, machine}}) ==
    X.prepared(N.prepare(N.Stopped{w, events, response}, c), initial) : X.Iteration}
def finite_execution_reaches_exact_adapter_result(c, n, initial, machine, w, events, response, obtained):
  match n machine:
    case 0n N.Running{s, action, ts}:
      L.ex_false({drive(c, 1n, X.Continue{X.StateExecution{initial, N.Running{s, action, ts}}}) ==
        X.prepared(N.prepare(N.Stopped{w, events, response}, c), initial) : X.Iteration},
        final_impossible(w, events, response, s, ts, obtained))
    case 0n N.Stopped{s, ts, r}:
      Equal.cong(S.Trace, X.Iteration, trace => final_output(c, initial, trace),
        S.Final{s, ts, r}, S.Final{w, events, response}, obtained)
    case Succ{+k} N.Running{s, action, ts}:
      next_complete(c, k, initial, N.advance(N.Running{s, action, ts}, S.schema(c)), w, events, response, obtained,
        next => result => finite_execution_reaches_exact_adapter_result(c, k, initial, next, w, events, response, result))
    case Succ{+k} N.Stopped{+s, +ts, +r}:
      +equality = Equal.trans(S.Trace, S.Final{s, ts, r}, N.traverse(1n+k, N.Stopped{s, ts, r}, S.schema(c)),
        S.Final{w, events, response}, Equal.sym(S.Trace, N.traverse(1n+k, N.Stopped{s, ts, r}, S.schema(c)),
          S.Final{s, ts, r}, N.stopped_absorbs(1n+k, s, ts, r, S.schema(c))), obtained)
      Equal.trans(X.Iteration,
        drive(c, Succ{Succ{k}}, X.Continue{X.StateExecution{initial, N.Stopped{s, ts, r}}}),
        X.prepared(N.prepare(N.Stopped{s, ts, r}, c), initial),
        X.prepared(N.prepare(N.Stopped{w, events, response}, c), initial),
        terminal_iteration_cannot_resume(c, Succ{k},
          X.prepared(N.prepare(N.Stopped{s, ts, r}, c), initial),
          preparation_is_terminal(N.prepare(N.Stopped{s, ts, r}, c), initial)),
        Equal.cong(S.Trace, X.Iteration, trace => final_output(c, initial, trace),
          S.Final{s, ts, r}, S.Final{w, events, response}, equality))

# The actual generated Client.program() and Configuration.config() are closed
# declarations. Reopening them here does not copy a captured continuation.
law reference_final_reaches_exact_adapter_result:
  for ~c: S.Configuration
  for ~program: S.Program
  for +n: Nat
  for +context: D.Context
  for +arguments: D.Value
  for +initial: D.State
  for +w: D.State
  for +events: List<&2, S.OperationEvent>
  for +response: S.Response
  for result: {S.execute(n, program, S.schema(c), initial, context, arguments) == S.Final{w, events, response} : S.Trace}
  {drive(c, Succ{n}, X.Continue{X.start(program, context, arguments, initial)}) ==
    X.prepared(N.prepare(N.Stopped{w, events, response}, c), initial) : X.Iteration}
def reference_final_reaches_exact_adapter_result(c, program, n, context, arguments, initial, w, events, response, result):
  finite_execution_reaches_exact_adapter_result(c, n, initial, N.start(program, context, arguments, initial),
    w, events, response, Equal.trans(S.Trace,
      N.traverse(n, N.start(program, context, arguments, initial), S.schema(c)),
      S.execute(n, program, S.schema(c), initial, context, arguments), S.Final{w, events, response},
      N.fidelity_of_all_os_prefixes(n, program, context, arguments, S.schema(c), initial), result))

law terminating_program_reaches_terminal_adapter_result:
  for ~c: S.Configuration
  for ~program: S.Program
  for +context: D.Context
  for +arguments: D.Value
  for +initial: D.State
  for terminates: I.Terminates(program, S.schema(c), initial, context, arguments)
  exs n: Nat
  exs w: D.State
  exs events: List<&2, S.OperationEvent>
  exs response: S.Response
  L.E<{drive(c, Succ{n}, X.Continue{X.start(program, context, arguments, initial)}) ==
      X.prepared(N.prepare(N.Stopped{w, events, response}, c), initial) : X.Iteration},
    Terminal(drive(c, Succ{n}, X.Continue{X.start(program, context, arguments, initial)}))>
def terminating_program_reaches_terminal_adapter_result(c, program, context, arguments, initial, terminates):
  match terminates:
    case (+n, +w, +events, +response, result):
      +same = reference_final_reaches_exact_adapter_result(c, program, n, context, arguments, initial, w, events, response, result)
      (n, w, events, response, L.Both{same,
        (%Equal.sym(X.Iteration,
          drive(c, Succ{n}, X.Continue{X.start(program, context, arguments, initial)}),
          X.prepared(N.prepare(N.Stopped{w, events, response}, c), initial), same) : Terminal(_)
          preparation_is_terminal(N.prepare(N.Stopped{w, events, response}, c), initial))})

# Inconsistency is ruled out from the computed valid conclusion, rather than
# being accepted as progress. Success includes the actual private state packet.
def success_output(~c: S.Configuration, +state: D.State, -value: D.Value, +bytes: List<&2, U32>,
  assembled: Proposal.Assembled(P.encode(D.state_value(state)), bytes)) ->
  &output: List<&2, U32> ->
    {X.conclude(N.Conclusion{state, S.Response{S.Success{}, value}, bytes}) == X.FinishOutput{output} : X.Iteration}:
  match assembled:
    case (encoded, +packet, L.Both{encoding, L.Both{joined, exact}}):
      (Con{1, packet}, exact)

def structural_conclusion_output(~c: S.Configuration, conclusion: N.Conclusion,
  configured: {R.configuration_is_valid(c) == True{} : Bool},
  structure: {R.structure(c, U.published(conclusion)) == True{} : Bool}) ->
  &output: List<&2, U32> -> {X.conclude(conclusion) == X.FinishOutput{output} : X.Iteration}:
  match conclusion:
    case N.Conclusion{+state, S.Response{S.Success{}, value}, +bytes}:
      success_output(c, state, value, bytes,
        Proposal.success_technical_has_proposal_real(c, state, value, bytes, configured, structure))
    case N.Conclusion{state, S.Response{S.Refusal{}, value}, +bytes}: (Con{0, bytes}, {==})
    case N.Conclusion{state, S.Response{S.Input{}, value}, +bytes}: (Con{0, bytes}, {==})
    case N.Conclusion{state, S.Response{S.Authentication{}, value}, +bytes}: (Con{0, bytes}, {==})
    case N.Conclusion{state, S.Response{S.Certificate{}, value}, +bytes}: (Con{0, bytes}, {==})
    case N.Conclusion{state, S.Response{S.DataError{}, value}, +bytes}: (Con{0, bytes}, {==})
    case N.Conclusion{state, S.Response{S.Limit{}, value}, +bytes}: (Con{0, bytes}, {==})
    case N.Conclusion{state, S.Response{S.Failure{}, value}, +bytes}: (Con{0, bytes}, {==})

def retained_validity(~c: S.Configuration, -conclusion: N.Conclusion,
  valid: R.Valid(c, U.published(conclusion)),
  result: &output: List<&2, U32> -> {X.conclude(conclusion) == X.FinishOutput{output} : X.Iteration}) ->
  &output: List<&2, U32> -> L.E<{X.conclude(conclusion) == X.FinishOutput{output} : X.Iteration},
    R.Valid(c, U.published(conclusion))>:
  match result:
    case (bytes, exact): (bytes, L.Both{exact, valid})

law valid_conclusion_has_complete_output:
  for ~c: S.Configuration
  for +conclusion: N.Conclusion
  for configured: {R.configuration_is_valid(c) == True{} : Bool}
  for valid: R.Valid(c, U.published(conclusion))
  exs output: List<&2, U32>
  L.E<{X.conclude(conclusion) == X.FinishOutput{output} : X.Iteration},
    R.Valid(c, U.published(conclusion))>
def valid_conclusion_has_complete_output(c, conclusion, configured, valid):
  L.Both{+structure, stable} = valid
  retained_validity(c, conclusion, L.Both{structure, stable},
    structural_conclusion_output(c, conclusion, configured, structure))

def Productive(~c: S.Configuration, ~program: S.Program,
  -context: D.Context, -arguments: D.Value, -initial: D.State, -n: Nat,
  -w: D.State, -events: List<&2, S.OperationEvent>, -response: S.Response) -> Type:
  &prepared: N.Prepared -> &output: List<&2, U32> ->
    L.E<{drive(c, Succ{n}, X.Continue{X.start(program, context, arguments, initial)}) == X.FinishOutput{output} : X.Iteration},
      L.E<{X.conclude(N.conclude(prepared, initial)) == X.FinishOutput{output} : X.Iteration},
        L.E<Q.Faithful(w, events, R.finalize(response, c, w), prepared),
          R.Valid(c, U.published(N.conclude(prepared, initial)))>>>

def output_faithful(~c: S.Configuration, ~program: S.Program,
  +context: D.Context, +arguments: D.Value, +initial: D.State, +n: Nat,
  +w: D.State, +events: List<&2, S.OperationEvent>, +response: S.Response, +prepared: N.Prepared,
  result: {N.traverse(n, N.start(program, context, arguments, initial), S.schema(c)) == S.Final{w, events, response} : S.Trace},
  preparation: {N.prepare(N.Stopped{w, events, response}, c) == Some{prepared} : Maybe<&2, N.Prepared>},
  faithful: Q.Faithful(w, events, R.finalize(response, c, w), prepared),
  output: &bytes: List<&2, U32> -> L.E<{X.conclude(N.conclude(prepared, initial)) == X.FinishOutput{bytes} : X.Iteration},
    R.Valid(c, U.published(N.conclude(prepared, initial)))>) ->
  Productive(c, program, context, arguments, initial, n, w, events, response):
  match output:
    case (+bytes, L.Both{+exact, valid}):
      (prepared, bytes,
        L.Both{Equal.trans(X.Iteration,
          drive(c, Succ{n}, X.Continue{X.start(program, context, arguments, initial)}),
          X.prepared(N.prepare(N.Stopped{w, events, response}, c), initial), X.FinishOutput{bytes},
          finite_execution_reaches_exact_adapter_result(c, n, initial,
            N.start(program, context, arguments, initial), w, events, response, result),
          Equal.trans(X.Iteration,
            X.prepared(N.prepare(N.Stopped{w, events, response}, c), initial),
            X.conclude(N.conclude(prepared, initial)), X.FinishOutput{bytes},
            Equal.cong(Maybe<&2, N.Prepared>, X.Iteration, p => X.prepared(p, initial),
              N.prepare(N.Stopped{w, events, response}, c), Some{prepared}, preparation), exact)), L.Both{exact, L.Both{faithful, valid}}})

def finish_certified(~c: S.Configuration, ~program: S.Program,
  +context: D.Context, +arguments: D.Value, +initial: D.State, +n: Nat,
  +w: D.State, +events: List<&2, S.OperationEvent>, +response: S.Response,
  result: {N.traverse(n, N.start(program, context, arguments, initial), S.schema(c)) == S.Final{w, events, response} : S.Trace},
  configured: {R.configuration_is_valid(c) == True{} : Bool},
  integral: C.ConclusionIntegral(c, initial, w, events, response)) ->
  Productive(c, program, context, arguments, initial, n, w, events, response):
  match integral:
    case (+prepared, L.Both{preparation, L.Both{faithful, published_valid}}):
      output_faithful(c, program, context, arguments, initial, n, w, events, response, prepared,
        result, preparation, faithful,
        valid_conclusion_has_complete_output(c, N.conclude(prepared, initial), configured, published_valid))

law certified_terminating_adapter_emits_complete_output:
  for ~c: S.Configuration
  for ~program: S.Program
  for -code: String
  for +context: D.Context
  for +arguments: D.Value
  for certificate: R.Certifies(c, code, program, context, arguments)
  for +initial: D.State
  for valid: R.Valid(c, initial)
  for credential: String
  for authenticated: {D.authenticate(initial, credential) == Some{context} : Maybe<&2, D.Context>}
  for +configured: {R.configuration_is_valid(c) == True{} : Bool}
  for terminates: I.Terminates(program, S.schema(c), initial, context, arguments)
  exs n: Nat
  exs w: D.State
  exs events: List<&2, S.OperationEvent>
  exs response: S.Response
  exs prepared: N.Prepared
  exs output: List<&2, U32>
  L.E<{drive(c, Succ{n}, X.Continue{X.start(program, context, arguments, initial)}) == X.FinishOutput{output} : X.Iteration},
    L.E<{X.conclude(N.conclude(prepared, initial)) == X.FinishOutput{output} : X.Iteration},
      L.E<Q.Faithful(w, events, R.finalize(response, c, w), prepared),
        R.Valid(c, U.published(N.conclude(prepared, initial)))>>>
def certified_terminating_adapter_emits_complete_output(c, program, code, context, arguments, certificate,
  initial, valid, credential, authenticated, configured, terminates):
  match terminates:
    case (+n, +w, +events, +response, reference):
      +result = Equal.trans(S.Trace,
        N.traverse(n, N.start(program, context, arguments, initial), S.schema(c)),
        S.execute(n, program, S.schema(c), initial, context, arguments), S.Final{w, events, response},
        N.fidelity_of_all_os_prefixes(n, program, context, arguments, S.schema(c), initial), reference)
      (n, w, events, response,
        finish_certified(c, program, context, arguments, initial, n, w, events, response, result, configured,
          C.call_authenticated_prepares_and_concludes(c, code, program, context, arguments, certificate,
            initial, valid, credential, authenticated, n, w, events, response, result, configured)))
