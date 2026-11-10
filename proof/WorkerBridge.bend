# The generated entry calls Worker.packet/registered_packet literally; the
# native conversion and step laws are checked in that same admitted Book.
# Here the pure worker result is related to the theorem's exact Gate path.
# Fuel is a proof index only, never an execution quota or prefix replay.
import Base
import ../contract/Bytes.bend as B
import ../contract/Theorems.bend as Theorems
import ../contract/Logic.bend as L
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Requirements.bend as R
import ../contract/Semantics.bend as S
import ../contract/PreparedRegistry.bend as Registry
import ../src/Core.bend as N
import ../src/Gate.bend as Gate
import ../src/Resolve.bend as Resolve
import ../src/Input.bend as Input
import ../src/Worker.bend as W
import ../src/Dispatch.bend as Dispatch
import ../src/Execution.bend as X
import ./ExecutionAdapter.bend as A

def reference(~c: S.Configuration, s: D.State, n: Nat, entry: Gate.Entry) -> X.Iteration:
  match entry:
    case Gate.Halted{r}: X.result(Gate.early(r, s))
    case Gate.Started{ctx, machine}: X.result(Gate.finish(N.traverse(n, machine, S.schema(c)), c, s))

def Complete(c: S.Configuration, n: Nat, entry: Gate.Entry) -> Type:
  match entry:
    case Gate.Halted{r}: Unit
    case Gate.Started{ctx, machine}:
      &w: D.State -> &ts: List<&2, S.OperationEvent> -> &r: S.Response ->
        {N.traverse(n, machine, S.schema(c)) == S.Final{w, ts, r} : S.Trace}

def result_terminal(result: Maybe<&2, N.Conclusion>) -> A.Terminal(X.result(result)):
  match result:
    case None{}: Unit{}
    case Some{c}: A.conclusion_is_terminal(c)

def machine_bridge(~c: S.Configuration, +s: D.State, +n: Nat, machine: N.Machine,
  +w: D.State, +ts: List<&2, S.OperationEvent>, +r: S.Response,
  +exact: {N.traverse(n, machine, S.schema(c)) == S.Final{w, ts, r} : S.Trace}) ->
  {A.drive(c, Succ{n}, X.Continue{X.StateExecution{s, machine}}) ==
    X.result(Gate.finish(N.traverse(n, machine, S.schema(c)), c, s)) : X.Iteration}:
  %Equal.sym(S.Trace, N.traverse(n, machine, S.schema(c)), S.Final{w, ts, r}, exact) :
    {A.drive(c, Succ{n}, X.Continue{X.StateExecution{s, machine}}) == X.result(Gate.finish(_, c, s)) : X.Iteration}
  A.finite_execution_reaches_exact_adapter_result(c, n, s, machine, w, ts, r, exact)

law worker_loop_equals_gate_composition:
  for ~c: S.Configuration
  for +s: D.State
  for +n: Nat
  for entry: Gate.Entry
  for complete: Complete(c, n, entry)
  {A.drive(c, Succ{n}, W.entered(entry, s)) == reference(c, s, n, entry) : X.Iteration}
def worker_loop_equals_gate_composition(c, s, n, entry, complete):
  match entry:
    case Gate.Halted{+r}:
      A.terminal_iteration_cannot_resume(c, Succ{n}, X.result(Gate.early(r, s)), result_terminal(Gate.early(r, s)))
    case Gate.Started{ctx, machine}:
      match complete:
        case (w, ts, r, exact): machine_bridge(c, s, n, machine, w, ts, r, exact)

# Whole-body entry is exactly checked ingress, followed by direct Resolve
# selection and Gate.begin. This is also the native entry after state decoding.
law raw_body_enters_proved_gate:
  for ~c: S.Configuration
  for +s: D.State
  for body: List<&2, U32>
  for admit: Gate.Oracle()
  {W.ingress(c, s, body, admit) ==
    W.decoded(c, s, Input.read_message(B.nat64(R.limit_message(S.limits(c))), body, s), admit) : X.Iteration}
def raw_body_enters_proved_gate(c, s, body, admit): {==}

law prepared_enters_proved_selection:
  for ~c: S.Configuration
  for +s: D.State
  for entries: List<&2, Registry.Entry>
  for raw: P.Request
  for admit: Gate.Oracle()
  {W.registered(c, s, Input.InputReady{s, raw}, entries, admit) ==
    W.selected(Resolve.select(S.environment(c), s, entries, Resolve.Registered{raw}), c, s, admit) : X.Iteration}
def prepared_enters_proved_selection(c, s, entries, raw, admit): {==}

def ingress_reference(~c: S.Configuration, initial: D.State, n: Nat, input: Input.PreAuthentication,
  admit: Gate.Oracle()) -> X.Iteration:
  match input:
    case Input.ErrorTransport{}: X.Inconsistent{}
    case Input.ErrorMessage{status}: X.result(Gate.early(S.response_error(status), initial))
    case Input.InputReady{+s, r}: reference(c, s, n, Gate.begin(c, s, r, admit))

def IngressComplete(~c: S.Configuration, n: Nat, input: Input.PreAuthentication,
  admit: Gate.Oracle()) -> Type:
  match input:
    case Input.InputReady{s, r}: Complete(c, n, Gate.begin(c, s, r, admit))
    case _: Unit

law decoded_worker_equals_ingress_composition:
  for ~c: S.Configuration
  for +n: Nat
  for +initial: D.State
  for input: Input.PreAuthentication
  for admit: Gate.Oracle()
  for complete: IngressComplete(c, n, input, admit)
  {A.drive(c, Succ{n}, W.decoded(c, initial, input, admit)) == ingress_reference(c, initial, n, input, admit) : X.Iteration}
def decoded_worker_equals_ingress_composition(c, n, initial, input, admit, complete):
  match input:
    case Input.ErrorTransport{}: A.terminal_iteration_cannot_resume(c, Succ{n}, X.Inconsistent{}, Unit{})
    case Input.ErrorMessage{+status}:
      A.terminal_iteration_cannot_resume(c, Succ{n},
        X.result(Gate.early(S.response_error(status), initial)),
        result_terminal(Gate.early(S.response_error(status), initial)))
    case Input.InputReady{+s, r}:
      worker_loop_equals_gate_composition(c, s, n, Gate.begin(c, s, r, admit), complete)

law worker_body_equals_ingress_composition:
  for ~c: S.Configuration
  for +s: D.State
  for +body: List<&2, U32>
  for +n: Nat
  for admit: Gate.Oracle()
  for complete: IngressComplete(c, n,
    Input.read_message(B.nat64(R.limit_message(S.limits(c))), body, s), admit)
  {A.drive(c, Succ{n}, W.ingress(c, s, body, admit)) == ingress_reference(c, s, n,
    Input.read_message(B.nat64(R.limit_message(S.limits(c))), body, s), admit) : X.Iteration}
def worker_body_equals_ingress_composition(c, s, body, n, admit, complete):
  decoded_worker_equals_ingress_composition(c, n, s,
    Input.read_message(B.nat64(R.limit_message(S.limits(c))), body, s), admit, complete)

def selection_reference(~c: S.Configuration, +s: D.State, n: Nat,
  selection: Resolve.Selection, admit: Gate.Oracle()) -> X.Iteration:
  match selection:
    case Resolve.Denied{status}: X.result(Gate.early(S.response_error(status), s))
    case Resolve.Selected{r}: reference(c, s, n, Gate.begin(c, s, r, admit))

def SelectedComplete(~c: S.Configuration, s: D.State, n: Nat,
  selection: Resolve.Selection, admit: Gate.Oracle()) -> Type:
  match selection:
    case Resolve.Denied{status}: Unit
    case Resolve.Selected{r}: Complete(c, n, Gate.begin(c, s, r, admit))

law worker_selection_equals_unified_composition:
  for ~c: S.Configuration
  for +s: D.State
  for +n: Nat
  for selection: Resolve.Selection
  for admit: Gate.Oracle()
  for complete: SelectedComplete(c, s, n, selection, admit)
  {A.drive(c, Succ{n}, W.selected(selection, c, s, admit)) ==
    selection_reference(c, s, n, selection, admit) : X.Iteration}
def worker_selection_equals_unified_composition(c, s, n, selection, admit, complete):
  match selection:
    case Resolve.Denied{+status}:
      A.terminal_iteration_cannot_resume(c, Succ{n}, X.result(Gate.early(S.response_error(status), s)),
        result_terminal(Gate.early(S.response_error(status), s)))
    case Resolve.Selected{r}:
      worker_loop_equals_gate_composition(c, s, n, Gate.begin(c, s, r, admit), complete)

law worker_unified_equals_gate_composition:
  for ~c: S.Configuration
  for +s: D.State
  for +n: Nat
  for entries: List<&2, Registry.Entry>
  for input: Resolve.Input
  for admit: Gate.Oracle()
  for complete: SelectedComplete(c, s, n, Resolve.select(S.environment(c), s, entries, input), admit)
  {A.drive(c, Succ{n}, W.unified(c, s, entries, input, admit)) ==
    selection_reference(c, s, n, Resolve.select(S.environment(c), s, entries, input), admit) : X.Iteration}
def worker_unified_equals_gate_composition(c, s, n, entries, input, admit, complete):
  worker_selection_equals_unified_composition(c, s, n, Resolve.select(S.environment(c), s, entries, input), admit, complete)

# Native private transport reaches the same complete-body function once the
# host's exact canonical root has been decoded. Physical pipe identity is T3.
law native_root_enters_ingress:
  for ~c: S.Configuration
  for s: D.State
  for body: List<&2, U32>
  for admit: Gate.Oracle()
  {W.root(c, Some{s}, body, None{}, admit) == W.ingress(c, s, body, admit) : X.Iteration}
def native_root_enters_ingress(c, s, body, admit): {==}

law native_registered_root_enters_selection:
  for ~c: S.Configuration
  for +s: D.State
  for body: List<&2, U32>
  for entries: List<&2, Registry.Entry>
  for admit: Gate.Oracle()
  {W.root(c, Some{s}, body, Some{entries}, admit) ==
    W.registered(c, s, Dispatch.execution(Dispatch.received(S.limits(c), body, s)), entries, admit) : X.Iteration}
def native_registered_root_enters_selection(c, s, body, entries, admit): {==}

# The bridge's finite witness is supplied by Core's existing Progress clause;
# it is not a new termination assumption about an accepted request.
law core_progress_supplies_worker_completion:
  for ~c: S.Configuration
  for s: D.State
  for ctx: D.Context
  for machine: N.Machine
  for progress: Theorems.Progress(c, s, machine)
  exs n: Nat
  Complete(c, n, Gate.Started{ctx, machine})
def core_progress_supplies_worker_completion(c, s, ctx, machine, progress):
  match progress:
    case (n, w, ts, r, L.Both{exact, rest}): (n, (w, ts, r, exact))
