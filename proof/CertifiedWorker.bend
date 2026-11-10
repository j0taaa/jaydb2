# Composition for a closed worker whose Book proves universal oracle soundness.
import Base
import ../contract/Bytes.bend as B
import ../contract/Theorems.bend as T
import ../contract/Logic.bend as L
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ../contract/Protocol.bend as P
import ../contract/PreparedRegistry.bend as Registry
import ../src/Input.bend as Input
import ../src/Gate.bend as Gate
import ../src/Resolve.bend as Resolve
import ../src/Worker.bend as W
import ../src/Execution.bend as X
import ./WorkerBridge.bend as Bridge
import ./ExecutionAdapter.bend as A
import ./Ingress.bend as Ingress
import ./OracleEvidence.bend as Evidence

def ingress(~c: S.Configuration, ~admit: Gate.Oracle(), k: T.Clause,
  +s: D.State, +body: List<&2, U32>, +n: Nat,
  configured: {R.configuration_is_valid(c) == True{} : Bool}, valid: R.Valid(c, s),
  complete: Bridge.IngressComplete(c, n, Input.read_message(B.nat64(R.limit_message(S.limits(c))), body, s), admit),
  sound: @r: P.Request -> T.OracleSoundness(c, r, admit)) ->
  L.E<T.IngressCore(k, c, s, body, admit),
    {A.drive(c, Succ{n}, W.ingress(c, s, body, admit)) == Bridge.ingress_reference(c, s, n,
      Input.read_message(B.nat64(R.limit_message(S.limits(c))), body, s), admit) : X.Iteration}>:
  L.Both{Ingress.ingress(k, c, s, body, admit, configured, valid,
      Bridge.decoded_oracle(Input.read_message(B.nat64(R.limit_message(S.limits(c))), body, s), c, admit, sound)),
    Bridge.worker_body_equals_ingress_composition(c, s, body, n, admit, complete)}

def unified(~c: S.Configuration, ~admit: Gate.Oracle(), k: T.Clause,
  +s: D.State, +entries: List<&2, Registry.Entry>, +input: Resolve.Input, +n: Nat,
  configured: {R.configuration_is_valid(c) == True{} : Bool}, valid: R.Valid(c, s),
  complete: Bridge.SelectedComplete(c, s, n, Resolve.select(S.environment(c), s, entries, input), admit),
  sound: @r: P.Request -> T.OracleSoundness(c, r, admit)) ->
  L.E<T.UnifiedCore(k, c, s, entries, input, admit),
    {A.drive(c, Succ{n}, W.unified(c, s, entries, input, admit)) == Bridge.selection_reference(c, s, n,
      Resolve.select(S.environment(c), s, entries, input), admit) : X.Iteration}>:
  L.Both{Ingress.unified(k, c, s, entries, input, admit, configured, valid,
      Bridge.selected_oracle(Resolve.select(S.environment(c), s, entries, input), c, admit, sound)),
    Bridge.worker_unified_equals_gate_composition(c, s, n, entries, input, admit, complete)}

# Checked is constructed in each admitted Book by checked_oracle. The oracle
# in the conclusion is exactly that package's admit field; no oracle premise
# remains for the caller to discharge.
def checked_ingress(~c: S.Configuration, k: T.Clause,
  +s: D.State, +body: List<&2, U32>, +n: Nat,
  configured: {R.configuration_is_valid(c) == True{} : Bool}, valid: R.Valid(c, s),
  checked: Evidence.Checked<c>,
  complete: Bridge.IngressComplete(c, n, Input.read_message(B.nat64(R.limit_message(S.limits(c))), body, s), Evidence.oracle(c, checked))) ->
  L.E<T.IngressCore(k, c, s, body, Evidence.oracle(c, checked)),
    {A.drive(c, Succ{n}, W.ingress(c, s, body, Evidence.oracle(c, checked))) == Bridge.ingress_reference(c, s, n,
      Input.read_message(B.nat64(R.limit_message(S.limits(c))), body, s), Evidence.oracle(c, checked)) : X.Iteration}>:
  match checked:
    case Evidence.Checked{admit, bridge, +same, sound}:
      %same : L.E<T.IngressCore(k, c, s, body, admit),
        {A.drive(c, Succ{n}, W.ingress(c, s, body, _)) == Bridge.ingress_reference(c, s, n,
          Input.read_message(B.nat64(R.limit_message(S.limits(c))), body, s), _) : X.Iteration}>
      L.Both{Ingress.ingress(k, c, s, body, admit, configured, valid,
          Bridge.decoded_oracle(Input.read_message(B.nat64(R.limit_message(S.limits(c))), body, s), c, admit, sound)),
        Bridge.worker_body_equals_ingress_composition(c, s, body, n, bridge,
          (%Equal.sym(Gate.Oracle(), bridge, admit, same) : Bridge.IngressComplete(c, n,
            Input.read_message(B.nat64(R.limit_message(S.limits(c))), body, s), _)
          complete))}

def checked_unified(~c: S.Configuration, k: T.Clause,
  +s: D.State, +entries: List<&2, Registry.Entry>, +input: Resolve.Input, +n: Nat,
  configured: {R.configuration_is_valid(c) == True{} : Bool}, valid: R.Valid(c, s),
  checked: Evidence.Checked<c>,
  complete: Bridge.SelectedComplete(c, s, n, Resolve.select(S.environment(c), s, entries, input), Evidence.oracle(c, checked))) ->
  L.E<T.UnifiedCore(k, c, s, entries, input, Evidence.oracle(c, checked)),
    {A.drive(c, Succ{n}, W.unified(c, s, entries, input, Evidence.oracle(c, checked))) == Bridge.selection_reference(c, s, n,
      Resolve.select(S.environment(c), s, entries, input), Evidence.oracle(c, checked)) : X.Iteration}>:
  match checked:
    case Evidence.Checked{admit, bridge, +same, sound}:
      %same : L.E<T.UnifiedCore(k, c, s, entries, input, admit),
        {A.drive(c, Succ{n}, W.unified(c, s, entries, input, _)) == Bridge.selection_reference(c, s, n,
          Resolve.select(S.environment(c), s, entries, input), _) : X.Iteration}>
      L.Both{Ingress.unified(k, c, s, entries, input, admit, configured, valid,
          Bridge.selected_oracle(Resolve.select(S.environment(c), s, entries, input), c, admit, sound)),
        Bridge.worker_unified_equals_gate_composition(c, s, n, entries, input, bridge,
          (%Equal.sym(Gate.Oracle(), bridge, admit, same) : Bridge.SelectedComplete(c, s, n,
            Resolve.select(S.environment(c), s, entries, input), _)
          complete))}

# The contract clauses themselves need only a valid configuration/root and
# the generated package. Finite completion is needed solely to index emission.
def checked_ingress_core(~c: S.Configuration, k: T.Clause,
  +s: D.State, +body: List<&2, U32>,
  configured: {R.configuration_is_valid(c) == True{} : Bool}, valid: R.Valid(c, s),
  checked: Evidence.Checked<c>) -> T.IngressCore(k, c, s, body, Evidence.oracle(c, checked)):
  match checked:
    case Evidence.Checked{admit, bridge, same, sound}:
      Ingress.ingress(k, c, s, body, admit, configured, valid,
        Bridge.decoded_oracle(Input.read_message(B.nat64(R.limit_message(S.limits(c))), body, s), c, admit, sound))

def checked_unified_core(~c: S.Configuration, k: T.Clause,
  +s: D.State, +entries: List<&2, Registry.Entry>, +input: Resolve.Input,
  configured: {R.configuration_is_valid(c) == True{} : Bool}, valid: R.Valid(c, s),
  checked: Evidence.Checked<c>) -> T.UnifiedCore(k, c, s, entries, input, Evidence.oracle(c, checked)):
  match checked:
    case Evidence.Checked{admit, bridge, same, sound}:
      Ingress.unified(k, c, s, entries, input, admit, configured, valid,
        Bridge.selected_oracle(Resolve.select(S.environment(c), s, entries, input), c, admit, sound))
