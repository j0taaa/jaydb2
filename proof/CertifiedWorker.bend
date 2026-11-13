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
import ../src/ControlBridge.bend as ControlBridge
import ../src/Dispatch.bend as Dispatch
import ../src/Transport.bend as Transport
import ../src/WorkerResult.bend as Result

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

# A false artifact binding cannot accept a program. A true binding preserves
# exactly the generated oracle's checked evidence.
def artifact_sound(matches: Bool, -c: S.Configuration, -r: P.Request, -ctx: D.Context,
  -admit: Gate.Oracle(), sound: T.VerdictSound(admit(c, r, ctx), c, r, ctx)) ->
  T.VerdictSound(W.artifact_verdict(matches, c, r, ctx, admit), c, r, ctx):
  match matches:
    case False{}: Unit{}
    case True{}: sound

def artifact_checked(-c: S.Configuration, +code: String, +proof: String,
  checked: Evidence.Checked<c>) -> Evidence.Checked<c>:
  match checked:
    case Evidence.Checked{admit, bridge, same, sound}:
      Evidence.Checked{W.artifact_oracle(code, proof, admit), W.artifact_oracle(code, proof, bridge),
        Equal.cong(Gate.Oracle(), Gate.Oracle(), a => W.artifact_oracle(code, proof, a), bridge, admit, same),
        +r => +ctx => artifact_sound(String.eq(Gate.code(r), code) && String.eq(Resolve.proof(r), proof), c, r, ctx, admit, sound(r, ctx))}

# A shared guard bit preserves the generated oracle's universal soundness.
# WorkerBridge separately proves that the actual bit is exactly the selected
# source/proof comparison and that its Gate entry equals the original guard.
def matched_checked(-c: S.Configuration, +matches: Bool,
  checked: Evidence.Checked<c>) -> Evidence.Checked<c>:
  match checked:
    case Evidence.Checked{admit, bridge, same, sound}:
      Evidence.Checked{W.matched_oracle(matches, admit), W.matched_oracle(matches, bridge),
        Equal.cong(Gate.Oracle(), Gate.Oracle(), a => W.matched_oracle(matches, a), bridge, admit, same),
        +r => +ctx => artifact_sound(matches, c, r, ctx, admit, sound(r, ctx))}

# The literal native packet, actual decoded registry bytes and exact root/body
# feed the same UnifiedCore instance and finite worker composition.
def checked_prepared(~c: S.Configuration, k: T.Clause, +s: D.State,
  +bytes: List<&2, U32>, +registry_bytes: List<&2, U32>, +packet: List<&2, U32>, +state_bytes: List<&2, U32>, +body: List<&2, U32>,
  +raw: P.Request, +n: Nat, +code: String, +proof: String, checked: Evidence.Checked<c>,
  outer: {Transport.separate(bytes) == Some{Transport.Parts{registry_bytes, packet}} : Maybe<&2, Transport.Parts>},
  parts: {Transport.separate(packet) == Some{Transport.Parts{state_bytes, body}} : Maybe<&2, Transport.Parts>},
  root: {Dispatch.read_root(state_bytes, S.schema(c), S.limits(c)) == Some{s} : Maybe<&2, D.State>},
  received: {Dispatch.execution(Dispatch.received(S.limits(c), body, s)) == Input.InputReady{s, raw} : Input.PreAuthentication},
  configured: {R.configuration_is_valid(c) == True{} : Bool}, valid: R.Valid(c, s),
  complete: Bridge.SelectedComplete(c, s, n,
    Resolve.select(S.environment(c), s, W.registry_entries(ControlBridge.decode_registry(registry_bytes)), Resolve.Registered{raw}),
    W.artifact_oracle(code, proof, Evidence.oracle(c, checked)))) ->
  L.E<T.UnifiedCore(k, c, s, W.registry_entries(ControlBridge.decode_registry(registry_bytes)), Resolve.Registered{raw},
      W.artifact_oracle(code, proof, Evidence.oracle(c, checked))),
    {A.drive(c, Succ{n}, W.registered_packet(c, Transport.separate(bytes), code, proof, Evidence.oracle(c, checked))) ==
      Bridge.selection_reference(c, s, n, Resolve.select(S.environment(c), s, W.registry_entries(ControlBridge.decode_registry(registry_bytes)), Resolve.Registered{raw}),
        W.artifact_oracle(code, proof, Evidence.oracle(c, checked))) : X.Iteration}>:
  match checked:
    case Evidence.Checked{admit, bridge, same, sound}:
      %Equal.sym(Maybe<&2, Transport.Parts>, Transport.separate(bytes), Some{Transport.Parts{registry_bytes, packet}}, outer) :
        L.E<T.UnifiedCore(k, c, s, W.registry_entries(ControlBridge.decode_registry(registry_bytes)), Resolve.Registered{raw}, W.artifact_oracle(code, proof, admit)),
          {A.drive(c, Succ{n}, W.registered_packet(c, _, code, proof, admit)) == Bridge.selection_reference(c, s, n,
            Resolve.select(S.environment(c), s, W.registry_entries(ControlBridge.decode_registry(registry_bytes)), Resolve.Registered{raw}),
            W.artifact_oracle(code, proof, admit)) : X.Iteration}>
      %Equal.sym(X.Iteration,
        W.registered_packet(c, Some{Transport.Parts{registry_bytes, packet}}, code, proof, admit),
        W.unified(c, s, W.registry_entries(ControlBridge.decode_registry(registry_bytes)), Resolve.Registered{raw}, W.artifact_oracle(code, proof, admit)),
        Bridge.prepared_packet_equals_real_registry_selection(c, registry_bytes, packet, state_bytes, body, s, raw, code, proof, admit, parts, root, received)) :
        L.E<T.UnifiedCore(k, c, s, W.registry_entries(ControlBridge.decode_registry(registry_bytes)), Resolve.Registered{raw}, W.artifact_oracle(code, proof, admit)),
          {A.drive(c, Succ{n}, _) == Bridge.selection_reference(c, s, n,
            Resolve.select(S.environment(c), s, W.registry_entries(ControlBridge.decode_registry(registry_bytes)), Resolve.Registered{raw}),
            W.artifact_oracle(code, proof, admit)) : X.Iteration}>
      checked_unified(c, k, s, W.registry_entries(ControlBridge.decode_registry(registry_bytes)), Resolve.Registered{raw}, n,
        configured, valid, artifact_checked(c, code, proof, Evidence.Checked{admit, bridge, same, sound}), complete)

# Map only the finite emission proof while retaining its exact Core clause.
def lift_emission(-clause: Type, -old: Type, -new: Type,
  result: L.E<clause, old>, lift: old -> new) -> L.E<clause, new>:
  match result:
    case L.Both{core, finished}: L.Both{core, lift(finished)}

# The actual metadata-bearing prepared entry retains the same UnifiedCore
# clause and exact finite result, with checked route/principal projections.
# The generated checked_oracle package is closed, like C.config/Client.program;
# reopening it avoids duplicating a captured linear oracle. The original
# checked_prepared theorem above remains unrestricted.
def checked_routed_prepared(~c: S.Configuration, ~checked: Evidence.Checked<c>, k: T.Clause, +s: D.State,
  +bytes: List<&2, U32>, +registry_bytes: List<&2, U32>, +packet: List<&2, U32>, +state_bytes: List<&2, U32>, +body: List<&2, U32>,
  +raw: P.Request, +n: Nat, +code: String, +proof: String,
  +outer: {Transport.separate(bytes) == Some{Transport.Parts{registry_bytes, packet}} : Maybe<&2, Transport.Parts>},
  +parts: {Transport.separate(packet) == Some{Transport.Parts{state_bytes, body}} : Maybe<&2, Transport.Parts>},
  +root: {Dispatch.read_root(state_bytes, S.schema(c), S.limits(c)) == Some{s} : Maybe<&2, D.State>},
  +received: {Dispatch.execution(Dispatch.received(S.limits(c), body, s)) == Input.InputReady{s, raw} : Input.PreAuthentication},
  configured: {R.configuration_is_valid(c) == True{} : Bool}, valid: R.Valid(c, s),
  complete: Bridge.SelectedComplete(c, s, n,
    Resolve.select(S.environment(c), s, W.registry_entries(ControlBridge.decode_registry(registry_bytes)), Resolve.Registered{raw}),
    W.artifact_oracle(code, proof, Evidence.oracle(c, checked)))) ->
  L.E<T.UnifiedCore(k, c, s, W.registry_entries(ControlBridge.decode_registry(registry_bytes)), Resolve.Registered{raw},
      W.artifact_oracle(code, proof, Evidence.oracle(c, checked))),
    {Bridge.result_drive(c, Succ{n}, W.routed_bytes(c, bytes, code, proof, Evidence.oracle(c, checked))) ==
      Result.attach(Bridge.prepared_metadata(c, s, raw, W.registry_entries(ControlBridge.decode_registry(registry_bytes)), code, proof), Bridge.selection_reference(c, s, n, Resolve.select(S.environment(c), s, W.registry_entries(ControlBridge.decode_registry(registry_bytes)), Resolve.Registered{raw}),
        W.artifact_oracle(code, proof, Evidence.oracle(c, checked)))) : Result.Iteration}>:
  lift_emission(
    T.UnifiedCore(k, c, s, W.registry_entries(ControlBridge.decode_registry(registry_bytes)), Resolve.Registered{raw},
      W.artifact_oracle(code, proof, Evidence.oracle(c, checked))),
    {A.drive(c, Succ{n}, W.registered_packet(c, Transport.separate(bytes), code, proof, Evidence.oracle(c, checked))) ==
      Bridge.selection_reference(c, s, n, Resolve.select(S.environment(c), s, W.registry_entries(ControlBridge.decode_registry(registry_bytes)), Resolve.Registered{raw}),
        W.artifact_oracle(code, proof, Evidence.oracle(c, checked))) : X.Iteration},
    {Bridge.result_drive(c, Succ{n}, W.routed_bytes(c, bytes, code, proof, Evidence.oracle(c, checked))) ==
      Result.attach(Bridge.prepared_metadata(c, s, raw, W.registry_entries(ControlBridge.decode_registry(registry_bytes)), code, proof),
        Bridge.selection_reference(c, s, n, Resolve.select(S.environment(c), s, W.registry_entries(ControlBridge.decode_registry(registry_bytes)), Resolve.Registered{raw}),
          W.artifact_oracle(code, proof, Evidence.oracle(c, checked)))) : Result.Iteration},
    checked_prepared(c, k, s, bytes, registry_bytes, packet, state_bytes, body, raw, n, code, proof,
      checked, outer, parts, root, received, configured, valid, complete),
    finished => Bridge.lifted_finite_result(c, Succ{n},
    Bridge.prepared_metadata(c, s, raw, W.registry_entries(ControlBridge.decode_registry(registry_bytes)), code, proof),
    W.routed_bytes(c, bytes, code, proof, Evidence.oracle(c, checked)),
    W.registered_packet(c, Transport.separate(bytes), code, proof, Evidence.oracle(c, checked)),
    Bridge.selection_reference(c, s, n, Resolve.select(S.environment(c), s, W.registry_entries(ControlBridge.decode_registry(registry_bytes)), Resolve.Registered{raw}),
      W.artifact_oracle(code, proof, Evidence.oracle(c, checked))),
    Bridge.routed_bytes_lifts_registered(c, bytes, registry_bytes, packet, state_bytes, body, s, raw, code, proof, Evidence.oracle(c, checked), outer, parts, root, received), finished))
