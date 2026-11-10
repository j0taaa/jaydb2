# PROPOSED full ordinary/prepared service specification; not a proof witness.
# One fixed observer supplies every policy-relevant event. The two core views
# below are typed projections used to reuse transaction lemmas, never substitutes
# for proving the complete contract over this observer. No implementation may
# choose which real events appear. Native/Rust/IO simulation remains required.
import Base
import ../../../contract/Bytes.bend as B
import ../../../contract/Data.bend as D
import ../../../contract/Interface.bend as I
import ../../../contract/LAWS.bend as K
import ../../../contract/Logic.bend as L
import ../../../contract/Protocol.bend as P
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/PreparedRegistry.bend as G
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/Requirements.bend as R
import ../../../contract/Resources.bend as X
import ../../../contract/Semantics.bend as S
import ../../../contract/ReadOnlyContract.bend as RO

type Outcome is Data:
  Transaction{response: S.Response}
  Receipt{receipt: W.Receipt}

def outcome_value(outcome: Outcome) -> D.Value:
  match outcome:
    case Transaction{response}: S.response_value(response)
    case Receipt{receipt}: W.receipt_value(receipt)

type Snapshot is Data:
  Snapshot{instance: String, database: D.State, response: List<&2, U32>, entries: List<&2, G.Entry>}

def instance(s: Snapshot) -> String:
  Snapshot{i, d, r, e} = s
  i

def database(s: Snapshot) -> D.State:
  Snapshot{i, d, r, e} = s
  d

def last_response(s: Snapshot) -> List<&2, U32>:
  Snapshot{i, d, r, e} = s
  r

def registry(s: Snapshot) -> List<&2, G.Entry>:
  Snapshot{i, d, r, e} = s
  e

type Mutation is Data:
  Publish{response: S.Response, bytes: List<&2, U32>}
  Register{entry: G.Entry}
  Invalidate{handle: String}

# Records refer to actual globally ordered mutation events. Their after-values
# are observed data; authorization and validity must be proved separately.
type Past is Data:
  Past{world: Nat, input: X.Reception, time: Nat, prepared: Bool,
    mutation: Mutation, before: Snapshot, after: Snapshot}

type Fact is Type:
  Ordinary{fact: I.Fact}
  PreparedKernel{fact: I.Fact}
  Boot{snapshot: Snapshot}
  Selected{snapshot: Snapshot}
  WireReceived{wire: W.WireRequest}
  IdentityEstablished{wire: W.WireRequest, context: Maybe<&2, D.Context>}
  UniversalAccepted{wire: W.WireRequest, context: D.Context, program: S.Program}
  HandleChosen{handle: String}
  UniversalRejected{wire: W.WireRequest, context: D.Context}
  EntryResolved{raw: P.Request, entry: G.Entry, logical: P.Request, context: D.Context, program: S.Program}
  ArtifactSealed{entry: G.Entry, program: S.Program}
  Mutated{prepared: Bool, mutation: Mutation, before: Snapshot, after: Snapshot}
  ReceiptPrepared{receipt: W.Receipt, bytes: List<&2, U32>}
  ReceiptConcluded{receipt: W.Receipt, result: H.ControlResult, snapshot: Snapshot, closes: Bool}

# Processable is the original external technical condition, independent of the
# candidate artifact or checker decision. Artifacts denotes exact current bytes
# and semantic source binding; hash equality is NOT its definition.
type Environment is Type:
  Environment{identity: String,
    elaborates: S.Configuration -> String -> S.Program -> Type,
    derives: S.Configuration -> String -> Type -> Type,
    processable: I.Scenario -> Type,
    failure: String -> I.Scenario -> Nat -> X.Stage -> String -> Bool -> Type,
    delivery_failure: String -> I.Scenario -> Nat -> Type,
    artifacts: H.Artifacts,
    run: Nat -> Nat,
    observes: String -> I.Scenario -> Nat -> Fact -> Type}

def observes(a: Environment, k: String, x: I.Scenario, t: Nat, f: Fact) -> Type:
  Environment{id, el, de, pr, fr, df, ar, run, ob} = a
  ob(k, x, t, f)

def artifacts(a: Environment) -> H.Artifacts:
  Environment{id, el, de, pr, fr, df, ar, run, ob} = a
  ar

def Processable(a: Environment, x: I.Scenario) -> Type:
  Environment{id, el, de, pr, fr, df, ar, run, ob} = a
  pr(x)

# A run is one semantic execution/lifetime of this service, supplied by the
# fixed operational interpretation. It is not a random wire/instance string.
# Counterfactual executions and restarts remain different runs even if all their
# random strings coincide. Grouping never depends on the candidate's decisions.
def scenario_world(x: I.Scenario) -> Nat:
  match x:
    case I.Initialize{world, c, s, pi}: world
    case I.Serve{world, c, s, input}: world

def run_of(a: Environment, world: Nat) -> Nat:
  Environment{id, el, de, pr, fr, df, ar, run, ob} = a
  run(world)

def OrdinaryDispatch(d: W.Dispatch) -> Type:
  match d:
    case W.OrdinaryBody{bytes}: Unit
    case _: Empty

def OrdinaryDisposition(d: X.Disposition) -> Type:
  match d:
    case X.ProcessBody{bytes}: OrdinaryDispatch(W.route_dispatch(bytes))
    case _: Unit

# This is only protocol classification of physical bytes. It is not an
# implementation-dependent admissibility predicate or a checker veto.
def OrdinaryPath(x: I.Scenario) -> Type:
  match x:
    case I.Initialize{world, c, s, pi}: Unit
    case I.Serve{world, c, s, input}: OrdinaryDisposition(X.decide_reception(c, input))

def PreparedDispatch(d: W.Dispatch) -> Type:
  match d:
    case W.OrdinaryBody{bytes}: Empty
    case _: Unit

def PreparedDisposition(d: X.Disposition) -> Type:
  match d:
    case X.ProcessBody{bytes}: PreparedDispatch(W.route_dispatch(bytes))
    case _: Empty

def PreparedPath(x: I.Scenario) -> Type:
  match x:
    case I.Initialize{world, c, s, pi}: Empty
    case I.Serve{world, c, s, input}: PreparedDisposition(X.decide_reception(c, input))

def core_fact(prepared: Bool, f: I.Fact) -> Fact:
  match prepared:
    case False{}: Ordinary{f}
    case True{}: PreparedKernel{f}

# These projections preserve the SAME external Processable. Compatibility
# below is explicitly restricted to OrdinaryPath, never a global old Contract.
def core_environment(prepared: Bool, a: Environment) -> I.Environment:
  match a:
    case Environment{id, el, de, pr, fr, df, ar, run, ob}:
      I.Environment{id, el, de, k => x => t => f => ob(k, x, t, core_fact(prepared, f)), pr, fr, df}

def Before(~a: Environment, -k: String, -x: I.Scenario, -t: Nat, -f: Fact) -> Type:
  &u: Nat -> L.E<{Nat.is_lt(u, t) == True{} : Bool}, observes(a, k, x, u, f)>

def Eventually(~a: Environment, -k: String, -x: I.Scenario, -f: Fact) -> Type:
  &t: Nat -> observes(a, k, x, t, f)

def Occurs(-record: Past, records: List<&2, Past>) -> Type:
  match records:
    case Nil{}: Empty
    case Con{head, tail}: L.Disjunction<{head == record : Past}, Occurs(record, tail)>

def replay(records: List<&2, Past>, initial: Snapshot) -> Snapshot:
  match records:
    case Nil{}: initial
    case Con{Past{world, input, time, mode, mutation, before, after}, tail}: replay(tail, after)

def HistoryObserved(~a: Environment, -k: String, -c: S.Configuration,
  records: List<&2, Past>, +previous: Snapshot, lower: Nat, +upper: Nat, +run: Nat) -> Type:
  match records:
    case Nil{}: Unit
    case Con{Past{+world, +input, +time, +mode, +mutation, +before, +after}, tail}:
      L.E<{run_of(a, world) == run : Nat},
        L.E<{before == previous : Snapshot},
          L.E<{instance(before) == instance(after) : String},
          L.E<{Nat.is_lt(lower, time) == True{} : Bool},
            L.E<{Nat.is_lt(time, upper) == True{} : Bool},
              L.E<observes(a, k, I.Serve{world, c, database(before), input}, time, Mutated{mode, mutation, before, after}),
                HistoryObserved(a, k, c, tail, after, time, upper, run)>>>>>>

# Completeness ranges over every physical call of the same instance. Omitting a
# prior real mutation cannot manufacture a convenient current registry/state.
def HistoryComplete(~a: Environment, -k: String, -c: S.Configuration,
  -i: String, -lower: Nat, -upper: Nat, -records: List<&2, Past>, -run: Nat) -> Type:
  @world: Nat -> @input: X.Reception -> @time: Nat -> @mode: Bool ->
  @mutation: Mutation -> @before: Snapshot -> @after: Snapshot ->
    {run_of(a, world) == run : Nat} -> {instance(before) == i : String} -> {Nat.is_lt(lower, time) == True{} : Bool} ->
    {Nat.is_lt(time, upper) == True{} : Bool} ->
    observes(a, k, I.Serve{world, c, database(before), input}, time, Mutated{mode, mutation, before, after}) ->
      Occurs(Past{world, input, time, mode, mutation, before, after}, records)

def Current(~a: Environment, -k: String, -x: I.Scenario, -time: Nat, +snapshot: Snapshot) -> Type:
  &world: Nat -> &seed: D.State -> &proof: String -> &started: Nat ->
  &records: List<&2, Past> ->
    L.E<{run_of(a, world) == run_of(a, scenario_world(x)) : Nat},
      L.E<observes(a, k, I.Initialize{world, I.configuration(x), seed, proof}, started,
        Boot{Snapshot{instance(snapshot), seed, Nil{}, Nil{}}}),
      L.E<{Nat.is_lt(started, time) == True{} : Bool},
        L.E<HistoryObserved(a, k, I.configuration(x), records,
          Snapshot{instance(snapshot), seed, Nil{}, Nil{}}, started, time, run_of(a, scenario_world(x))),
          L.E<HistoryComplete(a, k, I.configuration(x), instance(snapshot), started, time, records, run_of(a, scenario_world(x))),
            {snapshot == replay(records, Snapshot{instance(snapshot), seed, Nil{}, Nil{}}) : Snapshot}>>>>>

def SelectedBefore(~a: Environment, -k: String, -x: I.Scenario, -time: Nat, -snapshot: Snapshot) -> Type:
  Before(a, k, x, time, Selected{snapshot})

def SnapshotForCall(-x: I.Scenario, +snapshot: Snapshot) -> Type:
  {database(snapshot) == I.initial(x) : D.State}

def Received(x: I.Scenario, -wire: W.WireRequest) -> Type:
  match x:
    case I.Initialize{world, c, s, pi}: Empty
    case I.Serve{world, c, s, input}: W.Received(c, input, wire)

def InvalidWire(x: I.Scenario) -> Type:
  match x:
    case I.Initialize{world, c, s, pi}: Empty
    case I.Serve{world, c, s, input}: H.InvalidWire(c, input)

# These typed predicates never substitute an ordinary Encoding for full tag-7
# reception, nor use ordinary InputInvalid to reject a valid extension.
# A control error cannot mutate its own published pair or registry. Other
# selected read workers may publish a response meanwhile; global response
# equality across selection/error times would incorrectly freeze that pair.
def SameExecutionBase(-selected: Snapshot, -current: Snapshot) -> Type:
  L.E<{instance(current) == instance(selected) : String},
    L.E<{database(current) == database(selected) : D.State},
      {registry(current) == registry(selected) : List<&2, G.Entry>}>>

def NoOwnMutation(~a: Environment, -k: String, -x: I.Scenario) -> Type:
  @time: Nat -> @mode: Bool -> @mutation: Mutation -> @before: Snapshot -> @after: Snapshot ->
    observes(a, k, x, time, Mutated{mode, mutation, before, after}) -> Empty

def ControlErrorEffects(~a: Environment, -k: String, -x: I.Scenario, -time: Nat,
  -before: Snapshot, -after: Snapshot) -> Type:
  L.Disjunction<L.E<SameExecutionBase(before, after), NoOwnMutation(a, k, x)>,
    &handle: String -> Before(a, k, x, time, Mutated{True{}, Invalidate{handle}, before, after})>

def ControlCause(~a: Environment, -k: String, x: I.Scenario, -time: Nat, -status: S.Status) -> Type:
  match x:
    case I.Initialize{world, c, s, pi}: Empty
    case I.Serve{world, c, s, input}:
      &operation: W.Operation -> &raw: P.Request -> &before: Snapshot -> &after: Snapshot ->
        L.E<Received(x, W.Extension{operation, raw}),
          L.E<SelectedBefore(a, k, x, time, before),
            L.E<SnapshotForCall(x, before),
              L.E<Current(a, k, x, time, after),
                L.E<ControlErrorEffects(a, k, x, time, before, after),
                  H.ProtocolError(status, operation, core_environment(True{}, a), artifacts(a), k,
                    world, c, s, input, time, instance(before), registry(before), registry(after), raw)>>>>>

def RealFailure(~a: Environment, -k: String, x: I.Scenario, -time: Nat) -> Type:
  match x:
    case I.Initialize{world, c, s, pi}: Empty
    case I.Serve{world, c, s, input}:
      H.RealFailureBefore(core_environment(True{}, a), k, world, c, s, input, time)

def PreparedResponseCause(~a: Environment, -k: String, x: I.Scenario, -time: Nat, response: S.Response) -> Type:
  match response:
    case S.Response{S.Input{}, value}: L.Disjunction<InvalidWire(x), ControlCause(a, k, x, time, S.Input{})>
    case S.Response{S.Authentication{}, value}: ControlCause(a, k, x, time, S.Authentication{})
    case S.Response{S.Certificate{}, value}:
      &wire: W.WireRequest -> &context: D.Context ->
        L.E<Before(a, k, x, time, UniversalRejected{wire, context}), ControlCause(a, k, x, time, S.Certificate{})>
    case S.Response{S.Failure{}, value}: L.Disjunction<RealFailure(a, k, x, time), ControlCause(a, k, x, time, S.Failure{})>
    case S.Response{S.Limit{}, value}:
      L.Disjunction<ControlCause(a, k, x, time, S.Limit{}),
        &state: D.State -> I.ResponseOfProgram(core_environment(True{}, a), k, x, time, response, state)>
    case _:
      &state: D.State -> I.ResponseOfProgram(core_environment(True{}, a), k, x, time, response, state)

def PreparedBefore(~a: Environment, -k: String, -x: I.Scenario, -time: Nat, outcome: Outcome, -bytes: List<&2, U32>) -> Type:
  match outcome:
    case Transaction{response}: Before(a, k, x, time, PreparedKernel{I.Prepared{response, bytes}})
    case Receipt{receipt}: Before(a, k, x, time, ReceiptPrepared{receipt, bytes})

def ConcludedBefore(~a: Environment, -k: String, -x: I.Scenario, -time: Nat, outcome: Outcome,
  -state: D.State, -closes: Bool) -> Type:
  match outcome:
    case Transaction{response}: Before(a, k, x, time, PreparedKernel{I.Concluded{response, state, closes}})
    case Receipt{receipt}:
      &result: H.ControlResult -> &snapshot: Snapshot ->
        L.E<Before(a, k, x, time, ReceiptConcluded{receipt, result, snapshot, closes}),
          {database(snapshot) == state : D.State}>

def NoConclusionBefore(~a: Environment, -k: String, -x: I.Scenario, -time: Nat) -> Type:
  @outcome: Outcome -> @state: D.State -> @closes: Bool -> ConcludedBefore(a, k, x, time, outcome, state, closes) -> Empty

# A metadata success reports exactly this physical call's actual mutation.
# History completeness alone would also contain other calls' valid mutations.
def ReceiptMutationBefore(~a: Environment, -k: String, -x: I.Scenario, -time: Nat,
  -before: Snapshot, -after: Snapshot, receipt: W.Receipt) -> Type:
  match receipt:
    case W.PreparedReceipt{handle}:
      &entry: G.Entry -> L.E<{G.handle(entry) == handle : String},
        Before(a, k, x, time, Mutated{True{}, Register{entry}, before, after})>
    case W.InvalidatedReceipt{}:
      &handle: String -> Before(a, k, x, time, Mutated{True{}, Invalidate{handle}, before, after})

def ReceiptOutcome(~a: Environment, -k: String, x: I.Scenario, -time: Nat, -receipt: W.Receipt,
  -result: H.ControlResult, -snapshot: Snapshot) -> Type:
  match x:
    case I.Initialize{world, c, s, pi}: Empty
    case I.Serve{world, c, s, input}:
      &operation: W.Operation -> &raw: P.Request -> &before: Snapshot -> &bytes: List<&2, U32> ->
        L.E<SelectedBefore(a, k, x, time, before),
          L.E<SnapshotForCall(x, before),
            L.E<Current(a, k, x, time, snapshot),
              L.E<{H.response(result) == H.Metadata{receipt} : H.ControlResponse},
                L.E<{database(snapshot) == H.state(result) : D.State},
                  L.E<{registry(snapshot) == H.registry(result) : List<&2, G.Entry>},
                    L.E<PreparedBefore(a, k, x, time, Receipt{receipt}, bytes),
                      L.E<ReceiptMutationBefore(a, k, x, time, before, snapshot, receipt),
                        H.ControlOutcome(core_environment(True{}, a), artifacts(a), k, world, c, s, input,
                          time, instance(before), registry(before), operation, raw, result,
                          last_response(before), last_response(snapshot), bytes)>>>>>>>>

# No actual same-call checker event is invented for cached execution. The
# universal derivation is recovered from the CURRENT selected registry/history
# and specialized to the actual raw credential/context/arguments.
def ResolvedReady(~a: Environment, -k: String, x: I.Scenario, -time: Nat,
  -raw: P.Request, -entry: G.Entry, -logical: P.Request, -context: D.Context, -program: S.Program) -> Type:
  match x:
    case I.Initialize{world, c, s, pi}: Empty
    case I.Serve{world, c, s, input}:
      &selected: Snapshot -> &current: Snapshot ->
        L.E<SelectedBefore(a, k, x, time, selected),
          L.E<SnapshotForCall(x, selected),
            L.E<Current(a, k, x, time, current),
              L.E<SameExecutionBase(selected, current),
                L.E<Before(a, k, x, time, IdentityEstablished{W.Extension{W.Execute{}, raw}, Some{context}}),
                  L.E<{logical == H.resolved(raw, entry) : P.Request},
                    L.E<H.Ready(core_environment(True{}, a), artifacts(a), k, world, time, c, s, input,
                      instance(current), registry(current), raw, entry, context, program),
                      R.Certifies(c, I.code(logical), program, context, I.arguments(logical))>>>>>>>

def StartReady(~a: Environment, -k: String, -x: I.Scenario, -time: Nat,
  -logical: P.Request, -context: D.Context, -program: S.Program) -> Type:
  &raw: P.Request -> &entry: G.Entry -> Before(a, k, x, time, EntryResolved{raw, entry, logical, context, program})

def ReadModeEvidence(operation: W.Operation, -program: S.Program) -> Type:
  match operation:
    case W.Prepare{}: Unit
    case W.PrepareRead{}: RO.Program(program)
    case _: Empty

def PreparationAccepted(~a: Environment, -k: String, x: I.Scenario, -time: Nat,
  wire: W.WireRequest, -context: D.Context, -program: S.Program) -> Type:
  match x wire:
    case I.Serve{world, c, s, input} W.Extension{operation, raw}:
      &snapshot: Snapshot ->
        L.E<Current(a, k, x, time, snapshot),
          L.E<SnapshotForCall(x, snapshot),
            L.E<Before(a, k, x, time, IdentityEstablished{wire, Some{context}}),
              L.E<Received(x, wire),
                L.E<H.AdmissionDerivation(operation, core_environment(True{}, a), c, raw, program),
                  L.E<H.Universal(c, I.code(raw), program), ReadModeEvidence(operation, program)>>>>>>
    case _ _: Empty

# Typed mutation causes bind real before/after values and chronological events.
# They do not merely assert a final validity or registered-entry invariant.
def status(response: S.Response) -> S.Status:
  S.Response{status, value} = response
  status

def MutationCorrect(~a: Environment, -k: String, x: I.Scenario, -time: Nat,
  prepared: Bool, mutation: Mutation, +before: Snapshot, +after: Snapshot) -> Type:
  match x mutation:
    case I.Initialize{world, c, s, pi} _: Empty
    case I.Serve{world, c, s, input} Publish{response, bytes}:
      L.E<{instance(after) == instance(before) : String},
        L.E<{registry(after) == registry(before) : List<&2, G.Entry>},
          L.E<{last_response(after) == bytes : List<&2, U32>},
            L.E<{S.is_success(status(response)) == True{} : Bool},
              L.E<observes(a, k, x, time, core_fact(prepared, I.Published{database(after)})),
                I.Before(core_environment(prepared, a), k, x, time, I.Prepared{response, bytes})>>>>>
    case I.Serve{world, c, s, input} Register{entry}:
      &operation: W.Operation -> &raw: P.Request -> &context: D.Context -> &program: S.Program -> &bytes: List<&2, U32> ->
        L.E<{prepared == True{} : Bool},
          L.E<{database(after) == database(before) : D.State},
            L.E<{last_response(after) == last_response(before) : List<&2, U32>},
              L.E<{instance(after) == instance(before) : String},
                L.E<{registry(after) == Con{entry, registry(before)} : List<&2, G.Entry>},
                  L.E<Before(a, k, x, time, UniversalAccepted{W.Extension{operation, raw}, context, program}),
                    L.E<Before(a, k, x, time, ArtifactSealed{entry, program}),
                      L.E<PreparedBefore(a, k, x, time, Receipt{W.PreparedReceipt{G.handle(entry)}}, bytes),
                        H.RegistrationReady(core_environment(True{}, a), artifacts(a), k, world, time, c, s,
                          input, instance(before), registry(before), operation, raw, entry, context, program)>>>>>>>>
    case I.Serve{world, c, s, input} Invalidate{handle}:
      &raw: P.Request -> &entry: G.Entry -> &context: D.Context -> &bytes: List<&2, U32> ->
        L.E<{prepared == True{} : Bool},
          L.E<{handle == I.code(raw) : String},
            L.E<{database(after) == database(before) : D.State},
              L.E<{last_response(after) == last_response(before) : List<&2, U32>},
                L.E<{instance(after) == instance(before) : String},
                  L.E<{registry(after) == G.remove(instance(before), handle, registry(before)) : List<&2, G.Entry>},
                    L.E<Before(a, k, x, time, IdentityEstablished{W.Extension{W.Invalidate{}, raw}, Some{context}}),
                      L.E<PreparedBefore(a, k, x, time, Receipt{W.InvalidatedReceipt{}}, bytes),
                        H.InvalidationReady(c, s, input, instance(before), registry(before), raw, entry, context)>>>>>>>>

def HandleChosenCorrect(~a: Environment, -k: String, x: I.Scenario, -time: Nat, -handle: String) -> Type:
  &snapshot: Snapshot -> &wire: W.WireRequest -> &context: D.Context -> &program: S.Program ->
    L.E<Current(a, k, x, time, snapshot),
      L.E<Before(a, k, x, time, UniversalAccepted{wire, context, program}),
        L.E<H.HandleValid(handle), {G.lookup(instance(snapshot), handle, registry(snapshot)) == None{} : Maybe<&2, G.Entry>}>>>

def ReceiptAuthorization(~a: Environment, -k: String, x: I.Scenario, -time: Nat, receipt: W.Receipt) -> Type:
  match x receipt:
    case I.Initialize{world, c, s, pi} _: Empty
    case I.Serve{world, c, s, input} W.PreparedReceipt{handle}:
      &wire: W.WireRequest -> &context: D.Context -> &program: S.Program ->
        L.E<Before(a, k, x, time, UniversalAccepted{wire, context, program}),
          Before(a, k, x, time, HandleChosen{handle})>
    case I.Serve{world, c, s, input} W.InvalidatedReceipt{}:
      &snapshot: Snapshot -> &raw: P.Request -> &entry: G.Entry -> &context: D.Context ->
        L.E<Current(a, k, x, time, snapshot),
          L.E<SnapshotForCall(x, snapshot),
            L.E<Before(a, k, x, time, IdentityEstablished{W.Extension{W.Invalidate{}, raw}, Some{context}}),
              H.InvalidationReady(c, s, input, instance(snapshot), registry(snapshot), raw, entry, context)>>>

def SealingCorrect(~a: Environment, -k: String, x: I.Scenario, -time: Nat, -entry: G.Entry, -program: S.Program) -> Type:
  &snapshot: Snapshot -> &wire: W.WireRequest -> &context: D.Context -> &bytes: List<&2, U32> ->
    L.E<Current(a, k, x, time, snapshot),
      L.E<Before(a, k, x, time, UniversalAccepted{wire, context, program}),
        L.E<PreparedBefore(a, k, x, time, Receipt{W.PreparedReceipt{G.handle(entry)}}, bytes),
          H.Intact(artifacts(a), k, instance(snapshot), I.configuration(x), entry, program, x, time)>>>

def BootUnique(~a: Environment, -k: String, -x: I.Scenario, -time: Nat, -snapshot: Snapshot) -> Type:
  @y: I.Scenario -> @u: Nat -> @other: Snapshot ->
    {run_of(a, scenario_world(y)) == run_of(a, scenario_world(x)) : Nat} ->
    observes(a, k, y, u, Boot{other}) ->
      L.E<{u == time : Nat}, L.E<{y == x : I.Scenario}, {other == snapshot : Snapshot}>>

def SelectionUnique(~a: Environment, -k: String, -x: I.Scenario, -time: Nat, -snapshot: Snapshot) -> Type:
  @u: Nat -> @other: Snapshot -> observes(a, k, x, u, Selected{other}) ->
    L.E<{u == time : Nat}, {other == snapshot : Snapshot}>

# Ordinary clauses retain their exact targets. Rule2 additionally records the
# physical route; the compatibility proof projects this stronger conjunction.
# Parsed requests and client computation use the actual selected published
# snapshot. Reader prefetch/length events need not occur after selection.
def HasSelection(~a: Environment, -k: String, -x: I.Scenario, -time: Nat) -> Type:
  &snapshot: Snapshot -> L.E<SelectedBefore(a, k, x, time, snapshot), SnapshotForCall(x, snapshot)>

def SelectedForFact(~a: Environment, -k: String, -x: I.Scenario, -time: Nat, f: I.Fact) -> Type:
  match f:
    case I.ReceivedRequest{request}: HasSelection(a, k, x, time)
    case I.Authenticated{request, context}: HasSelection(a, k, x, time)
    case I.CertificateAccepted{request, context, program}: HasSelection(a, k, x, time)
    case I.CertificateRejected{request, context}: HasSelection(a, k, x, time)
    case I.ProgramStarted{request, context, program}: HasSelection(a, k, x, time)
    case I.Evaluated{request, context, program, trace}: HasSelection(a, k, x, time)
    case I.Operated{e, s, operation, result}: HasSelection(a, k, x, time)
    case _: Unit

def Rule1(~a: Environment, f: Fact, -k: String, x: I.Scenario, -time: Nat) -> Type:
  match f:
    case Ordinary{f}: L.E<K.Rule1(f, core_environment(False{}, a), k, x, time), SelectedForFact(a, k, x, time, f)>
    case PreparedKernel{I.ConfigurationInUse{c}}: {c == I.configuration(x) : S.Configuration}
    case Boot{snapshot}:
      match x:
        case I.Initialize{world, c, seed, pi}:
          L.E<{snapshot == Snapshot{instance(snapshot), seed, Nil{}, Nil{}} : Snapshot},
            L.E<Before(a, k, x, time, Ordinary{I.InstanceStarted{seed}}), BootUnique(a, k, x, time, snapshot)>>
        case _: Empty
    case Selected{snapshot}: L.E<SnapshotForCall(x, snapshot),
      L.E<Current(a, k, x, time, snapshot), SelectionUnique(a, k, x, time, snapshot)>>
    case _: Unit

def Rule2(~a: Environment, f: Fact, -k: String, x: I.Scenario, -time: Nat) -> Type:
  match f:
    case Ordinary{f}: L.E<OrdinaryPath(x), K.Rule2(f, core_environment(False{}, a), k, x, time)>
    case PreparedKernel{f}: L.E<PreparedPath(x), K.Rule2(f, core_environment(True{}, a), k, x, time)>
    case WireReceived{wire}: Received(x, wire)
    case EntryResolved{raw, entry, logical, context, program}: {logical == H.resolved(raw, entry) : P.Request}
    case _: Unit

def Rule3(~a: Environment, f: Fact, -k: String, x: I.Scenario, -time: Nat) -> Type:
  match f:
    case Ordinary{f}: K.Rule3(f, core_environment(False{}, a), k, x, time)
    case PreparedKernel{I.ProgramStarted{logical, context, program}}: StartReady(a, k, x, time, logical, context, program)
    case IdentityEstablished{wire, context}:
      &snapshot: Snapshot -> L.E<Current(a, k, x, time, snapshot),
        L.E<SnapshotForCall(x, snapshot),
          L.E<HasSelection(a, k, x, time),
            L.E<Before(a, k, x, time, WireReceived{wire}),
              {D.authenticate(database(snapshot), I.credential(W.raw(wire))) == context : Maybe<&2, D.Context>}>>>>
    case _: Unit

def Rule4(~a: Environment, f: Fact, -k: String, x: I.Scenario, -time: Nat) -> Type:
  match f:
    case Ordinary{f}: K.Rule4(f, core_environment(False{}, a), k, x, time)
    case PreparedKernel{I.ProgramStarted{logical, context, program}}: StartReady(a, k, x, time, logical, context, program)
    case UniversalAccepted{wire, context, program}: PreparationAccepted(a, k, x, time, wire, context, program)
    case UniversalRejected{wire, context}:
      match wire:
        case W.Extension{operation, raw}:
          L.E<Before(a, k, x, time, IdentityEstablished{wire, Some{context}}),
            L.E<H.PreparationOperation(operation), H.WithoutAdmission(operation, core_environment(True{}, a), I.configuration(x), raw)>>
        case _: Empty
    case EntryResolved{raw, entry, logical, context, program}: ResolvedReady(a, k, x, time, raw, entry, logical, context, program)
    case HandleChosen{handle}: HandleChosenCorrect(a, k, x, time, handle)
    case ReceiptPrepared{receipt, bytes}: ReceiptAuthorization(a, k, x, time, receipt)
    case ArtifactSealed{entry, program}: SealingCorrect(a, k, x, time, entry, program)
    case _: Unit

# Prepared kernel facts cannot impersonate ordinary reception/authentication or
# a fresh checker invocation. Those have the explicit full-wire events above.
def PreparedCoreAllowed(f: I.Fact) -> Type:
  match f:
    case I.ReceivedRequest{r}: Empty
    case I.Authenticated{r, context}: Empty
    case I.CertificateAccepted{r, context, program}: Empty
    case I.CertificateRejected{r, context}: Empty
    case I.InstanceStarted{state}: Empty
    case I.ProofInitialAccepts{}: Empty
    case I.InitializationRefused{status}: Empty
    case _: Unit

def ClientEvent(f: I.Fact) -> Type:
  match f:
    case I.ProgramStarted{r, context, program}: Unit
    case I.Evaluated{r, context, program, trace}: Unit
    case I.Operated{e, s, operation, result}: Unit
    case _: Empty

def Rule5(~a: Environment, f: Fact, -k: String, x: I.Scenario, -time: Nat) -> Type:
  match f:
    case Ordinary{f}: K.Rule5(f, core_environment(False{}, a), k, x, time)
    case PreparedKernel{f}:
      L.E<PreparedCoreAllowed(f),
        L.E<K.Rule5(f, core_environment(True{}, a), k, x, time), ClientEvent(f) -> NoConclusionBefore(a, k, x, time)>>
    case _: Unit

def PublicationCoupled(~a: Environment, -k: String, -x: I.Scenario, -time: Nat,
  -mode: Bool, f: I.Fact) -> Type:
  match f:
    case I.Published{state}:
      &response: S.Response -> &bytes: List<&2, U32> -> &before: Snapshot -> &after: Snapshot ->
        L.E<observes(a, k, x, time, Mutated{mode, Publish{response, bytes}, before, after}),
          {database(after) == state : D.State}>
    case _: Unit

def MutationUnique(~a: Environment, -k: String, -x: I.Scenario, -time: Nat,
  -mode: Bool, -mutation: Mutation, -before: Snapshot, -after: Snapshot) -> Type:
  @u: Nat -> @other_mode: Bool -> @other_mutation: Mutation -> @other_before: Snapshot -> @other_after: Snapshot ->
    observes(a, k, x, u, Mutated{other_mode, other_mutation, other_before, other_after}) ->
      L.E<{u == time : Nat}, L.E<{other_mode == mode : Bool}, L.E<{other_mutation == mutation : Mutation},
        L.E<{other_before == before : Snapshot}, {other_after == after : Snapshot}>>>>

def Rule6(~a: Environment, f: Fact, -k: String, x: I.Scenario, -time: Nat) -> Type:
  match f:
    case Ordinary{f}: L.E<K.Rule6(f, core_environment(False{}, a), k, x, time), PublicationCoupled(a, k, x, time, False{}, f)>
    case PreparedKernel{I.NextCall{previous, next}}:
      L.E<{next == previous : D.State}, &outcome: Outcome -> &closes: Bool -> ConcludedBefore(a, k, x, time, outcome, previous, closes)>
    case PreparedKernel{f}: L.E<K.Rule6(f, core_environment(True{}, a), k, x, time), PublicationCoupled(a, k, x, time, True{}, f)>
    case Mutated{mode, mutation, before, after}:
      L.E<Current(a, k, x, time, before),
        L.E<SnapshotForCall(x, before),
          L.E<MutationCorrect(a, k, x, time, mode, mutation, before, after),
            MutationUnique(a, k, x, time, mode, mutation, before, after)>>>
    case ReceiptConcluded{receipt, result, snapshot, closes}:
      L.E<{database(snapshot) == I.initial(x) : D.State},
        K.NonePublication(core_environment(True{}, a), k, x)>
    case _: Unit

# Delivery uniqueness is shared by transaction and metadata outcomes. The
# interrupted bytes must be a real written prefix of the exact prepared frame.
def ConclusionAt(~a: Environment, k: String, x: I.Scenario, time: Nat, outcome: Outcome,
  state: D.State, closes: Bool) -> Type:
  match outcome:
    case Transaction{response}: observes(a, k, x, time, PreparedKernel{I.Concluded{response, state, closes}})
    case Receipt{receipt}:
      &result: H.ControlResult -> &snapshot: Snapshot ->
        L.E<observes(a, k, x, time, ReceiptConcluded{receipt, result, snapshot, closes}),
          {database(snapshot) == state : D.State}>

def ConclusionUnique(~a: Environment, -k: String, -x: I.Scenario, -time: Nat,
  -outcome: Outcome, -state: D.State, -closing: Bool) -> Type:
  @u: Nat -> @other: Outcome -> @s: D.State -> @closes: Bool ->
    ConclusionAt(a, k, x, u, other, s, closes) ->
      L.E<{u == time : Nat}, L.E<{other == outcome : Outcome},
        L.E<{s == state : D.State}, {closes == closing : Bool}>>>

# Closing stops new dispatches for this service lifetime. Already selected read
# workers may still finish/clean up; no false post-close absence of their effects
# is imposed. Prefetching bytes is not a selected transaction.
def NoDispatchAfterClose(~a: Environment, -k: String, -x: I.Scenario, -time: Nat) -> Type:
  @y: I.Scenario -> @u: Nat -> @snapshot: Snapshot ->
    {run_of(a, scenario_world(y)) == run_of(a, scenario_world(x)) : Nat} ->
    {Nat.is_lt(time, u) == True{} : Bool} ->
    observes(a, k, y, u, Selected{snapshot}) -> Empty

def ClosureCoupled(~a: Environment, -k: String, -x: I.Scenario, -time: Nat, f: I.Fact) -> Type:
  match f:
    case I.ClosedChannel{}: NoDispatchAfterClose(a, k, x, time)
    case _: Unit

def Rule7(~a: Environment, f: Fact, k: String, x: I.Scenario, time: Nat) -> Type:
  match f:
    case Ordinary{f}: L.E<K.Rule7(f, core_environment(False{}, a), k, x, time), ClosureCoupled(a, k, x, time, f)>
    case PreparedKernel{I.Prepared{response, bytes}}:
      L.E<I.ErrorFixed(response), L.E<P.Message(S.response_value(response), bytes),
        L.E<{R.fits(R.limit_response(S.limits(I.configuration(x))), S.response_value(response)) == True{} : Bool},
          PreparedResponseCause(a, k, x, time, response)>>>
    case PreparedKernel{I.Concluded{response, state, closes}}:
      L.E<&bytes: List<&2, U32> -> PreparedBefore(a, k, x, time, Transaction{response}, bytes),
        L.E<L.E<K.ClosingAllowed(core_environment(True{}, a), k, x, time, closes),
          K.CloseEventually(closes, core_environment(True{}, a), k, x)>,
          ConclusionUnique(a, k, x, time, Transaction{response}, state, closes)>>
    case ReceiptPrepared{receipt, bytes}:
      L.E<W.ReceiptEncoding(receipt, bytes),
        {R.fits(R.limit_response(S.limits(I.configuration(x))), W.receipt_value(receipt)) == True{} : Bool}>
    case ReceiptConcluded{receipt, result, snapshot, closes}:
      L.E<ReceiptOutcome(a, k, x, time, receipt, result, snapshot),
        L.E<L.E<K.ClosingAllowed(core_environment(True{}, a), k, x, time, closes), K.CloseEventually(closes, core_environment(True{}, a), k, x)>,
          ConclusionUnique(a, k, x, time, Receipt{receipt}, database(snapshot), closes)>>
    case PreparedKernel{I.DeliveredEverything{bytes}}:
      &outcome: Outcome -> &state: D.State -> &closes: Bool ->
        L.E<ConcludedBefore(a, k, x, time, outcome, state, closes),
          L.E<PreparedBefore(a, k, x, time, outcome, bytes),
            K.DeliveryCompleteUnique(core_environment(True{}, a), k, x, time, bytes)>>
    case PreparedKernel{I.DeliveryInterrupted{prefix}}:
      &outcome: Outcome -> &state: D.State -> &closes: Bool -> &bytes: List<&2, U32> ->
        L.E<ConcludedBefore(a, k, x, time, outcome, state, closes),
          L.E<PreparedBefore(a, k, x, time, outcome, bytes),
            L.E<L.Prefix(U32, prefix, bytes),
              L.E<K.DeliveryInterruptedUnique(core_environment(True{}, a), k, x, time, prefix),
                I.FailureDeliveryReal(core_environment(True{}, a), k, x, time)>>>>
    case PreparedKernel{I.ClosedChannel{}}:
      L.E<L.Disjunction<K.WithoutResponseExpected(x),
        L.Disjunction<K.FailureFatalPrevious(core_environment(True{}, a), k, x, time),
          L.Disjunction<&outcome: Outcome -> &state: D.State -> ConcludedBefore(a, k, x, time, outcome, state, True{}),
            &prefix: List<&2, U32> -> Before(a, k, x, time, PreparedKernel{I.DeliveryInterrupted{prefix}})>>>,
        NoDispatchAfterClose(a, k, x, time)>
    case PreparedKernel{I.FailedEnvironment{stage, id, fatal}}:
      I.FailureReal(core_environment(True{}, a), k, x, time, stage, id, fatal)
    case _: Unit

# No program/metadata success is supplied as an availability premise. These are
# the required eventual events, not fields of a primitive IO-return contract.
def PreparedEnd(~a: Environment, -k: String, -x: I.Scenario) -> Type:
  L.Disjunction<L.E<K.WithoutResponseExpected(x), Eventually(a, k, x, PreparedKernel{I.ClosedChannel{}})>,
    &outcome: Outcome -> &state: D.State -> &closes: Bool -> &bytes: List<&2, U32> ->
      &tc: Nat -> &td: Nat ->
        L.E<ConclusionAt(a, k, x, tc, outcome, state, closes),
          L.E<{Nat.is_lt(tc, td) == True{} : Bool},
            observes(a, k, x, td, PreparedKernel{I.DeliveredEverything{bytes}})>>>

def PreparationProgress(~a: Environment, -k: String, -x: I.Scenario, -snapshot: Snapshot,
  operation: W.Operation, -raw: P.Request, -context: D.Context, -program: S.Program) -> Type:
  H.PreparationOperation(operation) -> Received(x, W.Extension{operation, raw}) ->
  H.Authenticated(database(snapshot), raw, context) ->
  H.AdmissionDerivation(operation, core_environment(True{}, a), I.configuration(x), raw, program) ->
    Eventually(a, k, x, UniversalAccepted{W.Extension{operation, raw}, context, program})

def ExecutionProgress(~a: Environment, -k: String, x: I.Scenario, -selected: Nat, -snapshot: Snapshot,
  -raw: P.Request, -entry: G.Entry, -context: D.Context, -program: S.Program) -> Type:
  match x:
    case I.Initialize{world, c, s, pi}: Empty
    case I.Serve{world, c, s, input}:
      Received(x, W.Extension{W.Execute{}, raw}) -> H.Authenticated(s, raw, context) ->
      H.HandleFields(raw, entry) -> {G.lookup(instance(snapshot), I.code(raw), registry(snapshot)) == Some{entry} : Maybe<&2, G.Entry>} ->
      H.ModeCertificateValid(core_environment(True{}, a), c, entry, program) ->
      H.Intact(artifacts(a), k, instance(snapshot), c, entry, program, x, selected) ->
        L.E<Eventually(a, k, x, EntryResolved{raw, entry, H.resolved(raw, entry), context, program}),
          Eventually(a, k, x, PreparedKernel{I.ProgramStarted{H.resolved(raw, entry), context, program}})>

def PreparedProgress(~a: Environment, -k: String, x: I.Scenario) -> Type:
  match x:
    case I.Initialize{world, c, s, pi}: Unit
    case I.Serve{world, c, s, input}:
      PreparedPath(x) -> I.ConfigurationValid(core_environment(True{}, a), c) -> R.Valid(c, s) ->
      X.ReceptionValid(input) -> Processable(a, x) ->
        L.E<PreparedEnd(a, k, x),
          &selected: Nat -> &snapshot: Snapshot ->
            L.E<observes(a, k, x, selected, Selected{snapshot}),
              L.E<@operation: W.Operation -> @raw: P.Request -> @context: D.Context -> @program: S.Program ->
                  PreparationProgress(a, k, x, snapshot, operation, raw, context, program),
                @raw: P.Request -> @entry: G.Entry -> @context: D.Context -> @program: S.Program ->
                  ExecutionProgress(a, k, x, selected, snapshot, raw, entry, context, program)>>>

def Progress(~a: Environment, -k: String, -x: I.Scenario) -> Type:
  L.E<(OrdinaryPath(x) -> K.Progress(x, core_environment(False{}, a), k)), PreparedProgress(a, k, x)>

def Law1(~a: Environment, -k: String) -> Type:
  @x: I.Scenario -> @time: Nat -> @f: Fact -> observes(a, k, x, time, f) -> Rule1(a, f, k, x, time)
def Law2(~a: Environment, -k: String) -> Type:
  @x: I.Scenario -> @time: Nat -> @f: Fact -> observes(a, k, x, time, f) -> Rule2(a, f, k, x, time)
def Law3(~a: Environment, -k: String) -> Type:
  @x: I.Scenario -> @time: Nat -> @f: Fact -> observes(a, k, x, time, f) -> Rule3(a, f, k, x, time)
def Law4(~a: Environment, -k: String) -> Type:
  @x: I.Scenario -> @time: Nat -> @f: Fact -> observes(a, k, x, time, f) -> Rule4(a, f, k, x, time)
def Law5(~a: Environment, -k: String) -> Type:
  @x: I.Scenario -> @time: Nat -> @f: Fact -> observes(a, k, x, time, f) -> Rule5(a, f, k, x, time)
def Law6(~a: Environment, -k: String) -> Type:
  @x: I.Scenario -> @time: Nat -> @f: Fact -> observes(a, k, x, time, f) -> Rule6(a, f, k, x, time)
def Law7(~a: Environment, -k: String) -> Type:
  @x: I.Scenario -> @time: Nat -> @f: Fact -> observes(a, k, x, time, f) -> Rule7(a, f, k, x, time)
def Law8(~a: Environment, -k: String) -> Type:
  @x: I.Scenario -> Progress(a, k, x)

def Contract(~a: Environment, -k: String) -> Type:
  L.E<Law1(a, k), L.E<Law2(a, k), L.E<Law3(a, k), L.E<Law4(a, k),
    L.E<Law5(a, k), L.E<Law6(a, k), L.E<Law7(a, k), Law8(a, k)>>>>>>>
