# Canonical selected records follow from the REAL source-state invariant,
# validation of requested names, and each actual observed read. No completed
# result, payload-validity, or record-validity premise is assumed here.
import Base
import ./ReadValueValidity.bend as V
import ./QuerySelectionModel.bend as M
import ./QueryReadTrace.bend as R
import ./ReadProgramTrace.bend as Closed
import ./ValueScalarProofs.bend as Scalar
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Logic.bend as L
import ./Query.bend as Q
import ./ReadProgram.bend as P
import ./Laws.bend as G
import ../src/Termination.bend as T

def observation_payload_is_valid(+observation: D.Observation,valid: V.ObservationValue(observation)) -> {D.value_valid(M.payload(S.Datum{observation})) == True{} : Bool}:
  match observation:
    case D.Cell{value}: valid
    case D.RowAbsent{}: {==}
    case D.Keys{keys}: {==}
    case D.Count{count}: {==}
    case D.Existence{exists}: {==}

def structured_reads_supply_valid_payloads(~Env: Data,~observation: Env -> Nat -> D.Observation,+env: Env,+names: List<&2,String>,+index: Nat,+schema: D.Schema,+state: D.State,+collection: D.Collection,+key: String,+structured: {D.structure(schema,state) == True{} : Bool},observed: R.ObservedReads(~Env,~observation,env,names,index,schema,state,collection,key)) -> M.PayloadsValid(~Env,~R.returned(~Env,~observation),env,names,index):
  match names observed:
    case Nil{} Unit{}: Unit{}
    case Con{+name,+tail} Scalar.Both{head,rest}:
      Scalar.Both{observation_payload_is_valid(observation(env,index),V.actual_observed_read_from_a_structured_state_has_a_valid_cell_payload(schema,state,collection,key,name,observation(env,index),structured,head)),structured_reads_supply_valid_payloads(~Env,~observation,env,tail,1n+index,schema,state,collection,key,structured,rest)}

def CanonicalSelection(selection: Q.Selection) -> Data:
  match selection:
    case Q.Selected{record}: {D.value_valid(record) == True{} : Bool}
    case Q.MissingRow{}: Unit
    case Q.InvalidFields{}: Unit
    case Q.UnexpectedReturn{}: Unit

def rendering_a_valid_record_is_canonical(problem: M.Problem,+record: D.Value,valid: {D.value_valid(record) == True{} : Bool}) -> CanonicalSelection(M.render(problem,record)):
  match problem:
    case M.Clear{}: valid
    case M.Absent{}: Unit{}
    case M.Unexpected{}: Unit{}

law actual_observed_validated_selection_of_a_structured_state_is_canonical:
  for ~Env: Data
  for ~observation: Env -> Nat -> D.Observation
  for +env: Env
  for +names: List<&2,String>
  for +index: Nat
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +key: String
  for valid_names: {Q.fields_valid(names) == True{} : Bool}
  for +structured: {D.structure(schema,state) == True{} : Bool}
  for observed: R.ObservedReads(~Env,~observation,env,names,index,schema,state,collection,key)
  CanonicalSelection(M.expected(~Env,~R.returned(~Env,~observation),env,index,names))
def actual_observed_validated_selection_of_a_structured_state_is_canonical(Env,observation,env,names,index,schema,state,collection,key,valid_names,structured,observed):
  rendering_a_valid_record_is_canonical(M.problem(~Env,~R.returned(~Env,~observation),env,names,index),M.record(~Env,~R.returned(~Env,~observation),env,names,index),M.valid_names_and_returned_payloads_materialize_an_exact_canonical_record(~Env,~R.returned(~Env,~observation),env,names,index,valid_names,structured_reads_supply_valid_payloads(~Env,~observation,env,names,index,schema,state,collection,key,structured,observed)))

law closed_real_selection_has_its_exact_canonical_result_and_complete_read_history:
  for ~Env: Data
  for ~observation: Env -> Nat -> D.Observation
  for +env: Env
  for +names: List<&2,String>
  for +index: Nat
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +key: String
  for +history: List<&2,S.OperationEvent>
  for +valid_names: {Q.fields_valid(names) == True{} : Bool}
  for +structured: {D.structure(schema,state) == True{} : Bool}
  for +observed: R.ObservedReads(~Env,~observation,env,names,index,schema,state,collection,key)
  L.E<{T.observe(G.depth(names,1n),P.select(collection,key,names),schema,state,history) == S.Final{state,R.append_events(R.events(~Env,~observation,env,names,index,collection,key),history),Closed.response(M.expected(~Env,~R.returned(~Env,~observation),env,index,names))} : S.Trace},CanonicalSelection(M.expected(~Env,~R.returned(~Env,~observation),env,index,names))>
def closed_real_selection_has_its_exact_canonical_result_and_complete_read_history(Env,observation,env,names,index,schema,state,collection,key,history,valid_names,structured,observed):
  L.Both{Closed.actual_validated_read_program_retains_exact_read_events_and_final_response(~Env,~observation,env,names,index,schema,state,collection,key,history,valid_names,observed),actual_observed_validated_selection_of_a_structured_state_is_canonical(~Env,~observation,env,names,index,schema,state,collection,key,valid_names,structured,observed)}
