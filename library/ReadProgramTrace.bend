# Closed selection uses the actual engine, not only a supplied Return stream.
# Successful-prefix facts are separate per-operation D.operate equations.
import Base
import ./QueryReadTrace.bend as R
import ./QuerySelectionModel.bend as M
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Query.bend as Q
import ./ReadProgram.bend as P
import ./Laws.bend as G
import ../src/Termination.bend as T

def response(selection: Q.Selection) -> S.Response:
  match selection:
    case Q.Selected{record}: S.Response{S.Success{},record}
    case Q.MissingRow{}: S.Response{S.Success{},D.VAbsent{}}
    case Q.InvalidFields{}: S.Response{S.Refusal{},D.VText{"invalid fields"}}
    case Q.UnexpectedReturn{}: S.Response{S.Refusal{},D.VText{"unexpected selection return"}}

law closed_selection_response_is_exact_for_every_selection_variant:
  for +selection: Q.Selection
  for -schema: D.Schema
  for -state: D.State
  for -history: List<&2,S.OperationEvent>
  {T.observe(1n,P.selected(selection),schema,state,history) == S.Final{state,history,response(selection)} : S.Trace}
def closed_selection_response_is_exact_for_every_selection_variant(selection,schema,state,history):
  match selection:
    case Q.Selected{record}: {==}
    case Q.MissingRow{}: {==}
    case Q.InvalidFields{}: {==}
    case Q.UnexpectedReturn{}: {==}

law actual_validated_read_program_retains_exact_read_events_and_final_response:
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
  for valid: {Q.fields_valid(names) == True{} : Bool}
  for observed: R.ObservedReads(~Env,~observation,env,names,index,schema,state,collection,key)
  {T.observe(G.depth(names,1n),P.select(collection,key,names),schema,state,history) == S.Final{state,R.append_events(R.events(~Env,~observation,env,names,index,collection,key),history),response(M.expected(~Env,~R.returned(~Env,~observation),env,index,names))} : S.Trace}
def actual_validated_read_program_retains_exact_read_events_and_final_response(Env,observation,env,names,index,schema,state,collection,key,history,valid,observed):
  %Equal.sym(Bool,Q.fields_valid(names),True{},valid) :
    {T.observe(G.depth(names,1n),Q.select_valid(_,collection,key,names,P.selected),schema,state,history) == S.Final{state,R.append_events(R.events(~Env,~observation,env,names,index,collection,key),history),response(M.expected(~Env,~R.returned(~Env,~observation),env,index,names))} : S.Trace}
  Equal.trans(S.Trace,T.observe(G.depth(names,1n),Q.read_fields(collection,key,names,P.selected),schema,state,history),T.observe(1n,P.selected(M.expected(~Env,~R.returned(~Env,~observation),env,index,names)),schema,state,R.append_events(R.events(~Env,~observation,env,names,index,collection,key),history)),S.Final{state,R.append_events(R.events(~Env,~observation,env,names,index,collection,key),history),response(M.expected(~Env,~R.returned(~Env,~observation),env,index,names))},
    R.actual_observed_read_prefix_retains_exact_events_then_hands_off_exact_selection(~Env,~observation,env,names,index,1n,schema,state,collection,key,P.selected,history,observed),closed_selection_response_is_exact_for_every_selection_variant(M.expected(~Env,~R.returned(~Env,~observation),env,index,names),schema,state,R.append_events(R.events(~Env,~observation,env,names,index,collection,key),history)))

law invalid_field_selection_refuses_before_any_real_operation:
  for +names: List<&2,String>
  for -schema: D.Schema
  for -state: D.State
  for -collection: D.Collection
  for -key: String
  for -history: List<&2,S.OperationEvent>
  for invalid: {Q.fields_valid(names) == False{} : Bool}
  {T.observe(1n,P.select(collection,key,names),schema,state,history) == S.Final{state,history,S.Response{S.Refusal{},D.VText{"invalid fields"}}} : S.Trace}
def invalid_field_selection_refuses_before_any_real_operation(names,schema,state,collection,key,history,invalid):
  %Equal.sym(Bool,Q.fields_valid(names),False{},invalid) :
    {T.observe(1n,Q.select_valid(_,collection,key,names,P.selected),schema,state,history) == S.Final{state,history,S.Response{S.Refusal{},D.VText{"invalid fields"}}} : S.Trace}
  {==}

# No existence or Unicode precondition is appropriate for an EMPTY selection.
law empty_selected_record_finishes_with_zero_database_events_for_every_state:
  for -schema: D.Schema
  for -state: D.State
  for -collection: D.Collection
  for -key: String
  for -history: List<&2,S.OperationEvent>
  {T.observe(1n,P.select(collection,key,Nil{}),schema,state,history) == S.Final{state,history,S.Response{S.Success{},D.VRecordEmpty{}}} : S.Trace}
def empty_selected_record_finishes_with_zero_database_events_for_every_state(schema,state,collection,key,history): {==}
