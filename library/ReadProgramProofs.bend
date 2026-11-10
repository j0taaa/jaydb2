# Total closed public ReadProgram.select behavior, forall input DATA with no
# read-outcome/output/invariant premise. Invalid fields make no read; valid
# fields use the exact source plan including the FIRST real data failure.
import Base
import ./QueryReadPlan.bend as M
import ./QueryReadPlanProofs.bend as R
import ./QueryReadTrace.bend as History
import ./QuerySelectionModel.bend as Meaning
import ./ReadProgramTrace.bend as Closed
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Query.bend as Q
import ./ReadProgram.bend as P
import ./Laws.bend as G
import ../src/Termination.bend as T

def depth(valid: Bool,names: List<&2,String>) -> Nat:
  match valid:
    case True{}: G.depth(names,1n)
    case False{}: 1n

def close(plan: M.Plan,+state: D.State,history: List<&2,S.OperationEvent>) -> S.Trace:
  match plan:
    case M.ReadsReady{problem,record,events}: S.Final{state,History.append_events(events,history),Closed.response(Meaning.render(problem,record))}
    case M.ReadsFailed{events}: S.Final{state,History.append_events(events,history),S.Response{S.DataError{},D.VAbsent{}}}

def result(valid: Bool,plan: M.Plan,+state: D.State,history: List<&2,S.OperationEvent>) -> S.Trace:
  match valid:
    case True{}: close(plan,state,history)
    case False{}: S.Final{state,history,S.Response{S.Refusal{},D.VText{"invalid fields"}}}

law closing_a_total_source_plan_has_exactly_its_complete_response_and_history:
  for +plan: M.Plan
  for +schema: D.Schema
  for +state: D.State
  for +history: List<&2,S.OperationEvent>
  {R.finish(plan,1n,schema,state,P.selected,history) == close(plan,state,history) : S.Trace}
def closing_a_total_source_plan_has_exactly_its_complete_response_and_history(plan,schema,state,history):
  match plan:
    case M.ReadsReady{problem,record,events}: Closed.closed_selection_response_is_exact_for_every_selection_variant(Meaning.render(problem,record),schema,state,History.append_events(events,history))
    case M.ReadsFailed{events}: {==}

def valid_case(valid: Bool,+schema: D.Schema,+state: D.State,+collection: D.Collection,+key: String,+names: List<&2,String>,+history: List<&2,S.OperationEvent>) ->
  {T.observe(depth(valid,names),Q.select_valid(valid,collection,key,names,P.selected),schema,state,history) == result(valid,M.plan(schema,state,collection,key,names),state,history) : S.Trace}:
  match valid:
    case True{}:
      Equal.trans(S.Trace,T.observe(G.depth(names,1n),Q.read_fields(collection,key,names,P.selected),schema,state,history),R.finish(M.plan(schema,state,collection,key,names),1n,schema,state,P.selected,history),close(M.plan(schema,state,collection,key,names),state,history),R.actual_read_fields_has_total_exact_source_state_behavior(schema,state,collection,key,names,1n,P.selected,history),closing_a_total_source_plan_has_exactly_its_complete_response_and_history(M.plan(schema,state,collection,key,names),schema,state,history))
    case False{}: {==}

law actual_public_read_program_select_has_total_exact_behavior_for_every_input:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +key: String
  for +names: List<&2,String>
  for +history: List<&2,S.OperationEvent>
  {T.observe(depth(Q.fields_valid(names),names),P.select(collection,key,names),schema,state,history) == result(Q.fields_valid(names),M.plan(schema,state,collection,key,names),state,history) : S.Trace}
def actual_public_read_program_select_has_total_exact_behavior_for_every_input(schema,state,collection,key,names,history):
  valid_case(Q.fields_valid(names),schema,state,collection,key,names,history)
