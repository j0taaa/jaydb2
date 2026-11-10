# TOTAL actual-engine theorem: all input states/schemas, names, arbitrary
# continuation, and remaining depth. No assumed read output, successful-prefix
# invariant, completed trace, or continuation behavior is a public premise.
import Base
import ./QueryReadPlan.bend as M
import ./QuerySelectionModel.bend as Meaning
import ./QueryReadTrace.bend as R
import ./ReadOperationProofs.bend as Op
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Query.bend as Q
import ./Proofs.bend as Event
import ./Laws.bend as G
import ../proof/Foundations.bend as F
import ../src/Termination.bend as T

def finish(plan: M.Plan,+remaining: Nat,+schema: D.Schema,+state: D.State,done: Q.Selection -> S.Action,history: List<&2,S.OperationEvent>) -> S.Trace:
  match plan:
    case M.ReadsReady{problem,record,events}: T.observe(remaining,done(Meaning.render(problem,record)),schema,state,R.append_events(events,history))
    case M.ReadsFailed{events}: S.Final{state,R.append_events(events,history),S.Response{S.DataError{},D.VAbsent{}}}

law observed_source_events_and_independent_selection_compose_exactly:
  for +tail: M.Plan
  for +op: D.Operation
  for +name: String
  for +observation: D.Observation
  for +remaining: Nat
  for +schema: D.Schema
  for +state: D.State
  for -done: Q.Selection -> S.Action
  for +history: List<&2,S.OperationEvent>
  {finish(tail,remaining,schema,state,result => done(Q.combine(name,S.Datum{observation},result)),S.append(history,S.OperationEvent{op,S.Reading{observation}})) == finish(M.observed(op,name,observation,tail),remaining,schema,state,done,history) : S.Trace}
def observed_source_events_and_independent_selection_compose_exactly(tail,op,name,observation,remaining,schema,state,done,history):
  match tail:
    case M.ReadsReady{+problem,+record,+events}:
      Equal.cong(Q.Selection,S.Trace,result => T.observe(remaining,done(result),schema,state,R.append_events(events,S.append(history,S.OperationEvent{op,S.Reading{observation}}))),Q.combine(name,S.Datum{observation},Meaning.render(problem,record)),Meaning.render(Meaning.head_problem(S.Datum{observation},problem),D.VRecord{name,Meaning.payload(S.Datum{observation}),record}),Equal.sym(Q.Selection,Meaning.render(Meaning.head_problem(S.Datum{observation},problem),D.VRecord{name,Meaning.payload(S.Datum{observation}),record}),Q.combine(name,S.Datum{observation},Meaning.render(problem,record)),Meaning.independently_classified_and_materialized_selection_obeys_the_actual_combiner(name,S.Datum{observation},problem,record)))
    case M.ReadsFailed{events}: {==}

def result_case(+result: D.ResultOp,+schema: D.Schema,+state: D.State,+collection: D.Collection,+key: String,+name: String,+tail: List<&2,String>,+remaining: Nat,-done: Q.Selection -> S.Action,+history: List<&2,S.OperationEvent>,actual: {D.operate(schema,state,D.ReadCell{collection,key,name}) == result : D.ResultOp},kind: Op.ResultKind(Op.Cell{},result),recursive: @-next: (Q.Selection -> S.Action) -> @+earlier: List<&2,S.OperationEvent> -> {T.observe(G.depth(tail,remaining),Q.read_fields(collection,key,tail,next),schema,state,earlier) == finish(M.plan(schema,state,collection,key,tail),remaining,schema,state,next,earlier) : S.Trace}) ->
  {T.observe(G.depth(Con{name,tail},remaining),Q.read_fields(collection,key,Con{name,tail},done),schema,state,history) == finish(M.extend(D.ReadCell{collection,key,name},name,result,M.plan(schema,state,collection,key,tail)),remaining,schema,state,done,history) : S.Trace}:
  match result:
    case D.FailureData{}:
      Op.actual_data_failure_retains_its_event_and_finishes_without_a_return_callback(G.depth(tail,remaining),schema,state,D.ReadCell{collection,key,name},Q.received(name,done,next => Q.read_fields(collection,key,tail,next)),history,actual)
    case D.Observed{+observation}:
      Equal.trans(S.Trace,T.observe(G.depth(Con{name,tail},remaining),Q.read_fields(collection,key,Con{name,tail},done),schema,state,history),T.observe(G.depth(tail,remaining),Q.read_fields(collection,key,tail,result => done(Q.combine(name,S.Datum{observation},result))),schema,state,S.append(history,S.OperationEvent{D.ReadCell{collection,key,name},S.Reading{observation}})),finish(M.observed(D.ReadCell{collection,key,name},name,observation,M.plan(schema,state,collection,key,tail)),remaining,schema,state,done,history),Event.read_continuation(G.depth(tail,remaining),schema,state,D.ReadCell{collection,key,name},observation,Q.received(name,done,next => Q.read_fields(collection,key,tail,next)),history,actual),
        Equal.trans(S.Trace,T.observe(G.depth(tail,remaining),Q.read_fields(collection,key,tail,result => done(Q.combine(name,S.Datum{observation},result))),schema,state,S.append(history,S.OperationEvent{D.ReadCell{collection,key,name},S.Reading{observation}})),finish(M.plan(schema,state,collection,key,tail),remaining,schema,state,result => done(Q.combine(name,S.Datum{observation},result)),S.append(history,S.OperationEvent{D.ReadCell{collection,key,name},S.Reading{observation}})),finish(M.observed(D.ReadCell{collection,key,name},name,observation,M.plan(schema,state,collection,key,tail)),remaining,schema,state,done,history),recursive(result => done(Q.combine(name,S.Datum{observation},result)),S.append(history,S.OperationEvent{D.ReadCell{collection,key,name},S.Reading{observation}})),observed_source_events_and_independent_selection_compose_exactly(M.plan(schema,state,collection,key,tail),D.ReadCell{collection,key,name},name,observation,remaining,schema,state,done,history)))
    case D.Changed{changed}:
      F.absurd_boolean({T.observe(G.depth(Con{name,tail},remaining),Q.read_fields(collection,key,Con{name,tail},done),schema,state,history) == finish(M.extend(D.ReadCell{collection,key,name},name,D.Changed{changed},M.plan(schema,state,collection,key,tail)),remaining,schema,state,done,history) : S.Trace},kind)

law actual_read_fields_has_total_exact_source_state_behavior:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +key: String
  for +names: List<&2,String>
  for +remaining: Nat
  for -done: Q.Selection -> S.Action
  for +history: List<&2,S.OperationEvent>
  {T.observe(G.depth(names,remaining),Q.read_fields(collection,key,names,done),schema,state,history) == finish(M.plan(schema,state,collection,key,names),remaining,schema,state,done,history) : S.Trace}
def actual_read_fields_has_total_exact_source_state_behavior(schema,state,collection,key,names,remaining,done,history):
  match names:
    case Nil{}: {==}
    case Con{+name,+tail}:
      result_case(D.operate(schema,state,D.ReadCell{collection,key,name}),schema,state,collection,key,name,tail,remaining,done,history,{==},Op.real_named_read_operations_have_only_the_expected_observation_or_data_failure(Op.Cell{},schema,state,collection,key,name),next => earlier => actual_read_fields_has_total_exact_source_state_behavior(schema,state,collection,key,tail,remaining,next,earlier))
