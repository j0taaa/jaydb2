# Total source-plan properties. Canonicality comes from actual D.structure and
# requested-name validation; ordinary returns come from the actual named-read
# implementation. No successful execution or final result is a premise.
import Base
import ./ReadProgramProofs.bend as Total
import ./ReadProgram.bend as P
import ../src/Termination.bend as T
import ./QueryReadPlan.bend as M
import ./QuerySelectionModel.bend as Meaning
import ./ReadOperationProofs.bend as Op
import ./ReadValueValidity.bend as V
import ./QuerySelectionCanonical.bend as C
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Query.bend as Q
import ../proof/Foundations.bend as F

def Head(plan: M.Plan,+names: List<&2,String>,+previous: String) -> Data:
  match plan:
    case M.ReadsReady{problem,record,events}: {D.record_later(record,previous) == Q.later(previous,names) : Bool}
    case M.ReadsFailed{events}: Unit

def extended_head(+result: D.ResultOp,+tail: M.Plan,+op: D.Operation,+name: String,+names: List<&2,String>,+previous: String) -> Head(M.extend(op,name,result,tail),Con{name,names},previous):
  match result tail:
    case D.FailureData{} tail: Unit{}
    case D.Changed{state} tail: Unit{}
    case D.Observed{observation} M.ReadsFailed{events}: Unit{}
    case D.Observed{observation} M.ReadsReady{problem,record,events}: {==}

law a_ready_source_record_has_exactly_the_requested_first_field:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +key: String
  for +names: List<&2,String>
  for +previous: String
  Head(M.plan(schema,state,collection,key,names),names,previous)
def a_ready_source_record_has_exactly_the_requested_first_field(schema,state,collection,key,names,previous):
  match names:
    case Nil{}: {==}
    case Con{+name,+tail}: extended_head(D.operate(schema,state,D.ReadCell{collection,key,name}),M.plan(schema,state,collection,key,tail),D.ReadCell{collection,key,name},name,tail,previous)

def Canonical(plan: M.Plan) -> Data:
  match plan:
    case M.ReadsReady{problem,record,events}: {D.value_valid(record) == True{} : Bool}
    case M.ReadsFailed{events}: Unit

def canonical_extension(+result: D.ResultOp,+tail: M.Plan,+op: D.Operation,+name: String,+names: List<&2,String>,+valid_name: {D.name_valid(name) == True{} : Bool},+later: {Q.later(name,names) == True{} : Bool},payload: V.ResultValue(result),canonical: Canonical(tail),head: Head(tail,names,name)) -> Canonical(M.extend(op,name,result,tail)):
  match result tail:
    case D.FailureData{} tail: Unit{}
    case D.Changed{state} tail: Unit{}
    case D.Observed{observation} M.ReadsFailed{events}: Unit{}
    case D.Observed{+observation} M.ReadsReady{problem,+record,events}:
      F.and_boolean_intro(D.name_valid(name) && D.value_valid(Meaning.payload(S.Datum{observation})) && D.record_later(record,name),D.value_valid(record),F.and_boolean_intro(D.name_valid(name) && D.value_valid(Meaning.payload(S.Datum{observation})),D.record_later(record,name),F.and_boolean_intro(D.name_valid(name),D.value_valid(Meaning.payload(S.Datum{observation})),valid_name,C.observation_payload_is_valid(observation,payload)),Equal.trans(Bool,D.record_later(record,name),Q.later(name,names),True{},head,later)),canonical)

law total_source_plan_selected_records_are_canonical_for_every_structured_state:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +key: String
  for +names: List<&2,String>
  for +structured: {D.structure(schema,state) == True{} : Bool}
  for +valid_names: {Q.fields_valid(names) == True{} : Bool}
  Canonical(M.plan(schema,state,collection,key,names))
def total_source_plan_selected_records_are_canonical_for_every_structured_state(schema,state,collection,key,names,structured,valid_names):
  match names:
    case Nil{}: {==}
    case Con{+name,+tail}:
      +first = F.and_boolean_left(D.name_valid(name) && Q.later(name,tail),Q.fields_valid(tail),valid_names)
      canonical_extension(D.operate(schema,state,D.ReadCell{collection,key,name}),M.plan(schema,state,collection,key,tail),D.ReadCell{collection,key,name},name,tail,F.and_boolean_left(D.name_valid(name),Q.later(name,tail),first),F.and_boolean_right(D.name_valid(name),Q.later(name,tail),first),V.actual_reads_of_structured_states_cannot_return_invalid_cell_payloads(schema,state,collection,key,name,structured),total_source_plan_selected_records_are_canonical_for_every_structured_state(schema,state,collection,key,tail,structured,F.and_boolean_right(D.name_valid(name) && Q.later(name,tail),Q.fields_valid(tail),valid_names)),a_ready_source_record_has_exactly_the_requested_first_field(schema,state,collection,key,tail,name))

# Actual named reads produce Cell/RowAbsent or data failure, so their total
# plan cannot produce helper-level UnexpectedReturn. This needs no state/schema
# validity or success premise.
def Ordinary(plan: M.Plan) -> Data:
  match plan:
    case M.ReadsReady{Meaning.Clear{},record,events}: Unit
    case M.ReadsReady{Meaning.Absent{},record,events}: Unit
    case M.ReadsReady{Meaning.Unexpected{},record,events}: {False{} == True{} : Bool}
    case M.ReadsFailed{events}: Unit

def cell_preserves_ordinary(+tail: M.Plan,+op: D.Operation,+name: String,+value: D.Value,ordinary: Ordinary(tail)) -> Ordinary(M.observed(op,name,D.Cell{value},tail)):
  match tail:
    case M.ReadsReady{Meaning.Clear{},record,events}: Unit{}
    case M.ReadsReady{Meaning.Absent{},record,events}: Unit{}
    case M.ReadsReady{Meaning.Unexpected{},record,events}: ordinary
    case M.ReadsFailed{events}: Unit{}

def absent_preserves_ordinary(+tail: M.Plan,+op: D.Operation,+name: String) -> Ordinary(M.observed(op,name,D.RowAbsent{},tail)):
  match tail:
    case M.ReadsReady{problem,record,events}: Unit{}
    case M.ReadsFailed{events}: Unit{}

def observed_preserves_ordinary(+observation: D.Observation,+tail: M.Plan,+op: D.Operation,+name: String,kind: Op.ObservationKind(Op.Cell{},observation),ordinary: Ordinary(tail)) -> Ordinary(M.observed(op,name,observation,tail)):
  match observation:
    case D.Cell{value}: cell_preserves_ordinary(tail,op,name,value,ordinary)
    case D.RowAbsent{}: absent_preserves_ordinary(tail,op,name)
    case D.Keys{keys}: F.absurd_boolean(Ordinary(M.observed(op,name,D.Keys{keys},tail)),kind)
    case D.Count{count}: F.absurd_boolean(Ordinary(M.observed(op,name,D.Count{count},tail)),kind)
    case D.Existence{exists}: F.absurd_boolean(Ordinary(M.observed(op,name,D.Existence{exists},tail)),kind)

def extension_preserves_ordinary(+result: D.ResultOp,+tail: M.Plan,+op: D.Operation,+name: String,kind: Op.ResultKind(Op.Cell{},result),ordinary: Ordinary(tail)) -> Ordinary(M.extend(op,name,result,tail)):
  match result:
    case D.FailureData{}: Unit{}
    case D.Changed{state}: F.absurd_boolean(Ordinary(M.extend(op,name,D.Changed{state},tail)),kind)
    case D.Observed{observation}: observed_preserves_ordinary(observation,tail,op,name,kind,ordinary)

law actual_total_source_read_plan_cannot_generate_an_unexpected_return:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +key: String
  for +names: List<&2,String>
  Ordinary(M.plan(schema,state,collection,key,names))
def actual_total_source_read_plan_cannot_generate_an_unexpected_return(schema,state,collection,key,names):
  match names:
    case Nil{}: Unit{}
    case Con{+name,+tail}: extension_preserves_ordinary(D.operate(schema,state,D.ReadCell{collection,key,name}),M.plan(schema,state,collection,key,tail),D.ReadCell{collection,key,name},name,Op.real_named_read_operations_have_only_the_expected_observation_or_data_failure(Op.Cell{},schema,state,collection,key,name),actual_total_source_read_plan_cannot_generate_an_unexpected_return(schema,state,collection,key,tail))

# Both exact total behavior and final value validity are stated on the ACTUAL
# closed action, with no assumed returned value/trace or successful-prefix fact.

def CanonicalTrace(trace: S.Trace) -> Data:
  match trace:
    case S.Prefix{state,events}: {False{} == True{} : Bool}
    case S.Final{state,events,S.Response{status,value}}: {D.value_valid(value) == True{} : Bool}

def canonical_plan_closes_with_a_valid_response(+plan: M.Plan,+state: D.State,+history: List<&2,S.OperationEvent>,canonical: Canonical(plan)) -> CanonicalTrace(Total.close(plan,state,history)):
  match plan:
    case M.ReadsFailed{events}: {==}
    case M.ReadsReady{Meaning.Clear{},record,events}: canonical
    case M.ReadsReady{Meaning.Absent{},record,events}: {==}
    case M.ReadsReady{Meaning.Unexpected{},record,events}: {==}

def canonical_result_case(valid: Bool,+schema: D.Schema,+state: D.State,+collection: D.Collection,+key: String,+names: List<&2,String>,+history: List<&2,S.OperationEvent>,+structured: {D.structure(schema,state) == True{} : Bool},valid_names: {Q.fields_valid(names) == valid : Bool}) -> CanonicalTrace(Total.result(valid,M.plan(schema,state,collection,key,names),state,history)):
  match valid:
    case False{}: {==}
    case True{}: canonical_plan_closes_with_a_valid_response(M.plan(schema,state,collection,key,names),state,history,total_source_plan_selected_records_are_canonical_for_every_structured_state(schema,state,collection,key,names,structured,valid_names))

law actual_public_select_is_complete_and_returns_a_valid_value_for_every_structured_state:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +key: String
  for +names: List<&2,String>
  for +history: List<&2,S.OperationEvent>
  for +structured: {D.structure(schema,state) == True{} : Bool}
  CanonicalTrace(T.observe(Total.depth(Q.fields_valid(names),names),P.select(collection,key,names),schema,state,history))
def actual_public_select_is_complete_and_returns_a_valid_value_for_every_structured_state(schema,state,collection,key,names,history,structured):
  %Equal.sym(S.Trace,T.observe(Total.depth(Q.fields_valid(names),names),P.select(collection,key,names),schema,state,history),Total.result(Q.fields_valid(names),M.plan(schema,state,collection,key,names),state,history),Total.actual_public_read_program_select_has_total_exact_behavior_for_every_input(schema,state,collection,key,names,history)) : CanonicalTrace(_)
  canonical_result_case(Q.fields_valid(names),schema,state,collection,key,names,history,structured,{==})
