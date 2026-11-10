# Real D.operate can return only the appropriate observation kind or DATA
# failure for these named reads, even for arbitrary input schema/state DATA.
# DATA failure stops before the continuation; it is not an unexpected Return.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../src/Termination.bend as T

type ReadKind is Data:
  Cell{}
  ExistenceRead{}
  Count{}
  Keys{}

def operation(kind: ReadKind,c: D.Collection,key: String,column: String) -> D.Operation:
  match kind:
    case Cell{}: D.ReadCell{c,key,column}
    case ExistenceRead{}: D.ViewExistence{c,key}
    case Count{}: D.CountRows{c}
    case Keys{}: D.EnumerateKeys{c}


def ObservationKind(kind: ReadKind,observation: D.Observation) -> Data:
  match kind observation:
    case Cell{} D.Cell{value}: Unit
    case Cell{} D.RowAbsent{}: Unit
    case ExistenceRead{} D.Existence{b}: Unit
    case Count{} D.Count{n}: Unit
    case Keys{} D.Keys{xs}: Unit
    case Cell{} D.Existence{b}: {False{} == True{} : Bool}
    case Cell{} D.Count{n}: {False{} == True{} : Bool}
    case Cell{} D.Keys{xs}: {False{} == True{} : Bool}
    case ExistenceRead{} D.Cell{value}: {False{} == True{} : Bool}
    case ExistenceRead{} D.RowAbsent{}: {False{} == True{} : Bool}
    case ExistenceRead{} D.Count{n}: {False{} == True{} : Bool}
    case ExistenceRead{} D.Keys{xs}: {False{} == True{} : Bool}
    case Count{} D.Cell{value}: {False{} == True{} : Bool}
    case Count{} D.RowAbsent{}: {False{} == True{} : Bool}
    case Count{} D.Existence{b}: {False{} == True{} : Bool}
    case Count{} D.Keys{xs}: {False{} == True{} : Bool}
    case Keys{} D.Cell{value}: {False{} == True{} : Bool}
    case Keys{} D.RowAbsent{}: {False{} == True{} : Bool}
    case Keys{} D.Existence{b}: {False{} == True{} : Bool}
    case Keys{} D.Count{n}: {False{} == True{} : Bool}

def ResultKind(+kind: ReadKind,result: D.ResultOp) -> Data:
  match result:
    case D.FailureData{}: Unit
    case D.Observed{observation}: ObservationKind(kind,observation)
    case D.Changed{state}: {False{} == True{} : Bool}


def result_cell_kind(value: Maybe<&2,D.Value>) -> ResultKind(Cell{},D.result_cell(value)):
  match value:
    case None{}: Unit{}
    case Some{v}: Unit{}

def row_kind(row: Maybe<&2,D.Row>,+column: String) -> ResultKind(Cell{},D.read_row(row,column)):
  match row:
    case None{}: Unit{}
    case Some{D.Row{key,fields}}: result_cell_kind(D.find_field(fields,column))

def column_kind(column: Maybe<&2,D.Column>,+row: Maybe<&2,D.Row>,+name: String) -> ResultKind(Cell{},D.read_column(column,row,name)):
  match column:
    case None{}: Unit{}
    case Some{c}: row_kind(row,name)


def resolved_kind(+kind: ReadKind,+c: D.Collection,+key: String,+column: String,resolved: Maybe<&2,D.Resolved>,+state: D.State) -> ResultKind(kind,D.operate_resolved(operation(kind,c,key,column),resolved,state)):
  match kind resolved:
    case Cell{} None{}: Unit{}
    case ExistenceRead{} None{}: Unit{}
    case Count{} None{}: Unit{}
    case Keys{} None{}: Unit{}
    case Cell{} Some{D.Resolved{D.SchemaTable{name,primary,columns},rows}}: column_kind(D.find_column(columns,column),D.find_row(rows,key),column)
    case ExistenceRead{} Some{D.Resolved{schema,rows}}: Unit{}
    case Count{} Some{D.Resolved{schema,rows}}: Unit{}
    case Keys{} Some{D.Resolved{schema,rows}}: Unit{}


def address_kind(valid: Bool,+kind: ReadKind,+schema: D.Schema,+state: D.State,+c: D.Collection,+key: String,+column: String) -> ResultKind(kind,D.operate_address(valid,schema,state,operation(kind,c,key,column))):
  match valid:
    case False{}: Unit{}
    case True{}: resolved_kind(kind,c,key,column,D.resolve_parts(D.schema_collection(D.collection_op(operation(kind,c,key,column)),schema),D.rows_collection(D.collection_op(operation(kind,c,key,column)),state)),state)

law real_named_read_operations_have_only_the_expected_observation_or_data_failure:
  for +kind: ReadKind
  for +schema: D.Schema
  for +state: D.State
  for +c: D.Collection
  for +key: String
  for +column: String
  ResultKind(kind,D.operate(schema,state,operation(kind,c,key,column)))
def real_named_read_operations_have_only_the_expected_observation_or_data_failure(kind,schema,state,c,key,column):
  address_kind(D.address_op_valid(operation(kind,c,key,column)),kind,schema,state,c,key,column)

# A missing schema column fails even if the row is absent. A known column and
# absent row yields RowAbsent. A present absent-valued cell is still Cell data.
law missing_schema_column_is_data_failure_before_row_classification:
  for -row: Maybe<&2,D.Row>
  for -name: String
  {D.read_column(None{},row,name) == D.FailureData{} : D.ResultOp}
def missing_schema_column_is_data_failure_before_row_classification(row,name): {==}

law known_schema_column_and_absent_row_returns_row_absence:
  for -column: D.Column
  for -name: String
  {D.read_column(Some{column},None{},name) == D.Observed{D.RowAbsent{}} : D.ResultOp}
def known_schema_column_and_absent_row_returns_row_absence(column,name): {==}

law absent_cell_value_is_observed_data:
  {D.result_cell(Some{D.VAbsent{}}) == D.Observed{D.Cell{D.VAbsent{}}} : D.ResultOp}
def absent_cell_value_is_observed_data(): {==}

law missing_field_in_a_present_row_is_data_failure:
  {D.result_cell(None{}) == D.FailureData{} : D.ResultOp}
def missing_field_in_a_present_row_is_data_failure(): {==}

# The actual operation result is substituted into S.step, then the existing
# execution theorem gives the final error for EVERY remaining trace depth.
law actual_data_failure_stops_before_invoking_any_continuation:
  for +schema: D.Schema
  for +state: D.State
  for +op: D.Operation
  for -resume: S.Return -> S.Action
  for actual: {D.operate(schema,state,op) == D.FailureData{} : D.ResultOp}
  {S.step(S.Access{op,resume},schema,state) == S.OperationFailed{state,S.OperationEvent{op,S.ErrorOfData{}}} : S.Step}
def actual_data_failure_stops_before_invoking_any_continuation(schema,state,op,resume,actual):
  Equal.cong(D.ResultOp,S.Step,result => S.apply(result,state,op,resume),D.operate(schema,state,op),D.FailureData{},actual)

law actual_data_failure_retains_its_event_and_finishes_without_a_return_callback:
  for +remaining: Nat
  for +schema: D.Schema
  for +state: D.State
  for +op: D.Operation
  for -resume: S.Return -> S.Action
  for +history: List<&2,S.OperationEvent>
  for actual: {D.operate(schema,state,op) == D.FailureData{} : D.ResultOp}
  {S.resume_execution_trace(remaining,S.step(S.Access{op,resume},schema,state),schema,history) == S.Final{state,S.append(history,S.OperationEvent{op,S.ErrorOfData{}}),S.Response{S.DataError{},D.VAbsent{}}} : S.Trace}
def actual_data_failure_retains_its_event_and_finishes_without_a_return_callback(remaining,schema,state,op,resume,history,actual):
  Equal.trans(S.Trace,S.resume_execution_trace(remaining,S.step(S.Access{op,resume},schema,state),schema,history),S.resume_execution_trace(remaining,S.OperationFailed{state,S.OperationEvent{op,S.ErrorOfData{}}},schema,history),S.Final{state,S.append(history,S.OperationEvent{op,S.ErrorOfData{}}),S.Response{S.DataError{},D.VAbsent{}}},
    Equal.cong(S.Step,S.Trace,step => S.resume_execution_trace(remaining,step,schema,history),S.step(S.Access{op,resume},schema,state),S.OperationFailed{state,S.OperationEvent{op,S.ErrorOfData{}}},actual_data_failure_stops_before_invoking_any_continuation(schema,state,op,resume,actual)),T.failure_of_operation(remaining,state,S.OperationEvent{op,S.ErrorOfData{}},schema,history))
