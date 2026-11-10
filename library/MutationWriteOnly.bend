# Real ordered mutation helpers never receive an observed Datum from a write.
# Their primitive short-circuit is DataError; malformed supplied Returns are
# separately covered by the complete A.written decoder/prefix specification.
import Base
import ./MutationPrimitiveProofs.bend as Primitive
import ./MutationWriteSequence.bend as W
import ./MutationWritePlan.bend as M
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./ValueScalarProofs.bend as Pair
import ../proof/Foundations.bend as F

def NamedWrite(op: D.Operation) -> Data:
  match op:
    case D.DefineRow{collection,key,fields}: Unit
    case D.DefineColumn{collection,key,name,value}: Unit
    case D.RemoveRow{collection,key}: Unit
    case D.ReadCell{collection,key,name}: {False{} == True{} : Bool}
    case D.ViewExistence{collection,key}: {False{} == True{} : Bool}
    case D.CountRows{collection}: {False{} == True{} : Bool}
    case D.EnumerateKeys{collection}: {False{} == True{} : Bool}

def AllNamed(operations: List<&2,D.Operation>) -> Data:
  match operations:
    case Nil{}: Unit
    case Con{op,tail}: Pair.Both<NamedWrite(op),AllNamed(tail)>

def named_write_result(+op: D.Operation,+schema: D.Schema,+state: D.State,named: NamedWrite(op)) -> Primitive.WriteResult(D.operate(schema,state,op)):
  match op:
    case D.DefineRow{collection,key,fields}: Primitive.every_actual_named_write_either_changes_the_working_state_or_fails_before_callback(Primitive.RowWrite{},schema,state,collection,key,"",fields,D.VAbsent{})
    case D.DefineColumn{collection,key,name,value}: Primitive.every_actual_named_write_either_changes_the_working_state_or_fails_before_callback(Primitive.ColumnWrite{},schema,state,collection,key,name,Nil{},value)
    case D.RemoveRow{collection,key}: Primitive.every_actual_named_write_either_changes_the_working_state_or_fails_before_callback(Primitive.RowRemoval{},schema,state,collection,key,"",Nil{},D.VAbsent{})
    case D.ReadCell{collection,key,name}: F.absurd_boolean(Primitive.WriteResult(D.operate(schema,state,D.ReadCell{collection,key,name})),named)
    case D.ViewExistence{collection,key}: F.absurd_boolean(Primitive.WriteResult(D.operate(schema,state,D.ViewExistence{collection,key})),named)
    case D.CountRows{collection}: F.absurd_boolean(Primitive.WriteResult(D.operate(schema,state,D.CountRows{collection})),named)
    case D.EnumerateKeys{collection}: F.absurd_boolean(Primitive.WriteResult(D.operate(schema,state,D.EnumerateKeys{collection})),named)

def DataFailureOnly(plan: M.Plan) -> Data:
  match plan:
    case M.WriteHandoff{working,events}: Unit
    case M.WriteHalt{working,events,response}: {response == S.Response{S.DataError{},D.VAbsent{}} : S.Response}

def event_preserves_data_failure_only(+plan: M.Plan,+event: S.OperationEvent,proper: DataFailureOnly(plan)) -> DataFailureOnly(M.prepend(event,plan)):
  match plan:
    case M.WriteHandoff{working,events}: Unit{}
    case M.WriteHalt{working,events,response}: proper

def result_preserves_data_failure_only(+result: D.ResultOp,+before: D.State,+op: D.Operation,+tail: M.Plan,kind: Primitive.WriteResult(result),proper: DataFailureOnly(tail)) -> DataFailureOnly(M.combine(result,before,op,tail)):
  match result:
    case D.FailureData{}: {==}
    case D.Observed{observation}: F.absurd_boolean(DataFailureOnly(M.combine(D.Observed{observation},before,op,tail)),kind)
    case D.Changed{working}: event_preserves_data_failure_only(tail,S.OperationEvent{op,S.Write{}},proper)

law actual_named_write_sequence_stops_only_for_real_data_failure:
  for +operations: List<&2,D.Operation>
  for +schema: D.Schema
  for +before: D.State
  for named: AllNamed(operations)
  DataFailureOnly(M.plan(operations,schema,before))
def actual_named_write_sequence_stops_only_for_real_data_failure(operations,schema,before,named):
  match operations named:
    case Nil{} Unit{}: Unit{}
    case Con{+op,+tail} Pair.Both{head,rest}: result_preserves_data_failure_only(D.operate(schema,before,op),before,op,M.plan(tail,schema,M.after(D.operate(schema,before,op),before)),named_write_result(op,schema,before,head),actual_named_write_sequence_stops_only_for_real_data_failure(tail,schema,M.after(D.operate(schema,before,op),before),rest))

def rows_are_named(+collection: D.Collection,rows: List<&2,D.Row>) -> AllNamed(W.rows(collection,rows)):
  match rows:
    case Nil{}: Unit{}
    case Con{D.Row{key,fields},tail}: Pair.Both{Unit{},rows_are_named(collection,tail)}

def removals_are_named(+collection: D.Collection,keys: List<&2,String>) -> AllNamed(W.removals(collection,keys)):
  match keys:
    case Nil{}: Unit{}
    case Con{key,tail}: Pair.Both{Unit{},removals_are_named(collection,tail)}

def columns_are_named(+collection: D.Collection,+key: String,fields: List<&2,D.Field>) -> AllNamed(W.columns(collection,key,fields)):
  match fields:
    case Nil{}: Unit{}
    case Con{D.Field{name,value},tail}: Pair.Both{Unit{},columns_are_named(collection,key,tail)}

law actual_define_rows_cannot_refuse_a_malformed_write_return:
  for +schema: D.Schema
  for +before: D.State
  for +collection: D.Collection
  for +rows: List<&2,D.Row>
  DataFailureOnly(M.plan(W.rows(collection,rows),schema,before))
def actual_define_rows_cannot_refuse_a_malformed_write_return(schema,before,collection,rows):
  actual_named_write_sequence_stops_only_for_real_data_failure(W.rows(collection,rows),schema,before,rows_are_named(collection,rows))

law actual_remove_rows_cannot_refuse_a_malformed_write_return:
  for +schema: D.Schema
  for +before: D.State
  for +collection: D.Collection
  for +keys: List<&2,String>
  DataFailureOnly(M.plan(W.removals(collection,keys),schema,before))
def actual_remove_rows_cannot_refuse_a_malformed_write_return(schema,before,collection,keys):
  actual_named_write_sequence_stops_only_for_real_data_failure(W.removals(collection,keys),schema,before,removals_are_named(collection,keys))

law actual_columns_cannot_refuse_a_malformed_write_return:
  for +schema: D.Schema
  for +before: D.State
  for +collection: D.Collection
  for +key: String
  for +fields: List<&2,D.Field>
  DataFailureOnly(M.plan(W.columns(collection,key,fields),schema,before))
def actual_columns_cannot_refuse_a_malformed_write_return(schema,before,collection,key,fields):
  actual_named_write_sequence_stops_only_for_real_data_failure(W.columns(collection,key,fields),schema,before,columns_are_named(collection,key,fields))
