# Ordinary full-row receipt write. It performs no authentication, admission or
# publication; exact engine effects follow from the ordinary write semantics.
import Base
import ./ReceiptAdapterProofs.bend as Adapter
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Receipts.bend as H
import ./MutationWritePlan.bend as M
import ./MutationWriteTrace.bend as R
import ./MutationPrimitiveProofs.bend as Primitive
import ./ReadOperationProofs.bend as Failure
import ../proof/Foundations.bend as F
import ../src/Termination.bend as T

def operation(owner: String,key: String,fields: List<&2,D.Field>) -> D.Operation: D.DefineRow{D.Application{owner},key,fields}

law receipt_put_is_exactly_one_named_complete_row_write_before_the_caller:
  for +owner: String
  for +key: String
  for +fields: List<&2,D.Field>
  for -next: S.Action
  {H.put(owner,key,fields,next) == S.Access{operation(owner,key,fields),H.written(next)} : S.Action}
def receipt_put_is_exactly_one_named_complete_row_write_before_the_caller(owner,key,fields,next): {==}

def result_case(+result: D.ResultOp,+schema: D.Schema,+before: D.State,+owner: String,+key: String,+fields: List<&2,D.Field>,+remaining: Nat,-next: S.Action,+history: List<&2,S.OperationEvent>,actual: {D.operate(schema,before,operation(owner,key,fields)) == result : D.ResultOp},kind: Primitive.WriteResult(result)) -> {T.observe(2n+remaining,H.put(owner,key,fields,next),schema,before,history) == R.finish(M.combine(result,before,operation(owner,key,fields),M.WriteHandoff{M.after(result,before),Nil{}}),1n+remaining,schema,next,history) : S.Trace}:
  match result:
    case D.FailureData{}: Failure.actual_data_failure_retains_its_event_and_finishes_without_a_return_callback(1n+remaining,schema,before,operation(owner,key,fields),H.written(next),history,actual)
    case D.Changed{+working}: R.real_changed_primitive_retains_the_write_and_continues_in_its_actual_new_state(1n+remaining,schema,before,working,operation(owner,key,fields),H.written(next),history,actual)
    case D.Observed{observation}: F.absurd_boolean({T.observe(2n+remaining,H.put(owner,key,fields,next),schema,before,history) == R.finish(M.combine(D.Observed{observation},before,operation(owner,key,fields),M.WriteHandoff{before,Nil{}}),1n+remaining,schema,next,history) : S.Trace},kind)

law actual_receipt_put_has_total_exact_state_event_error_and_handoff_behavior:
  for +schema: D.Schema
  for +before: D.State
  for +owner: String
  for +key: String
  for +fields: List<&2,D.Field>
  for +remaining: Nat
  for -next: S.Action
  for +history: List<&2,S.OperationEvent>
  {T.observe(2n+remaining,H.put(owner,key,fields,next),schema,before,history) == R.finish(M.plan([operation(owner,key,fields)],schema,before),1n+remaining,schema,next,history) : S.Trace}
def actual_receipt_put_has_total_exact_state_event_error_and_handoff_behavior(schema,before,owner,key,fields,remaining,next,history):
  result_case(D.operate(schema,before,operation(owner,key,fields)),schema,before,owner,key,fields,remaining,next,history,{==},Primitive.every_actual_named_write_either_changes_the_working_state_or_fails_before_callback(Primitive.RowWrite{},schema,before,D.Application{owner},key,"",fields,D.VAbsent{}))

law an_actual_valid_receipt_put_upserts_the_complete_input_row_then_hands_off:
  for +schema: D.Schema
  for +before: D.State
  for +owner: String
  for +key: String
  for +fields: List<&2,D.Field>
  for +table: D.SchemaTable
  for +rows: List<&2,D.Row>
  for +remaining: Nat
  for -next: S.Action
  for +history: List<&2,S.OperationEvent>
  for schema_found: {D.schema_collection(D.Application{owner},schema) == Some{table} : Maybe<&2,D.SchemaTable>}
  for rows_found: {D.rows_collection(D.Application{owner},before) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for valid: {D.row_is_valid(table,D.Row{key,fields}) == True{} : Bool}
  {T.observe(2n+remaining,H.put(owner,key,fields,next),schema,before,history) == T.observe(1n+remaining,next,schema,D.swap_collection(D.Application{owner},before,D.insert_row(rows,D.Row{key,fields})),S.append(history,S.OperationEvent{operation(owner,key,fields),S.Write{}})) : S.Trace}
def an_actual_valid_receipt_put_upserts_the_complete_input_row_then_hands_off(schema,before,owner,key,fields,table,rows,remaining,next,history,schema_found,rows_found,valid):
  R.real_changed_primitive_retains_the_write_and_continues_in_its_actual_new_state(1n+remaining,schema,before,D.swap_collection(D.Application{owner},before,D.insert_row(rows,D.Row{key,fields})),operation(owner,key,fields),H.written(next),history,Primitive.defining_a_valid_row_in_an_existing_collection_performs_the_exact_upsert(schema,before,D.Application{owner},table,rows,key,fields,schema_found,rows_found,valid))
