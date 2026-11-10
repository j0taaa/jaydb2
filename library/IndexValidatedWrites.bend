# Every named primitive success is DERIVED from independent input collection
# views, Unicode addresses and row/schema validity. The batch yields a known
# exact state/event plan and row view; no completed operation/loop is assumed.
import Base
import ./CollectionFrameProofs.bend as Frame
import ./CollectionSwapProofs.bend as Swap
import ./RowRemovalProofs.bend as Remove
import ./RowInsertionProofs.bend as Insert
import ./MutationPrimitiveProofs.bend as Primitive
import ./MutationWriteSequence.bend as W
import ./MutationWritePlan.bend as M
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./ValueScalarProofs.bend as Pair
import ../proof/Foundations.bend as F

def recorded(operations: List<&2,D.Operation>) -> List<&2,S.OperationEvent>:
  match operations:
    case Nil{}: Nil{}
    case Con{op,tail}: Con{S.OperationEvent{op,S.Write{}},recorded(tail)}

# Zero operations preserve the ENTIRE state. Replacing its existing view by
# equal rows is not identity on malformed duplicate physical tables.
def working(operations: List<&2,D.Operation>,collection: D.Collection,state: D.State,rows: List<&2,D.Row>) -> D.State:
  match operations:
    case Nil{}: state
    case Con{op,tail}: D.swap_collection(collection,state,rows)

def Success(+operations: List<&2,D.Operation>,+schema: D.Schema,+state: D.State,+collection: D.Collection,+rows: List<&2,D.Row>) -> Data:
  Pair.Both<{M.plan(operations,schema,state) == M.WriteHandoff{working(operations,collection,state,rows),recorded(operations)} : M.Plan},{D.rows_collection(collection,working(operations,collection,state,rows)) == Some{rows} : Maybe<&2,List<&2,D.Row>>}>

def unicode_keys(keys: List<&2,String>) -> Bool:
  match keys:
    case Nil{}: True{}
    case Con{key,tail}: D.unicode_valid(key) && unicode_keys(tail)

def ValidRows(+table: D.SchemaTable,rows: List<&2,D.Row>) -> Data:
  match rows:
    case Nil{}: Unit
    case Con{head,tail}: Pair.Both<{D.row_is_valid(table,head) == True{} : Bool},ValidRows(table,tail)>

law actual_contract_valid_rows_give_each_independent_row_validation:
  for +rows: List<&2,D.Row>
  for +table: D.SchemaTable
  for +valid: {D.rows_valid_cases(rows,table) == True{} : Bool}
  ValidRows(table,rows)
def actual_contract_valid_rows_give_each_independent_row_validation(rows,table,valid):
  match rows:
    case Nil{}: Unit{}
    case Con{D.Row{+key,+fields},+tail}: Pair.Both{F.and_boolean_left(D.row_is_valid(table,D.Row{key,fields}),D.rows_later(tail,key),F.and_boolean_left(D.row_is_valid(table,D.Row{key,fields}) && D.rows_later(tail,key),D.rows_valid_cases(tail,table),valid)),actual_contract_valid_rows_give_each_independent_row_validation(tail,table,F.and_boolean_right(D.row_is_valid(table,D.Row{key,fields}) && D.rows_later(tail,key),D.rows_valid_cases(tail,table),valid))}

law actual_contract_valid_rows_have_only_unicode_enumerated_addresses:
  for +rows: List<&2,D.Row>
  for +table: D.SchemaTable
  for +valid: {D.rows_valid_cases(rows,table) == True{} : Bool}
  {unicode_keys(D.keys_rows(rows)) == True{} : Bool}
def actual_contract_valid_rows_have_only_unicode_enumerated_addresses(rows,table,valid):
  match rows:
    case Nil{}: {==}
    case Con{D.Row{+key,+fields},+tail}: F.and_boolean_intro(D.unicode_valid(key),unicode_keys(D.keys_rows(tail)),Primitive.valid_row_has_a_valid_unicode_address(table,D.Row{key,fields},F.and_boolean_left(D.row_is_valid(table,D.Row{key,fields}),D.rows_later(tail,key),F.and_boolean_left(D.row_is_valid(table,D.Row{key,fields}) && D.rows_later(tail,key),D.rows_valid_cases(tail,table),valid))),actual_contract_valid_rows_have_only_unicode_enumerated_addresses(tail,table,F.and_boolean_right(D.row_is_valid(table,D.Row{key,fields}) && D.rows_later(tail,key),D.rows_valid_cases(tail,table),valid)))

def prepend_succeeded(+op: D.Operation,+tail: List<&2,D.Operation>,+schema: D.Schema,+state: D.State,+collection: D.Collection,+previous: List<&2,D.Row>,+next: List<&2,D.Row>,+expected: List<&2,D.Row>,actual: {D.operate(schema,state,op) == D.Changed{D.swap_collection(collection,state,next)} : D.ResultOp},collapsed: {working(tail,collection,D.swap_collection(collection,state,next),expected) == D.swap_collection(collection,state,expected) : D.State},found: {D.rows_collection(collection,state) == Some{previous} : Maybe<&2,List<&2,D.Row>>},success: Success(tail,schema,D.swap_collection(collection,state,next),collection,expected)) -> Success(Con{op,tail},schema,state,collection,expected):
  match success:
    case Pair.Both{plan,view}:
      Pair.Both{Equal.trans(M.Plan,M.plan(Con{op,tail},schema,state),M.prepend(S.OperationEvent{op,S.Write{}},M.plan(tail,schema,D.swap_collection(collection,state,next))),M.WriteHandoff{D.swap_collection(collection,state,expected),recorded(Con{op,tail})},Equal.cong(D.ResultOp,M.Plan,result => M.combine(result,state,op,M.plan(tail,schema,M.after(result,state))),D.operate(schema,state,op),D.Changed{D.swap_collection(collection,state,next)},actual),Equal.trans(M.Plan,M.prepend(S.OperationEvent{op,S.Write{}},M.plan(tail,schema,D.swap_collection(collection,state,next))),M.WriteHandoff{working(tail,collection,D.swap_collection(collection,state,next),expected),recorded(Con{op,tail})},M.WriteHandoff{D.swap_collection(collection,state,expected),recorded(Con{op,tail})},Equal.cong(M.Plan,M.Plan,p => M.prepend(S.OperationEvent{op,S.Write{}},p),M.plan(tail,schema,D.swap_collection(collection,state,next)),M.WriteHandoff{working(tail,collection,D.swap_collection(collection,state,next),expected),recorded(tail)},plan),Equal.cong(D.State,M.Plan,w => M.WriteHandoff{w,recorded(Con{op,tail})},working(tail,collection,D.swap_collection(collection,state,next),expected),D.swap_collection(collection,state,expected),collapsed))),Frame.replacing_an_existing_collection_has_the_exact_new_row_view(collection,state,previous,expected,found)}

law completing_removals_after_a_first_change_has_the_exact_last_replacement_state:
  for +keys: List<&2,String>
  for +collection: D.Collection
  for +state: D.State
  for +first: List<&2,D.Row>
  {working(W.removals(collection,keys),collection,D.swap_collection(collection,state,first),Remove.all(keys,first)) == D.swap_collection(collection,state,Remove.all(keys,first)) : D.State}
def completing_removals_after_a_first_change_has_the_exact_last_replacement_state(keys,collection,state,first):
  match keys:
    case Nil{}: {==}
    case Con{head,tail}: Swap.last_collection_replacement_overrides_every_prior_replacement(collection,state,first,Remove.all(Con{head,tail},first))

law every_valid_addressed_removal_batch_has_exact_state_events_and_transformed_rows:
  for +keys: List<&2,String>
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +table: D.SchemaTable
  for +rows: List<&2,D.Row>
  for +schema_found: {D.schema_collection(collection,schema) == Some{table} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(collection,state) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for +valid: {unicode_keys(keys) == True{} : Bool}
  Success(W.removals(collection,keys),schema,state,collection,Remove.all(keys,rows))
def every_valid_addressed_removal_batch_has_exact_state_events_and_transformed_rows(keys,schema,state,collection,table,rows,schema_found,rows_found,valid):
  match keys:
    case Nil{}: Pair.Both{{==},rows_found}
    case Con{+key,+tail}:
      prepend_succeeded(D.RemoveRow{collection,key},W.removals(collection,tail),schema,state,collection,rows,D.remove_row(rows,key),Remove.all(tail,D.remove_row(rows,key)),Primitive.removing_a_valid_address_in_an_existing_collection_performs_exact_removal(schema,state,collection,table,rows,key,F.and_boolean_left(D.unicode_valid(key),unicode_keys(tail),valid),schema_found,rows_found),completing_removals_after_a_first_change_has_the_exact_last_replacement_state(tail,collection,state,D.remove_row(rows,key)),rows_found,every_valid_addressed_removal_batch_has_exact_state_events_and_transformed_rows(tail,schema,D.swap_collection(collection,state,D.remove_row(rows,key)),collection,table,D.remove_row(rows,key),schema_found,Frame.replacing_an_existing_collection_has_the_exact_new_row_view(collection,state,rows,D.remove_row(rows,key),rows_found),F.and_boolean_right(D.unicode_valid(key),unicode_keys(tail),valid)))

law completing_upserts_after_a_first_change_has_the_exact_last_replacement_state:
  for +rows: List<&2,D.Row>
  for +collection: D.Collection
  for +state: D.State
  for +first: List<&2,D.Row>
  {working(W.rows(collection,rows),collection,D.swap_collection(collection,state,first),Insert.all(rows,first)) == D.swap_collection(collection,state,Insert.all(rows,first)) : D.State}
def completing_upserts_after_a_first_change_has_the_exact_last_replacement_state(rows,collection,state,first):
  match rows:
    case Nil{}: {==}
    case Con{D.Row{key,fields},tail}: Swap.last_collection_replacement_overrides_every_prior_replacement(collection,state,first,Insert.all(Con{D.Row{key,fields},tail},first))

law every_schema_valid_upsert_batch_has_exact_state_events_and_transformed_rows:
  for +new: List<&2,D.Row>
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +table: D.SchemaTable
  for +rows: List<&2,D.Row>
  for +schema_found: {D.schema_collection(collection,schema) == Some{table} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(collection,state) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for valid: ValidRows(table,new)
  Success(W.rows(collection,new),schema,state,collection,Insert.all(new,rows))
def every_schema_valid_upsert_batch_has_exact_state_events_and_transformed_rows(new,schema,state,collection,table,rows,schema_found,rows_found,valid):
  match new valid:
    case Nil{} Unit{}: Pair.Both{{==},rows_found}
    case Con{D.Row{+key,+fields},+tail} Pair.Both{head,rest}:
      prepend_succeeded(D.DefineRow{collection,key,fields},W.rows(collection,tail),schema,state,collection,rows,D.insert_row(rows,D.Row{key,fields}),Insert.all(tail,D.insert_row(rows,D.Row{key,fields})),Primitive.defining_a_valid_row_in_an_existing_collection_performs_the_exact_upsert(schema,state,collection,table,rows,key,fields,schema_found,rows_found,head),completing_upserts_after_a_first_change_has_the_exact_last_replacement_state(tail,collection,state,D.insert_row(rows,D.Row{key,fields})),rows_found,every_schema_valid_upsert_batch_has_exact_state_events_and_transformed_rows(tail,schema,D.swap_collection(collection,state,D.insert_row(rows,D.Row{key,fields})),collection,table,D.insert_row(rows,D.Row{key,fields}),schema_found,Frame.replacing_an_existing_collection_has_the_exact_new_row_view(collection,state,rows,D.insert_row(rows,D.Row{key,fields}),rows_found),rest))
