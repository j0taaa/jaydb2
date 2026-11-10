# Named write primitives have only Changed or FailureData for ALL input DATA.
# Observed Datum values are a helper-callback misuse, never real write output.
import Base
import ../contract/Data.bend as D
import ../proof/Foundations.bend as F

type WriteKind is Data:
  RowWrite{}
  ColumnWrite{}
  RowRemoval{}

def operation(kind: WriteKind,collection: D.Collection,key: String,name: String,fields: List<&2,D.Field>,value: D.Value) -> D.Operation:
  match kind:
    case RowWrite{}: D.DefineRow{collection,key,fields}
    case ColumnWrite{}: D.DefineColumn{collection,key,name,value}
    case RowRemoval{}: D.RemoveRow{collection,key}

def WriteResult(result: D.ResultOp) -> Data:
  match result:
    case D.FailureData{}: Unit
    case D.Changed{state}: Unit
    case D.Observed{observation}: {False{} == True{} : Bool}

def valid_write_result(valid: Bool,+collection: D.Collection,+state: D.State,+rows: List<&2,D.Row>) -> WriteResult(D.write_se(valid,collection,state,rows)):
  match valid:
    case False{}: Unit{}
    case True{}: Unit{}

def resolved_result(+kind: WriteKind,+collection: D.Collection,+key: String,+name: String,+fields: List<&2,D.Field>,+value: D.Value,+resolved: Maybe<&2,D.Resolved>,+state: D.State) -> WriteResult(D.operate_resolved(operation(kind,collection,key,name,fields,value),resolved,state)):
  match kind resolved:
    case RowWrite{} None{}: Unit{}
    case ColumnWrite{} None{}: Unit{}
    case RowRemoval{} None{}: Unit{}
    case RowWrite{} Some{D.Resolved{+schema,+rows}}: valid_write_result(D.row_is_valid(schema,D.Row{key,fields}),collection,state,D.insert_row(rows,D.Row{key,fields}))
    case ColumnWrite{} Some{D.Resolved{D.SchemaTable{table,+primary,+columns},+rows}}: valid_write_result(D.column_write_is_valid(D.find_column(columns,name),primary,key,value),collection,state,D.substitute_column(rows,key,name,value))
    case RowRemoval{} Some{D.Resolved{schema,rows}}: Unit{}

def address_result(valid: Bool,+kind: WriteKind,+schema: D.Schema,+state: D.State,+collection: D.Collection,+key: String,+name: String,+fields: List<&2,D.Field>,+value: D.Value) -> WriteResult(D.operate_address(valid,schema,state,operation(kind,collection,key,name,fields,value))):
  match valid:
    case False{}: Unit{}
    case True{}: resolved_result(kind,collection,key,name,fields,value,D.resolve_parts(D.schema_collection(D.collection_op(operation(kind,collection,key,name,fields,value)),schema),D.rows_collection(D.collection_op(operation(kind,collection,key,name,fields,value)),state)),state)

law every_actual_named_write_either_changes_the_working_state_or_fails_before_callback:
  for +kind: WriteKind
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +key: String
  for +name: String
  for +fields: List<&2,D.Field>
  for +value: D.Value
  WriteResult(D.operate(schema,state,operation(kind,collection,key,name,fields,value)))
def every_actual_named_write_either_changes_the_working_state_or_fails_before_callback(kind,schema,state,collection,key,name,fields,value):
  address_result(D.address_op_valid(operation(kind,collection,key,name,fields,value)),kind,schema,state,collection,key,name,fields,value)

# Successful primitive domains concern only input schema/state/address/value.
# These are NOT assumed operation outputs or whole-action postconditions.
def valid_row_has_a_valid_unicode_address(+schema: D.SchemaTable,+row: D.Row,valid: {D.row_is_valid(schema,row) == True{} : Bool}) -> {D.unicode_valid(D.row_key(row)) == True{} : Bool}:
  match schema row:
    case D.SchemaTable{name,primary,columns} D.Row{key,fields}: F.and_boolean_left(D.unicode_valid(key),D.fields_all_valid(columns,fields),F.and_boolean_left(D.unicode_valid(key) && D.fields_all_valid(columns,fields),D.key_correct(D.find_field(fields,primary),key),valid))

law defining_a_valid_row_in_an_existing_collection_performs_the_exact_upsert:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +table: D.SchemaTable
  for +rows: List<&2,D.Row>
  for +key: String
  for +fields: List<&2,D.Field>
  for schema_found: {D.schema_collection(collection,schema) == Some{table} : Maybe<&2,D.SchemaTable>}
  for rows_found: {D.rows_collection(collection,state) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for +row_valid: {D.row_is_valid(table,D.Row{key,fields}) == True{} : Bool}
  {D.operate(schema,state,D.DefineRow{collection,key,fields}) == D.Changed{D.swap_collection(collection,state,D.insert_row(rows,D.Row{key,fields}))} : D.ResultOp}
def defining_a_valid_row_in_an_existing_collection_performs_the_exact_upsert(schema,state,collection,table,rows,key,fields,schema_found,rows_found,row_valid):
  %Equal.sym(Bool,D.unicode_valid(key),True{},valid_row_has_a_valid_unicode_address(table,D.Row{key,fields},row_valid)) : {D.operate_address(_,schema,state,D.DefineRow{collection,key,fields}) == D.Changed{D.swap_collection(collection,state,D.insert_row(rows,D.Row{key,fields}))} : D.ResultOp}
  %Equal.sym(Maybe<&2,D.SchemaTable>,D.schema_collection(collection,schema),Some{table},schema_found) : {D.operate_resolved(D.DefineRow{collection,key,fields},D.resolve_parts(_,D.rows_collection(collection,state)),state) == D.Changed{D.swap_collection(collection,state,D.insert_row(rows,D.Row{key,fields}))} : D.ResultOp}
  %Equal.sym(Maybe<&2,List<&2,D.Row>>,D.rows_collection(collection,state),Some{rows},rows_found) : {D.operate_resolved(D.DefineRow{collection,key,fields},D.resolve_parts(Some{table},_),state) == D.Changed{D.swap_collection(collection,state,D.insert_row(rows,D.Row{key,fields}))} : D.ResultOp}
  %Equal.sym(Bool,D.row_is_valid(table,D.Row{key,fields}),True{},row_valid) : {D.write_se(_,collection,state,D.insert_row(rows,D.Row{key,fields})) == D.Changed{D.swap_collection(collection,state,D.insert_row(rows,D.Row{key,fields}))} : D.ResultOp}
  {==}

law removing_a_valid_address_in_an_existing_collection_performs_exact_removal:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +table: D.SchemaTable
  for +rows: List<&2,D.Row>
  for +key: String
  for address: {D.unicode_valid(key) == True{} : Bool}
  for schema_found: {D.schema_collection(collection,schema) == Some{table} : Maybe<&2,D.SchemaTable>}
  for rows_found: {D.rows_collection(collection,state) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  {D.operate(schema,state,D.RemoveRow{collection,key}) == D.Changed{D.swap_collection(collection,state,D.remove_row(rows,key))} : D.ResultOp}
def removing_a_valid_address_in_an_existing_collection_performs_exact_removal(schema,state,collection,table,rows,key,address,schema_found,rows_found):
  %Equal.sym(Bool,D.unicode_valid(key),True{},address) : {D.operate_address(_,schema,state,D.RemoveRow{collection,key}) == D.Changed{D.swap_collection(collection,state,D.remove_row(rows,key))} : D.ResultOp}
  %Equal.sym(Maybe<&2,D.SchemaTable>,D.schema_collection(collection,schema),Some{table},schema_found) : {D.operate_resolved(D.RemoveRow{collection,key},D.resolve_parts(_,D.rows_collection(collection,state)),state) == D.Changed{D.swap_collection(collection,state,D.remove_row(rows,key))} : D.ResultOp}
  %Equal.sym(Maybe<&2,List<&2,D.Row>>,D.rows_collection(collection,state),Some{rows},rows_found) : {D.operate_resolved(D.RemoveRow{collection,key},D.resolve_parts(Some{table},_),state) == D.Changed{D.swap_collection(collection,state,D.remove_row(rows,key))} : D.ResultOp}
  {==}

law defining_a_schema_compatible_column_updates_exactly_that_named_cell:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +table_name: String
  for +primary: String
  for +columns: List<&2,D.Column>
  for +rows: List<&2,D.Row>
  for +key: String
  for +name: String
  for +value: D.Value
  for address: {D.unicode_valid(key) == True{} : Bool}
  for schema_found: {D.schema_collection(collection,schema) == Some{D.SchemaTable{table_name,primary,columns}} : Maybe<&2,D.SchemaTable>}
  for rows_found: {D.rows_collection(collection,state) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for compatible: {D.column_write_is_valid(D.find_column(columns,name),primary,key,value) == True{} : Bool}
  {D.operate(schema,state,D.DefineColumn{collection,key,name,value}) == D.Changed{D.swap_collection(collection,state,D.substitute_column(rows,key,name,value))} : D.ResultOp}
def defining_a_schema_compatible_column_updates_exactly_that_named_cell(schema,state,collection,table_name,primary,columns,rows,key,name,value,address,schema_found,rows_found,compatible):
  %Equal.sym(Bool,D.unicode_valid(key),True{},address) : {D.operate_address(_,schema,state,D.DefineColumn{collection,key,name,value}) == D.Changed{D.swap_collection(collection,state,D.substitute_column(rows,key,name,value))} : D.ResultOp}
  %Equal.sym(Maybe<&2,D.SchemaTable>,D.schema_collection(collection,schema),Some{D.SchemaTable{table_name,primary,columns}},schema_found) : {D.operate_resolved(D.DefineColumn{collection,key,name,value},D.resolve_parts(_,D.rows_collection(collection,state)),state) == D.Changed{D.swap_collection(collection,state,D.substitute_column(rows,key,name,value))} : D.ResultOp}
  %Equal.sym(Maybe<&2,List<&2,D.Row>>,D.rows_collection(collection,state),Some{rows},rows_found) : {D.operate_resolved(D.DefineColumn{collection,key,name,value},D.resolve_parts(Some{D.SchemaTable{table_name,primary,columns}},_),state) == D.Changed{D.swap_collection(collection,state,D.substitute_column(rows,key,name,value))} : D.ResultOp}
  %Equal.sym(Bool,D.column_write_is_valid(D.find_column(columns,name),primary,key,value),True{},compatible) : {D.write_se(_,collection,state,D.substitute_column(rows,key,name,value)) == D.Changed{D.swap_collection(collection,state,D.substitute_column(rows,key,name,value))} : D.ResultOp}
  {==}
