# Complete source cases for ordinary row writes. Existence and row validation
# are INPUT facts; no operation result or desired action outcome is assumed.
import Base
import ../contract/Data.bend as D
import ../proof/Foundations.bend as F

law a_schema_rejected_unicode_address_is_already_a_rejected_full_row:
  for +table: D.SchemaTable
  for +key: String
  for +fields: List<&2,D.Field>
  for invalid: {D.unicode_valid(key) == False{} : Bool}
  {D.row_is_valid(table,D.Row{key,fields}) == False{} : Bool}
def a_schema_rejected_unicode_address_is_already_a_rejected_full_row(table,key,fields,invalid):
  match table:
    case D.SchemaTable{name,primary,columns}: Equal.cong(Bool,Bool,b => b && D.fields_all_valid(columns,fields) && D.key_correct(D.find_field(fields,primary),key),D.unicode_valid(key),False{},invalid)

def known_address_case(valid: Bool,+schema: D.Schema,+before: D.State,+collection: D.Collection,+table: D.SchemaTable,+rows: List<&2,D.Row>,+key: String,+fields: List<&2,D.Field>,actual: {D.unicode_valid(key) == valid : Bool},schema_found: {D.schema_collection(collection,schema) == Some{table} : Maybe<&2,D.SchemaTable>},rows_found: {D.rows_collection(collection,before) == Some{rows} : Maybe<&2,List<&2,D.Row>>}) -> {D.operate_address(valid,schema,before,D.DefineRow{collection,key,fields}) == D.write_se(D.row_is_valid(table,D.Row{key,fields}),collection,before,D.insert_row(rows,D.Row{key,fields})) : D.ResultOp}:
  match valid:
    case False{}: Equal.sym(D.ResultOp,D.write_se(D.row_is_valid(table,D.Row{key,fields}),collection,before,D.insert_row(rows,D.Row{key,fields})),D.FailureData{},Equal.cong(Bool,D.ResultOp,b => D.write_se(b,collection,before,D.insert_row(rows,D.Row{key,fields})),D.row_is_valid(table,D.Row{key,fields}),False{},a_schema_rejected_unicode_address_is_already_a_rejected_full_row(table,key,fields,actual)))
    case True{}:
      %Equal.sym(Maybe<&2,D.SchemaTable>,D.schema_collection(collection,schema),Some{table},schema_found) : {D.operate_resolved(D.DefineRow{collection,key,fields},D.resolve_parts(_,D.rows_collection(collection,before)),before) == D.write_se(D.row_is_valid(table,D.Row{key,fields}),collection,before,D.insert_row(rows,D.Row{key,fields})) : D.ResultOp}
      %Equal.sym(Maybe<&2,List<&2,D.Row>>,D.rows_collection(collection,before),Some{rows},rows_found) : {D.operate_resolved(D.DefineRow{collection,key,fields},D.resolve_parts(Some{table},_),before) == D.write_se(D.row_is_valid(table,D.Row{key,fields}),collection,before,D.insert_row(rows,D.Row{key,fields})) : D.ResultOp}
      {==}

law a_real_full_row_write_on_known_inputs_is_exactly_its_schema_validator_choice:
  for +schema: D.Schema
  for +before: D.State
  for +collection: D.Collection
  for +table: D.SchemaTable
  for +rows: List<&2,D.Row>
  for +key: String
  for +fields: List<&2,D.Field>
  for schema_found: {D.schema_collection(collection,schema) == Some{table} : Maybe<&2,D.SchemaTable>}
  for rows_found: {D.rows_collection(collection,before) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  {D.operate(schema,before,D.DefineRow{collection,key,fields}) == D.write_se(D.row_is_valid(table,D.Row{key,fields}),collection,before,D.insert_row(rows,D.Row{key,fields})) : D.ResultOp}
def a_real_full_row_write_on_known_inputs_is_exactly_its_schema_validator_choice(schema,before,collection,table,rows,key,fields,schema_found,rows_found):
  known_address_case(D.unicode_valid(key),schema,before,collection,table,rows,key,fields,{==},schema_found,rows_found)
