# COMPLETE actual primitive source linkage for arbitrary schemas/states/keys.
# Every Changed result carries the ORIGINAL input row view and exact structural
# row update. Failure needs no callback; an Observed write result is impossible.
import Base
import ../contract/Data.bend as D
import ./ValueScalarProofs.bend as Pair

type Transform is Data:
  RowUpsert{key: String,fields: List<&2,D.Field>}
  RowDelete{key: String}
def operation(collection: D.Collection,transform: Transform) -> D.Operation:
  match transform:
    case RowUpsert{key,fields}: D.DefineRow{collection,key,fields}
    case RowDelete{key}: D.RemoveRow{collection,key}
def apply(transform: Transform,rows: List<&2,D.Row>) -> List<&2,D.Row>:
  match transform:
    case RowUpsert{key,fields}: D.insert_row(rows,D.Row{key,fields})
    case RowDelete{key}: D.remove_row(rows,key)

def Shape(+before: D.State,+collection: D.Collection,+transform: Transform,result: D.ResultOp) -> Data:
  match result:
    case D.FailureData{}: Unit
    case D.Observed{observation}: {False{} == True{} : Bool}
    case D.Changed{working}: Sigma<&2,&2,List<&2,D.Row>,rows => Pair.Both<{D.rows_collection(collection,before) == Some{rows} : Maybe<&2,List<&2,D.Row>>},{working == D.swap_collection(collection,before,apply(transform,rows)) : D.State}>>

def valid_case(valid: Bool,+before: D.State,+collection: D.Collection,+rows: List<&2,D.Row>,+key: String,+fields: List<&2,D.Field>,found: {D.rows_collection(collection,before) == Some{rows} : Maybe<&2,List<&2,D.Row>>}) -> Shape(before,collection,RowUpsert{key,fields},D.write_se(valid,collection,before,D.insert_row(rows,D.Row{key,fields}))):
  match valid:
    case False{}: Unit{}
    case True{}: (rows,Pair.Both{found,{==}})

def missing(transform: Transform,+before: D.State,+collection: D.Collection) -> Shape(before,collection,transform,D.operate_resolved(operation(collection,transform),None{},before)):
  match transform:
    case RowUpsert{key,fields}: Unit{}
    case RowDelete{key}: Unit{}

def present(+transform: Transform,+before: D.State,+collection: D.Collection,+table: D.SchemaTable,+rows: List<&2,D.Row>,found: {D.rows_collection(collection,before) == Some{rows} : Maybe<&2,List<&2,D.Row>>}) -> Shape(before,collection,transform,D.operate_resolved(operation(collection,transform),Some{D.Resolved{table,rows}},before)):
  match transform:
    case RowUpsert{+key,+fields}: valid_case(D.row_is_valid(table,D.Row{key,fields}),before,collection,rows,key,fields,found)
    case RowDelete{key}: (rows,Pair.Both{found,{==}})

def resolved(schema_view: Maybe<&2,D.SchemaTable>,rows_view: Maybe<&2,List<&2,D.Row>>,+transform: Transform,+before: D.State,+collection: D.Collection,actual_rows: {D.rows_collection(collection,before) == rows_view : Maybe<&2,List<&2,D.Row>>}) -> Shape(before,collection,transform,D.operate_resolved(operation(collection,transform),D.resolve_parts(schema_view,rows_view),before)):
  match schema_view rows_view:
    case Some{table} Some{rows}: present(transform,before,collection,table,rows,actual_rows)
    case None{} rows: missing(transform,before,collection)
    case Some{table} None{}: missing(transform,before,collection)

def true_address(transform: Transform,+schema: D.Schema,+before: D.State,+collection: D.Collection) -> Shape(before,collection,transform,D.operate_address(True{},schema,before,operation(collection,transform))):
  match transform:
    case RowUpsert{+key,+fields}: resolved(D.schema_collection(collection,schema),D.rows_collection(collection,before),RowUpsert{key,fields},before,collection,{==})
    case RowDelete{+key}: resolved(D.schema_collection(collection,schema),D.rows_collection(collection,before),RowDelete{key},before,collection,{==})

def address(valid: Bool,+transform: Transform,+schema: D.Schema,+before: D.State,+collection: D.Collection) -> Shape(before,collection,transform,D.operate_address(valid,schema,before,operation(collection,transform))):
  match valid:
    case False{}: Unit{}
    case True{}: true_address(transform,schema,before,collection)

law actual_ordinary_row_transform_has_complete_input_state_shape_for_every_input:
  for +schema: D.Schema
  for +before: D.State
  for +collection: D.Collection
  for +transform: Transform
  Shape(before,collection,transform,D.operate(schema,before,operation(collection,transform)))
def actual_ordinary_row_transform_has_complete_input_state_shape_for_every_input(schema,before,collection,transform):
  match transform:
    case RowUpsert{+key,+fields}: address(D.unicode_valid(key),RowUpsert{key,fields},schema,before,collection)
    case RowDelete{+key}: address(D.unicode_valid(key),RowDelete{key},schema,before,collection)
