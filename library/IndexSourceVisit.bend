# Independent INPUT-table domains yield actual primitive observations, then
# exact source visitor output. No primitive/output/trace equation is assumed.
import Base
import ./IndexSourceRows.bend as Source
import ./IndexEntryProofs.bend as Entry
import ./IndexVisitProofs.bend as Visit
import ./QueryReadPlan.bend as ReadPlan
import ./QuerySelectionModel.bend as Selection
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Key.bend as Key

law actual_target_read_of_a_source_entry_has_exact_input_payload:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +table_name: String
  for +rows: List<&2,D.Row>
  for +key: String
  for +parts: List<&2,String>
  for +target: String
  for address: {D.unicode_valid(key) == True{} : Bool}
  for schema_found: {D.schema_collection(collection,schema) == Some{Entry.schema(table_name)} : Maybe<&2,D.SchemaTable>}
  for rows_found: {D.rows_collection(collection,state) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for row_found: {D.find_row(rows,key) == Some{Source.raw(Source.SourceEntry{key,parts,target})} : Maybe<&2,D.Row>}
  {D.operate(schema,state,D.ReadCell{collection,key,"target"}) == D.Observed{D.Cell{D.VText{target}}} : D.ResultOp}
def actual_target_read_of_a_source_entry_has_exact_input_payload(schema,state,collection,table_name,rows,key,parts,target,address,schema_found,rows_found,row_found):
  %Equal.sym(Bool,D.unicode_valid(key),True{},address) : {D.operate_address(_,schema,state,D.ReadCell{collection,key,"target"}) == D.Observed{D.Cell{D.VText{target}}} : D.ResultOp}
  %Equal.sym(Maybe<&2,D.SchemaTable>,D.schema_collection(collection,schema),Some{Entry.schema(table_name)},schema_found) : {D.operate_resolved(D.ReadCell{collection,key,"target"},D.resolve_parts(_,D.rows_collection(collection,state)),state) == D.Observed{D.Cell{D.VText{target}}} : D.ResultOp}
  %Equal.sym(Maybe<&2,List<&2,D.Row>>,D.rows_collection(collection,state),Some{rows},rows_found) : {D.operate_resolved(D.ReadCell{collection,key,"target"},D.resolve_parts(Some{Entry.schema(table_name)},_),state) == D.Observed{D.Cell{D.VText{target}}} : D.ResultOp}
  %Equal.sym(Maybe<&2,D.Row>,D.find_row(rows,key),Some{Source.raw(Source.SourceEntry{key,parts,target})},row_found) : {D.read_row(_,"target") == D.Observed{D.Cell{D.VText{target}}} : D.ResultOp}
  {==}

law actual_value_read_of_a_source_entry_has_exact_input_payload:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +table_name: String
  for +rows: List<&2,D.Row>
  for +key: String
  for +parts: List<&2,String>
  for +target: String
  for address: {D.unicode_valid(key) == True{} : Bool}
  for schema_found: {D.schema_collection(collection,schema) == Some{Entry.schema(table_name)} : Maybe<&2,D.SchemaTable>}
  for rows_found: {D.rows_collection(collection,state) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for row_found: {D.find_row(rows,key) == Some{Source.raw(Source.SourceEntry{key,parts,target})} : Maybe<&2,D.Row>}
  {D.operate(schema,state,D.ReadCell{collection,key,"value"}) == D.Observed{D.Cell{D.VText{Key.encode(parts)}}} : D.ResultOp}
def actual_value_read_of_a_source_entry_has_exact_input_payload(schema,state,collection,table_name,rows,key,parts,target,address,schema_found,rows_found,row_found):
  %Equal.sym(Bool,D.unicode_valid(key),True{},address) : {D.operate_address(_,schema,state,D.ReadCell{collection,key,"value"}) == D.Observed{D.Cell{D.VText{Key.encode(parts)}}} : D.ResultOp}
  %Equal.sym(Maybe<&2,D.SchemaTable>,D.schema_collection(collection,schema),Some{Entry.schema(table_name)},schema_found) : {D.operate_resolved(D.ReadCell{collection,key,"value"},D.resolve_parts(_,D.rows_collection(collection,state)),state) == D.Observed{D.Cell{D.VText{Key.encode(parts)}}} : D.ResultOp}
  %Equal.sym(Maybe<&2,List<&2,D.Row>>,D.rows_collection(collection,state),Some{rows},rows_found) : {D.operate_resolved(D.ReadCell{collection,key,"value"},D.resolve_parts(Some{Entry.schema(table_name)},_),state) == D.Observed{D.Cell{D.VText{Key.encode(parts)}}} : D.ResultOp}
  %Equal.sym(Maybe<&2,D.Row>,D.find_row(rows,key),Some{Source.raw(Source.SourceEntry{key,parts,target})},row_found) : {D.read_row(_,"value") == D.Observed{D.Cell{D.VText{Key.encode(parts)}}} : D.ResultOp}
  {==}

def events(+collection: D.Collection,entry: Source.SourceEntry) -> List<&2,S.OperationEvent>:
  match entry:
    case Source.SourceEntry{+key,parts,target}: [S.OperationEvent{D.ReadCell{collection,key,"target"},S.Reading{D.Cell{D.VText{target}}}},S.OperationEvent{D.ReadCell{collection,key,"value"},S.Reading{D.Cell{D.VText{Key.encode(parts)}}}}]

law actual_source_entry_visitor_keeps_exactly_encoded_part_matches_and_both_reads:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +table_name: String
  for +rows: List<&2,D.Row>
  for +entry: Source.SourceEntry
  for +query: String
  for +address: {D.unicode_valid(Source.key(entry)) == True{} : Bool}
  for +schema_found: {D.schema_collection(collection,schema) == Some{Entry.schema(table_name)} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(collection,state) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for +row_found: {D.find_row(rows,Source.key(entry)) == Some{Source.raw(entry)} : Maybe<&2,D.Row>}
  {Visit.plan(schema,state,collection,Source.key(entry),query) == Visit.VisitYield{Bool.pick(Maybe<&2,D.Value>,String.eq(query,Key.encode(Source.parts(entry))),Some{D.VText{Source.target(entry)}},None{}),events(collection,entry)} : Visit.VisitPlan}
def actual_source_entry_visitor_keeps_exactly_encoded_part_matches_and_both_reads(schema,state,collection,table_name,rows,entry,query,address,schema_found,rows_found,row_found):
  match entry:
    case Source.SourceEntry{+key,+parts,+target}:
      +read_target = actual_target_read_of_a_source_entry_has_exact_input_payload(schema,state,collection,table_name,rows,key,parts,target,address,schema_found,rows_found,row_found)
      +read_value = actual_value_read_of_a_source_entry_has_exact_input_payload(schema,state,collection,table_name,rows,key,parts,target,address,schema_found,rows_found,row_found)
      %Equal.sym(D.ResultOp,D.operate(schema,state,D.ReadCell{collection,key,"target"}),D.Observed{D.Cell{D.VText{target}}},read_target) :
        {Visit.from_read_plan(query,ReadPlan.extend(D.ReadCell{collection,key,"target"},"target",_,ReadPlan.plan(schema,state,collection,key,["value"]))) == Visit.VisitYield{Bool.pick(Maybe<&2,D.Value>,String.eq(query,Key.encode(parts)),Some{D.VText{target}},None{}),events(collection,Source.SourceEntry{key,parts,target})} : Visit.VisitPlan}
      %Equal.sym(D.ResultOp,D.operate(schema,state,D.ReadCell{collection,key,"value"}),D.Observed{D.Cell{D.VText{Key.encode(parts)}}},read_value) :
        {Visit.from_read_plan(query,ReadPlan.extend(D.ReadCell{collection,key,"target"},"target",D.Observed{D.Cell{D.VText{target}}},ReadPlan.extend(D.ReadCell{collection,key,"value"},"value",_,ReadPlan.ReadsReady{Selection.Clear{},D.VRecordEmpty{},Nil{}}))) == Visit.VisitYield{Bool.pick(Maybe<&2,D.Value>,String.eq(query,Key.encode(parts)),Some{D.VText{target}},None{}),events(collection,Source.SourceEntry{key,parts,target})} : Visit.VisitPlan}
      {==}
