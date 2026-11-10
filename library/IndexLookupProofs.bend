# Input-content meaning of actual unique lookup. Every present payload comes
# from the exact original source position; absence excludes all input keys.
# These are local facts, never a whole-table consistency conclusion.
import Base
import ./IndexKeyViewProofs.bend as Views
import ./IndexEntryProofs.bend as Entry
import ./IndexSourceRows.bend as Source
import ./IndexSourceVisit.bend as ReadSource
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Index.bend as I
import ./Key.bend as K
import ./Query.bend as Q
import ./Proofs.bend as Event
import ../src/Termination.bend as T

def read(collection: D.Collection,parts: List<&2,String>) -> D.Operation: D.ReadCell{collection,K.encode(parts),"target"}
def record(target: String) -> D.Value: D.VRecord{"target",D.VText{target},D.VRecordEmpty{}}

law an_indexed_unique_source_occurrence_looks_up_exactly_its_target_with_one_read:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +table_name: String
  for +entries: List<&2,Source.SourceEntry>
  for +position: Nat
  for +parts: List<&2,String>
  for +target: String
  for +remaining: Nat
  for -done: Q.Selection -> S.Action
  for +history: List<&2,S.OperationEvent>
  for valid_parts: {Entry.parts_valid(parts) == True{} : Bool}
  for schema_found: {D.schema_collection(collection,schema) == Some{Entry.schema(table_name)} : Maybe<&2,D.SchemaTable>}
  for rows_found: {D.rows_collection(collection,state) == Some{Source.rows(entries)} : Maybe<&2,List<&2,D.Row>>}
  for unique: {Source.unique(entries) == True{} : Bool}
  for present: {Source.at(entries,position) == Some{Source.SourceEntry{K.encode(parts),parts,target}} : Maybe<&2,Source.SourceEntry>}
  {T.observe(1n+remaining,I.lookup(collection,parts,done),schema,state,history) == T.observe(remaining,done(Q.Selected{record(target)}),schema,state,S.append(history,S.OperationEvent{read(collection,parts),S.Reading{D.Cell{D.VText{target}}}})) : S.Trace}
def an_indexed_unique_source_occurrence_looks_up_exactly_its_target_with_one_read(schema,state,collection,table_name,entries,position,parts,target,remaining,done,history,valid_parts,schema_found,rows_found,unique,present):
  Event.read_continuation(remaining,schema,state,read(collection,parts),D.Cell{D.VText{target}},Q.received("target",done,next => Q.read_fields(collection,K.encode(parts),Nil{},next)),history,ReadSource.actual_target_read_of_a_source_entry_has_exact_input_payload(schema,state,collection,table_name,Source.rows(entries),K.encode(parts),parts,target,Entry.encoding_valid_parts_always_produces_a_valid_unicode_row_key(parts,valid_parts),schema_found,rows_found,Source.every_unique_source_occurrence_has_its_exact_key_lookup_and_complete_row_payload(entries,position,Source.SourceEntry{K.encode(parts),parts,target},unique,present)))

law a_key_absent_from_every_original_row_looks_up_as_missing_after_one_read:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +table_name: String
  for +rows: List<&2,D.Row>
  for +parts: List<&2,String>
  for +remaining: Nat
  for -done: Q.Selection -> S.Action
  for +history: List<&2,S.OperationEvent>
  for valid_parts: {Entry.parts_valid(parts) == True{} : Bool}
  for schema_found: {D.schema_collection(collection,schema) == Some{Entry.schema(table_name)} : Maybe<&2,D.SchemaTable>}
  for rows_found: {D.rows_collection(collection,state) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for absent: Views.Absent(K.encode(parts),rows)
  {T.observe(1n+remaining,I.lookup(collection,parts,done),schema,state,history) == T.observe(remaining,done(Q.MissingRow{}),schema,state,S.append(history,S.OperationEvent{read(collection,parts),S.Reading{D.RowAbsent{}}})) : S.Trace}
def a_key_absent_from_every_original_row_looks_up_as_missing_after_one_read(schema,state,collection,table_name,rows,parts,remaining,done,history,valid_parts,schema_found,rows_found,absent):
  Event.read_continuation(remaining,schema,state,read(collection,parts),D.RowAbsent{},Q.received("target",done,next => Q.read_fields(collection,K.encode(parts),Nil{},next)),history,Views.an_excluded_input_key_has_exact_row_absence_for_the_declared_target_cell(schema,state,collection,table_name,rows,K.encode(parts),Entry.encoding_valid_parts_always_produces_a_valid_unicode_row_key(parts,valid_parts),schema_found,rows_found,absent))
