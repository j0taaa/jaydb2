# Unique-claim mathematical input meaning. Key occupancy is derived from a
# real original source position (with distinct keys); absence excludes the
# key from EVERY original row. No operation result or callback outcome premise.
import Base
import ./IndexKeyViewProofs.bend as Views
import ./IndexEntryProofs.bend as Entry
import ./IndexSourceRows.bend as Source
import ./MutationPrimitiveProofs.bend as Primitive
import ./MutationWriteTrace.bend as Write
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Index.bend as I
import ./Key.bend as K
import ./Mutation.bend as M
import ./Action.bend as A
import ./Proofs.bend as Event
import ../src/Termination.bend as T

def existence(+collection: D.Collection,parts: List<&2,String>) -> D.Operation: D.ViewExistence{collection,K.encode(parts)}
def write(+collection: D.Collection,+parts: List<&2,String>,target: String) -> D.Operation: D.DefineRow{collection,K.encode(parts),Entry.fields(I.unique(parts,target))}
def occupied_events(collection: D.Collection,parts: List<&2,String>,before: List<&2,S.OperationEvent>) -> List<&2,S.OperationEvent>:
  S.append(before,S.OperationEvent{existence(collection,parts),S.Reading{D.Existence{True{}}}})
def new_state(collection: D.Collection,before: D.State,rows: List<&2,D.Row>,parts: List<&2,String>,target: String) -> D.State:
  D.swap_collection(collection,before,D.insert_row(rows,I.unique(parts,target)))
def new_events(+collection: D.Collection,+parts: List<&2,String>,target: String,before: List<&2,S.OperationEvent>) -> List<&2,S.OperationEvent>:
  S.append(S.append(before,S.OperationEvent{existence(collection,parts),S.Reading{D.Existence{False{}}}}),S.OperationEvent{write(collection,parts,target),S.Write{}})

law an_occupied_input_key_returns_false_without_a_claim_write_even_for_a_different_target:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +table: D.SchemaTable
  for +rows: List<&2,D.Row>
  for +parts: List<&2,String>
  for +target: String
  for +present_row: D.Row
  for +remaining: Nat
  for -done: Bool -> S.Action
  for +history: List<&2,S.OperationEvent>
  for address: {D.unicode_valid(K.encode(parts)) == True{} : Bool}
  for schema_found: {D.schema_collection(collection,schema) == Some{table} : Maybe<&2,D.SchemaTable>}
  for rows_found: {D.rows_collection(collection,state) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for found: {D.find_row(rows,K.encode(parts)) == Some{present_row} : Maybe<&2,D.Row>}
  {T.observe(3n+remaining,I.claim(collection,parts,target,done),schema,state,history) == T.observe(2n+remaining,done(False{}),schema,state,occupied_events(collection,parts,history)) : S.Trace}
def an_occupied_input_key_returns_false_without_a_claim_write_even_for_a_different_target(schema,state,collection,table,rows,parts,target,present_row,remaining,done,history,address,schema_found,rows_found,found):
  Event.read_continuation(2n+remaining,schema,state,existence(collection,parts),D.Existence{True{}},M.inserted(collection,I.unique(parts,target),done),history,Views.a_present_input_row_has_exact_occupied_existence(schema,state,collection,table,rows,K.encode(parts),present_row,address,schema_found,rows_found,found))

law an_occupied_unique_source_occurrence_returns_false_with_one_exact_read:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +table: D.SchemaTable
  for +entries: List<&2,Source.SourceEntry>
  for +position: Nat
  for +parts: List<&2,String>
  for +stored_target: String
  for +claimed_target: String
  for +remaining: Nat
  for -done: Bool -> S.Action
  for +history: List<&2,S.OperationEvent>
  for valid_parts: {Entry.parts_valid(parts) == True{} : Bool}
  for schema_found: {D.schema_collection(collection,schema) == Some{table} : Maybe<&2,D.SchemaTable>}
  for rows_found: {D.rows_collection(collection,state) == Some{Source.rows(entries)} : Maybe<&2,List<&2,D.Row>>}
  for unique: {Source.unique(entries) == True{} : Bool}
  for present: {Source.at(entries,position) == Some{Source.SourceEntry{K.encode(parts),parts,stored_target}} : Maybe<&2,Source.SourceEntry>}
  {T.observe(3n+remaining,I.claim(collection,parts,claimed_target,done),schema,state,history) == T.observe(2n+remaining,done(False{}),schema,state,occupied_events(collection,parts,history)) : S.Trace}
def an_occupied_unique_source_occurrence_returns_false_with_one_exact_read(schema,state,collection,table,entries,position,parts,stored_target,claimed_target,remaining,done,history,valid_parts,schema_found,rows_found,unique,present):
  an_occupied_input_key_returns_false_without_a_claim_write_even_for_a_different_target(schema,state,collection,table,Source.rows(entries),parts,claimed_target,I.unique(parts,stored_target),remaining,done,history,Entry.encoding_valid_parts_always_produces_a_valid_unicode_row_key(parts,valid_parts),schema_found,rows_found,Source.every_unique_source_occurrence_has_its_exact_key_lookup_and_complete_row_payload(entries,position,Source.SourceEntry{K.encode(parts),parts,stored_target},unique,present))

law a_fully_absent_valid_unique_key_writes_the_complete_entry_then_returns_true:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +table_name: String
  for +rows: List<&2,D.Row>
  for +parts: List<&2,String>
  for +target: String
  for +remaining: Nat
  for -done: Bool -> S.Action
  for +history: List<&2,S.OperationEvent>
  for +valid_parts: {Entry.parts_valid(parts) == True{} : Bool}
  for +valid_target: {D.unicode_valid(target) == True{} : Bool}
  for +schema_found: {D.schema_collection(collection,schema) == Some{Entry.schema(table_name)} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(collection,state) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for absent: Views.Absent(K.encode(parts),rows)
  {T.observe(3n+remaining,I.claim(collection,parts,target,done),schema,state,history) == T.observe(1n+remaining,done(True{}),schema,new_state(collection,state,rows,parts,target),new_events(collection,parts,target,history)) : S.Trace}
def a_fully_absent_valid_unique_key_writes_the_complete_entry_then_returns_true(schema,state,collection,table_name,rows,parts,target,remaining,done,history,valid_parts,valid_target,schema_found,rows_found,absent):
  Equal.trans(S.Trace,T.observe(3n+remaining,I.claim(collection,parts,target,done),schema,state,history),T.observe(2n+remaining,M.inserted(collection,I.unique(parts,target),done,S.Datum{D.Existence{False{}}}),schema,state,S.append(history,S.OperationEvent{existence(collection,parts),S.Reading{D.Existence{False{}}}})),T.observe(1n+remaining,done(True{}),schema,new_state(collection,state,rows,parts,target),new_events(collection,parts,target,history)),Event.read_continuation(2n+remaining,schema,state,existence(collection,parts),D.Existence{False{}},M.inserted(collection,I.unique(parts,target),done),history,Views.a_key_excluded_from_every_input_row_has_exact_absent_existence(schema,state,collection,Entry.schema(table_name),rows,K.encode(parts),Entry.encoding_valid_parts_always_produces_a_valid_unicode_row_key(parts,valid_parts),schema_found,rows_found,absent)),Write.real_changed_primitive_retains_the_write_and_continues_in_its_actual_new_state(1n+remaining,schema,state,new_state(collection,state,rows,parts,target),write(collection,parts,target),r => A.written(done(True{}),r),S.append(history,S.OperationEvent{existence(collection,parts),S.Reading{D.Existence{False{}}}}),Primitive.defining_a_valid_row_in_an_existing_collection_performs_the_exact_upsert(schema,state,collection,Entry.schema(table_name),rows,K.encode(parts),Entry.fields(I.unique(parts,target)),schema_found,rows_found,Entry.valid_unique_entries_always_fit_the_required_index_schema(table_name,parts,target,valid_parts,valid_target))))
