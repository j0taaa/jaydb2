# A finite spine of LOCAL read-plan equalities is DERIVED from independent
# input table contents, Unicode addresses, distinct keys and source indices.
# No visitor/primitive output or completed scan is a public assumption.
import Base
import ./IndexSourceRows.bend as Source
import ./IndexSourceVisit.bend as Visit
import ./IndexEntryProofs.bend as Entry
import ./IndexVisitProofs.bend as Actual
import ../contract/Data.bend as D
import ./Key.bend as Key
import ./ValueScalarProofs.bend as Pair

def Ready(entries: List<&2,Source.SourceEntry>,+schema: D.Schema,+state: D.State,+collection: D.Collection,+query: String) -> Data:
  match entries:
    case Nil{}: Unit
    case Con{+head,tail}: Pair.Both<{Actual.plan(schema,state,collection,Source.key(head),query) == Actual.VisitYield{Bool.pick(Maybe<&2,D.Value>,String.eq(query,Key.encode(Source.parts(head))),Some{D.VText{Source.target(head)}},None{}),Visit.events(collection,head)} : Actual.VisitPlan},Ready(tail,schema,state,collection,query)>

def certify_suffix(+global: List<&2,Source.SourceEntry>,+entries: List<&2,Source.SourceEntry>,+offset: Nat,+schema: D.Schema,+state: D.State,+collection: D.Collection,+table_name: String,+query: String,+unique: {Source.unique(global) == True{} : Bool},+unicode: {Source.unicode_keys(global) == True{} : Bool},+schema_found: {D.schema_collection(collection,schema) == Some{Entry.schema(table_name)} : Maybe<&2,D.SchemaTable>},+rows_found: {D.rows_collection(collection,state) == Some{Source.rows(global)} : Maybe<&2,List<&2,D.Row>>},+suffix: {Source.drop(global,offset) == entries : List<&2,Source.SourceEntry>}) -> Ready(entries,schema,state,collection,query):
  match entries:
    case Nil{}: Unit{}
    case Con{+head,+tail}:
      +present = Equal.trans(Maybe<&2,Source.SourceEntry>,Source.at(global,offset),Source.at(Source.drop(global,offset),0n),Some{head},Source.input_index_lookup_is_exactly_the_head_of_its_input_suffix(global,offset),Equal.cong(List<&2,Source.SourceEntry>,Maybe<&2,Source.SourceEntry>,items => Source.at(items,0n),Source.drop(global,offset),Con{head,tail},suffix))
      Pair.Both{Visit.actual_source_entry_visitor_keeps_exactly_encoded_part_matches_and_both_reads(schema,state,collection,table_name,Source.rows(global),head,query,Source.an_indexed_source_key_is_unicode_valid_when_all_source_keys_are(global,offset,head,unicode,present),schema_found,rows_found,Source.every_unique_source_occurrence_has_its_exact_key_lookup_and_complete_row_payload(global,offset,head,unique,present)),certify_suffix(global,tail,1n+offset,schema,state,collection,table_name,query,unique,unicode,schema_found,rows_found,Equal.trans(List<&2,Source.SourceEntry>,Source.drop(global,1n+offset),Source.rest(Source.drop(global,offset)),tail,Source.advancing_an_input_index_is_exactly_dropping_its_current_suffix_head(global,offset),Equal.cong(List<&2,Source.SourceEntry>,List<&2,Source.SourceEntry>,Source.rest,Source.drop(global,offset),Con{head,tail},suffix)))}

law every_independent_source_entry_has_its_exact_actual_two_cell_visit_plan:
  for +entries: List<&2,Source.SourceEntry>
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +table_name: String
  for +query: String
  for +unique: {Source.unique(entries) == True{} : Bool}
  for +unicode: {Source.unicode_keys(entries) == True{} : Bool}
  for +schema_found: {D.schema_collection(collection,schema) == Some{Entry.schema(table_name)} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(collection,state) == Some{Source.rows(entries)} : Maybe<&2,List<&2,D.Row>>}
  Ready(entries,schema,state,collection,query)
def every_independent_source_entry_has_its_exact_actual_two_cell_visit_plan(entries,schema,state,collection,table_name,query,unique,unicode,schema_found,rows_found):
  certify_suffix(entries,entries,0n,schema,state,collection,table_name,query,unique,unicode,schema_found,rows_found,Source.dropping_zero_input_entries_is_identity(entries))
