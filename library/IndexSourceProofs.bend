# Whole scan correctness against an independent complete INPUT source table.
# Unique keys prevent repeated first-row lookup aliasing; Unicode addresses
# prevent primitive address errors. Encoded query matching is literal parts
# equality by SourceContent. No completed scan/outcome is a premise.
import Base
import ./IndexSourceRows.bend as Source
import ./IndexSourceContent.bend as Content
import ./IndexSourceProjection.bend as Projection
import ./IndexEntryProofs.bend as Entry
import ./IndexScanModel.bend as M
import ./IndexScanMapProofs.bend as Map
import ./IndexScanProofs.bend as Scan
import ./QueryReadTrace.bend as History
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../contract/Semantics.bend as S
import ./Index.bend as Index
import ./Key.bend as Key
import ./Sequence.bend as Sequence
import ../src/Termination.bend as T

law actual_source_table_enumeration_is_every_original_source_key_in_order:
  for +entries: List<&2,Source.SourceEntry>
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +table_name: String
  for schema_found: {D.schema_collection(collection,schema) == Some{Entry.schema(table_name)} : Maybe<&2,D.SchemaTable>}
  for rows_found: {D.rows_collection(collection,state) == Some{Source.rows(entries)} : Maybe<&2,List<&2,D.Row>>}
  {D.operate(schema,state,D.EnumerateKeys{collection}) == D.Observed{D.Keys{Source.keys(entries)}} : D.ResultOp}
def actual_source_table_enumeration_is_every_original_source_key_in_order(entries,schema,state,collection,table_name,schema_found,rows_found):
  %Equal.sym(Maybe<&2,D.SchemaTable>,D.schema_collection(collection,schema),Some{Entry.schema(table_name)},schema_found) : {D.operate_resolved(D.EnumerateKeys{collection},D.resolve_parts(_,D.rows_collection(collection,state)),state) == D.Observed{D.Keys{Source.keys(entries)}} : D.ResultOp}
  %Equal.sym(Maybe<&2,List<&2,D.Row>>,D.rows_collection(collection,state),Some{Source.rows(entries)},rows_found) : {D.operate_resolved(D.EnumerateKeys{collection},D.resolve_parts(Some{Entry.schema(table_name)},_),state) == D.Observed{D.Keys{Source.keys(entries)}} : D.ResultOp}
  Equal.cong(List<&2,String>,D.ResultOp,keys => D.Observed{D.Keys{keys}},D.keys_rows(Source.rows(entries)),Source.keys(entries),Source.independent_source_keys_are_exactly_the_actual_row_enumeration_order(entries))

law actual_scan_of_a_unique_unicode_addressed_source_table_has_exact_independent_contents_and_history:
  for +entries: List<&2,Source.SourceEntry>
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +table_name: String
  for +parts: List<&2,String>
  for +remaining: Nat
  for -done: D.Value -> S.Action
  for +history: List<&2,S.OperationEvent>
  for +unique: {Source.unique(entries) == True{} : Bool}
  for +unicode: {Source.unicode_keys(entries) == True{} : Bool}
  for +schema_found: {D.schema_collection(collection,schema) == Some{Entry.schema(table_name)} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(collection,state) == Some{Source.rows(entries)} : Maybe<&2,List<&2,D.Row>>}
  {T.observe(1n+M.depth(Source.keys(entries),remaining),Index.scan_equal(collection,parts,done),schema,state,history) == T.observe(1n+remaining,done(Sequence.values(Content.targets(entries,Key.encode(parts)))),schema,state,History.append_events(Content.events(entries,collection),S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Reading{D.Keys{Source.keys(entries)}}}))) : S.Trace}
def actual_scan_of_a_unique_unicode_addressed_source_table_has_exact_independent_contents_and_history(entries,schema,state,collection,table_name,parts,remaining,done,history,unique,unicode,schema_found,rows_found):
  Equal.trans(S.Trace,T.observe(1n+M.depth(Source.keys(entries),remaining),Index.scan_equal(collection,parts,done),schema,state,history),Map.finish(M.plan(Source.keys(entries),schema,state,collection,Key.encode(parts)),remaining,schema,state,done,S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Reading{D.Keys{Source.keys(entries)}}})),T.observe(1n+remaining,done(Sequence.values(Content.targets(entries,Key.encode(parts)))),schema,state,History.append_events(Content.events(entries,collection),S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Reading{D.Keys{Source.keys(entries)}}}))),Scan.result_case(D.Observed{D.Keys{Source.keys(entries)}},schema,state,collection,parts,remaining,done,history,actual_source_table_enumeration_is_every_original_source_key_in_order(entries,schema,state,collection,table_name,schema_found,rows_found),Unit{}),Equal.cong(M.MapPlan,S.Trace,plan => Map.finish(plan,remaining,schema,state,done,S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Reading{D.Keys{Source.keys(entries)}}})),M.plan(Source.keys(entries),schema,state,collection,Key.encode(parts)),M.ScanYield{Content.targets(entries,Key.encode(parts)),Content.events(entries,collection)},Content.actual_source_table_plan_has_complete_ordered_matching_contents_and_all_reads(entries,schema,state,collection,table_name,Key.encode(parts),unique,unicode,schema_found,rows_found)))


def finish(value: D.Value) -> S.Action: S.Finish{value}

law closed_actual_source_scan_has_exact_indexed_contents_multiplicity_and_complete_history:
  for +entries: List<&2,Source.SourceEntry>
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +table_name: String
  for +parts: List<&2,String>
  for +history: List<&2,S.OperationEvent>
  for +unique: {Source.unique(entries) == True{} : Bool}
  for +unicode: {Source.unicode_keys(entries) == True{} : Bool}
  for +schema_found: {D.schema_collection(collection,schema) == Some{Entry.schema(table_name)} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(collection,state) == Some{Source.rows(entries)} : Maybe<&2,List<&2,D.Row>>}
  L.E<{T.observe(1n+M.depth(Source.keys(entries),0n),Index.scan_equal(collection,parts,finish),schema,state,history) == S.Final{state,History.append_events(Content.events(entries,collection),S.append(history,S.OperationEvent{D.EnumerateKeys{collection},S.Reading{D.Keys{Source.keys(entries)}}})),S.Response{S.Success{},Sequence.values(Content.targets(entries,Key.encode(parts)))}} : S.Trace},Projection.Meaning(parts,entries,Content.targets(entries,Key.encode(parts)))>
def closed_actual_source_scan_has_exact_indexed_contents_multiplicity_and_complete_history(entries,schema,state,collection,table_name,parts,history,unique,unicode,schema_found,rows_found):
  L.Both{actual_scan_of_a_unique_unicode_addressed_source_table_has_exact_independent_contents_and_history(entries,schema,state,collection,table_name,parts,0n,finish,history,unique,unicode,schema_found,rows_found),Projection.independent_source_projection_has_exact_contents_multiplicity_and_original_index_meaning(parts,entries)}

law complete_source_cell_history_contains_exactly_two_reads_per_original_entry:
  for +entries: List<&2,Source.SourceEntry>
  for +collection: D.Collection
  {List.length(&2,S.OperationEvent,Content.events(entries,collection)) == M.owned(Source.keys(entries)) : Nat}
def complete_source_cell_history_contains_exactly_two_reads_per_original_entry(entries,collection):
  match entries:
    case Nil{}: {==}
    case Con{Source.SourceEntry{key,parts,target},+tail}: Equal.cong(Nat,Nat,n => 2n+n,List.length(&2,S.OperationEvent,Content.events(tail,collection)),M.owned(Source.keys(tail)),complete_source_cell_history_contains_exactly_two_reads_per_original_entry(tail,collection))
