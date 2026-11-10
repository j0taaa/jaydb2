# Independent source projection: include each original entry's target iff its
# STORED encoded parts equal the query. Literal parts equality is separately
# proved equivalent; no duplicate target is removed and no key lookup defines
# this source-list specification.
import Base
import ./IndexSourceRows.bend as Source
import ./IndexSourceReadiness.bend as Ready
import ./IndexSourceVisit.bend as Visit
import ./IndexEntryProofs.bend as Entry
import ./IndexScanModel.bend as Actual
import ./IndexVisitProofs.bend as VisitPlan
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Key.bend as Key
import ./Sequence.bend as Sequence
import ./ValueScalarProofs.bend as Pair
import ../proof/Foundations.bend as F
import ../proof/Orders.bend as O

def matches(+query: String,entry: Source.SourceEntry) -> Bool:
  String.eq(query,Key.encode(Source.parts(entry)))

def targets(entries: List<&2,Source.SourceEntry>,+query: String) -> List<&2,D.Value>:
  match entries:
    case Nil{}: Nil{}
    case Con{+head,tail}: Sequence.include(matches(query,head),D.VText{Source.target(head)},targets(tail,query))

def events(entries: List<&2,Source.SourceEntry>,+collection: D.Collection) -> List<&2,S.OperationEvent>:
  match entries:
    case Nil{}: Nil{}
    case Con{head,tail}: Actual.events(Visit.events(collection,head),events(tail,collection))

def PartsEquality(+query: List<&2,String>,+entry: Source.SourceEntry,equal: Bool) -> Type:
  match equal:
    case True{}: {query == Source.parts(entry) : List<&2,String>}
    case False{}: {query == Source.parts(entry) : List<&2,String>} -> Empty

def literal_parts_case(+query: List<&2,String>,+entry: Source.SourceEntry,equal: Bool,actual: {matches(Key.encode(query),entry) == equal : Bool}) -> PartsEquality(query,entry,equal):
  match equal:
    case True{}: Key.injective(query,Source.parts(entry),O.string_equal(Key.encode(query),Key.encode(Source.parts(entry)),actual))
    case False{}:
      same => F.false_negative_true(Equal.trans(Bool,False{},matches(Key.encode(query),entry),True{},Equal.sym(Bool,matches(Key.encode(query),entry),False{},actual),Equal.trans(Bool,matches(Key.encode(query),entry),String.eq(Key.encode(query),Key.encode(query)),True{},Equal.cong(String,Bool,other => String.eq(Key.encode(query),other),Key.encode(Source.parts(entry)),Key.encode(query),Equal.sym(String,Key.encode(query),Key.encode(Source.parts(entry)),Equal.cong(List<&2,String>,String,Key.encode,query,Source.parts(entry),same))),O.string_eq_refl(Key.encode(query)))))

law encoded_source_matching_is_exactly_literal_complete_parts_equality:
  for +query: List<&2,String>
  for +entry: Source.SourceEntry
  PartsEquality(query,entry,matches(Key.encode(query),entry))
def encoded_source_matching_is_exactly_literal_complete_parts_equality(query,entry): literal_parts_case(query,entry,matches(Key.encode(query),entry),{==})

law optional_visitor_payload_is_exactly_independent_source_inclusion:
  for +equal: Bool
  for +entry: Source.SourceEntry
  for +tail_items: List<&2,D.Value>
  for +tail_events: List<&2,S.OperationEvent>
  for +collection: D.Collection
  {Actual.combine(VisitPlan.VisitYield{Bool.pick(Maybe<&2,D.Value>,equal,Some{D.VText{Source.target(entry)}},None{}),Visit.events(collection,entry)},Actual.ScanYield{tail_items,tail_events}) == Actual.ScanYield{Sequence.include(equal,D.VText{Source.target(entry)},tail_items),Actual.events(Visit.events(collection,entry),tail_events)} : Actual.MapPlan}
def optional_visitor_payload_is_exactly_independent_source_inclusion(equal,entry,tail_items,tail_events,collection):
  match equal:
    case True{}: {==}
    case False{}: {==}

# Internal derived finite certificates are consumed once. The public theorem
# below constructs them from complete INPUT rows/indices/schema, not outcomes.
law actual_map_plan_refines_independent_source_projection_from_local_certificates:
  for +entries: List<&2,Source.SourceEntry>
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +query: String
  for ready: Ready.Ready(entries,schema,state,collection,query)
  {Actual.plan(Source.keys(entries),schema,state,collection,query) == Actual.ScanYield{targets(entries,query),events(entries,collection)} : Actual.MapPlan}
def actual_map_plan_refines_independent_source_projection_from_local_certificates(entries,schema,state,collection,query,ready):
  match entries ready:
    case Nil{} Unit{}: {==}
    case Con{+head,+tail} Pair.Both{head_ready,tail_ready}:
      Equal.trans(Actual.MapPlan,Actual.plan(Source.keys(Con{head,tail}),schema,state,collection,query),Actual.combine(VisitPlan.VisitYield{Bool.pick(Maybe<&2,D.Value>,matches(query,head),Some{D.VText{Source.target(head)}},None{}),Visit.events(collection,head)},Actual.plan(Source.keys(tail),schema,state,collection,query)),Actual.ScanYield{targets(Con{head,tail},query),events(Con{head,tail},collection)},Equal.cong(VisitPlan.VisitPlan,Actual.MapPlan,visit => Actual.combine(visit,Actual.plan(Source.keys(tail),schema,state,collection,query)),VisitPlan.plan(schema,state,collection,Source.key(head),query),VisitPlan.VisitYield{Bool.pick(Maybe<&2,D.Value>,matches(query,head),Some{D.VText{Source.target(head)}},None{}),Visit.events(collection,head)},head_ready),Equal.trans(Actual.MapPlan,Actual.combine(VisitPlan.VisitYield{Bool.pick(Maybe<&2,D.Value>,matches(query,head),Some{D.VText{Source.target(head)}},None{}),Visit.events(collection,head)},Actual.plan(Source.keys(tail),schema,state,collection,query)),Actual.combine(VisitPlan.VisitYield{Bool.pick(Maybe<&2,D.Value>,matches(query,head),Some{D.VText{Source.target(head)}},None{}),Visit.events(collection,head)},Actual.ScanYield{targets(tail,query),events(tail,collection)}),Actual.ScanYield{targets(Con{head,tail},query),events(Con{head,tail},collection)},Equal.cong(Actual.MapPlan,Actual.MapPlan,rest => Actual.combine(VisitPlan.VisitYield{Bool.pick(Maybe<&2,D.Value>,matches(query,head),Some{D.VText{Source.target(head)}},None{}),Visit.events(collection,head)},rest),Actual.plan(Source.keys(tail),schema,state,collection,query),Actual.ScanYield{targets(tail,query),events(tail,collection)},actual_map_plan_refines_independent_source_projection_from_local_certificates(tail,schema,state,collection,query,tail_ready)),optional_visitor_payload_is_exactly_independent_source_inclusion(matches(query,head),head,targets(tail,query),events(tail,collection),collection)))

law actual_source_table_plan_has_complete_ordered_matching_contents_and_all_reads:
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
  {Actual.plan(Source.keys(entries),schema,state,collection,query) == Actual.ScanYield{targets(entries,query),events(entries,collection)} : Actual.MapPlan}
def actual_source_table_plan_has_complete_ordered_matching_contents_and_all_reads(entries,schema,state,collection,table_name,query,unique,unicode,schema_found,rows_found):
  actual_map_plan_refines_independent_source_projection_from_local_certificates(entries,schema,state,collection,query,Ready.every_independent_source_entry_has_its_exact_actual_two_cell_visit_plan(entries,schema,state,collection,table_name,query,unique,unicode,schema_found,rows_found))
