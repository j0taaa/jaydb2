# Total claim/lookup/maintenance behavior. The public heads receive only input
# DATA; no primitive output, completed trace, or whole-table invariant premise.
# Index consistency is a separate property requiring an explicit build/domain.
import Base
import ./MutationBooleanProofs.bend as Insert
import ./MutationBooleanDecisions.bend as Decision
import ./MutationDecisionTrace.bend as ReadWrite
import ./MutationWriteSequence.bend as W
import ./MutationWritePlan.bend as Plan
import ./MutationWriteTrace.bend as Trace
import ./ReadPrefixComposition.bend as Lists
import ./QueryReadPlan.bend as ReadPlan
import ./QueryReadPlanProofs.bend as ReadTrace
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Index.bend as Index
import ./Query.bend as Query
import ./Key.bend as Key
import ./Action.bend as Action
import ../src/Termination.bend as T

law actual_unique_claim_has_exact_existing_or_inserted_full_entry_behavior:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +parts: List<&2,String>
  for +target: String
  for +remaining: Nat
  for -done: Bool -> S.Action
  for +history: List<&2,S.OperationEvent>
  {T.observe(3n+remaining,Index.claim(collection,parts,target,done),schema,state,history) == ReadWrite.result_trace(~Bool,~Decision.RowContext,~Decision.insertion,Decision.RowContext{collection,Index.unique(parts,target)},D.operate(schema,state,D.ViewExistence{collection,Key.encode(parts)}),remaining,schema,state,D.ViewExistence{collection,Key.encode(parts)},done,history) : S.Trace}
def actual_unique_claim_has_exact_existing_or_inserted_full_entry_behavior(schema,state,collection,parts,target,remaining,done,history):
  Insert.actual_insert_if_absent_has_total_exact_read_decision_write_and_handoff(schema,state,collection,Index.unique(parts,target),remaining,done,history)

law actual_unique_lookup_selects_exactly_the_named_target_for_the_encoded_key:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +parts: List<&2,String>
  for +remaining: Nat
  for -done: Query.Selection -> S.Action
  for +history: List<&2,S.OperationEvent>
  {T.observe(1n+remaining,Index.lookup(collection,parts,done),schema,state,history) == ReadTrace.finish(ReadPlan.plan(schema,state,collection,Key.encode(parts),["target"]),remaining,schema,state,done,history) : S.Trace}
def actual_unique_lookup_selects_exactly_the_named_target_for_the_encoded_key(schema,state,collection,parts,remaining,done,history):
  ReadTrace.actual_read_fields_has_total_exact_source_state_behavior(schema,state,collection,Key.encode(parts),["target"],remaining,done,history)

law ordered_write_sequences_compose_by_exact_operation_concatenation:
  for +first: List<&2,D.Operation>
  for +later: List<&2,D.Operation>
  for -done: S.Action
  {W.perform(first,W.perform(later,done)) == W.perform(Lists.append(first,later),done) : S.Action}
def ordered_write_sequences_compose_by_exact_operation_concatenation(first,later,done):
  match first:
    case Nil{}: {==}
    case Con{+op,+tail}: Equal.cong(S.Action,S.Action,next => S.Access{op,r => Action.written(next,r)},W.perform(tail,W.perform(later,done)),W.perform(Lists.append(tail,later),done),ordered_write_sequences_compose_by_exact_operation_concatenation(tail,later,done))

def operations(+collection: D.Collection,old: List<&2,String>,rows: List<&2,D.Row>) -> List<&2,D.Operation>:
  Lists.append(W.removals(collection,old),W.rows(collection,rows))

law actual_maintenance_is_exact_removals_then_full_upserts_then_business_handoff:
  for +collection: D.Collection
  for +old: List<&2,String>
  for +rows: List<&2,D.Row>
  for -business: S.Action
  {Index.maintain(collection,old,rows,business) == W.perform(operations(collection,old,rows),business) : S.Action}
def actual_maintenance_is_exact_removals_then_full_upserts_then_business_handoff(collection,old,rows,business):
  Equal.trans(S.Action,Index.maintain(collection,old,rows,business),W.perform(W.removals(collection,old),Action.define_rows(collection,rows,business)),W.perform(operations(collection,old,rows),business),W.actual_remove_rows_is_exactly_the_ordered_named_write_sequence(collection,old,Action.define_rows(collection,rows,business)),Equal.trans(S.Action,W.perform(W.removals(collection,old),Action.define_rows(collection,rows,business)),W.perform(W.removals(collection,old),W.perform(W.rows(collection,rows),business)),W.perform(operations(collection,old,rows),business),Equal.cong(S.Action,S.Action,next => W.perform(W.removals(collection,old),next),Action.define_rows(collection,rows,business),W.perform(W.rows(collection,rows),business),W.actual_define_rows_is_exactly_the_ordered_named_write_sequence(collection,rows,business)),ordered_write_sequences_compose_by_exact_operation_concatenation(W.removals(collection,old),W.rows(collection,rows),business)))

law actual_index_maintenance_has_total_exact_state_events_errors_and_business_handoff:
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +old: List<&2,String>
  for +rows: List<&2,D.Row>
  for +remaining: Nat
  for -business: S.Action
  for +history: List<&2,S.OperationEvent>
  {T.observe(Plan.depth(operations(collection,old,rows),1n+remaining),Index.maintain(collection,old,rows,business),schema,state,history) == Trace.finish(Plan.plan(operations(collection,old,rows),schema,state),1n+remaining,schema,business,history) : S.Trace}
def actual_index_maintenance_has_total_exact_state_events_errors_and_business_handoff(schema,state,collection,old,rows,remaining,business,history):
  Equal.trans(S.Trace,T.observe(Plan.depth(operations(collection,old,rows),1n+remaining),Index.maintain(collection,old,rows,business),schema,state,history),T.observe(Plan.depth(operations(collection,old,rows),1n+remaining),W.perform(operations(collection,old,rows),business),schema,state,history),Trace.finish(Plan.plan(operations(collection,old,rows),schema,state),1n+remaining,schema,business,history),Equal.cong(S.Action,S.Trace,action => T.observe(Plan.depth(operations(collection,old,rows),1n+remaining),action,schema,state,history),Index.maintain(collection,old,rows,business),W.perform(operations(collection,old,rows),business),actual_maintenance_is_exact_removals_then_full_upserts_then_business_handoff(collection,old,rows,business)),Trace.actual_ordered_write_sequence_has_total_exact_evolving_state_behavior(operations(collection,old,rows),schema,state,remaining,business,history))
