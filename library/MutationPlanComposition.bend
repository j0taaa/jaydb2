# Exact DATA-plan composition; first real stop prevents the second stage.
# This connects independent removal/upsert row algebra to the already-checked
# actual interpreter, rather than assuming a successful combined loop.
import Base
import ./IndexScanModel.bend as Events
import ./MutationWritePlan.bend as M
import ./ReadPrefixComposition.bend as Lists
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S

def prefix(events: List<&2,S.OperationEvent>,plan: M.Plan) -> M.Plan:
  match plan:
    case M.WriteHandoff{working,later}: M.WriteHandoff{working,Events.events(events,later)}
    case M.WriteHalt{working,later,response}: M.WriteHalt{working,Events.events(events,later),response}

def follow(plan: M.Plan,+later: List<&2,D.Operation>,+schema: D.Schema) -> M.Plan:
  match plan:
    case M.WriteHandoff{working,events}: prefix(events,M.plan(later,schema,working))
    case M.WriteHalt{working,events,response}: M.WriteHalt{working,events,response}

law prepending_one_actual_event_preserves_exact_plan_prefix_composition:
  for +event: S.OperationEvent
  for +events: List<&2,S.OperationEvent>
  for +plan: M.Plan
  {M.prepend(event,prefix(events,plan)) == prefix(Con{event,events},plan) : M.Plan}
def prepending_one_actual_event_preserves_exact_plan_prefix_composition(event,events,plan):
  match plan:
    case M.WriteHandoff{working,later}: {==}
    case M.WriteHalt{working,later,response}: {==}

law following_a_plan_preserves_its_exact_preceding_event:
  for +event: S.OperationEvent
  for +plan: M.Plan
  for +later: List<&2,D.Operation>
  for +schema: D.Schema
  {M.prepend(event,follow(plan,later,schema)) == follow(M.prepend(event,plan),later,schema) : M.Plan}
def following_a_plan_preserves_its_exact_preceding_event(event,plan,later,schema):
  match plan:
    case M.WriteHandoff{+working,+events}: prepending_one_actual_event_preserves_exact_plan_prefix_composition(event,events,M.plan(later,schema,working))
    case M.WriteHalt{working,events,response}: {==}

law each_real_primitive_result_preserves_exact_stage_composition:
  for +result: D.ResultOp
  for +state: D.State
  for +op: D.Operation
  for +tail: M.Plan
  for +later: List<&2,D.Operation>
  for +schema: D.Schema
  {M.combine(result,state,op,follow(tail,later,schema)) == follow(M.combine(result,state,op,tail),later,schema) : M.Plan}
def each_real_primitive_result_preserves_exact_stage_composition(result,state,op,tail,later,schema):
  match result:
    case D.FailureData{}: {==}
    case D.Observed{observation}: {==}
    case D.Changed{working}: following_a_plan_preserves_its_exact_preceding_event(S.OperationEvent{op,S.Write{}},tail,later,schema)

law an_empty_plan_prefix_is_identity:
  for +plan: M.Plan
  {prefix(Nil{},plan) == plan : M.Plan}
def an_empty_plan_prefix_is_identity(plan):
  match plan:
    case M.WriteHandoff{working,events}: {==}
    case M.WriteHalt{working,events,response}: {==}

law actual_data_plan_for_concatenated_operations_is_exact_stage_composition:
  for +first: List<&2,D.Operation>
  for +later: List<&2,D.Operation>
  for +schema: D.Schema
  for +state: D.State
  {M.plan(Lists.append(first,later),schema,state) == follow(M.plan(first,schema,state),later,schema) : M.Plan}
def actual_data_plan_for_concatenated_operations_is_exact_stage_composition(first,later,schema,state):
  match first:
    case Nil{}: Equal.sym(M.Plan,prefix(Nil{},M.plan(later,schema,state)),M.plan(later,schema,state),an_empty_plan_prefix_is_identity(M.plan(later,schema,state)))
    case Con{+op,+tail}:
      Equal.trans(M.Plan,M.plan(Lists.append(Con{op,tail},later),schema,state),M.combine(D.operate(schema,state,op),state,op,follow(M.plan(tail,schema,M.after(D.operate(schema,state,op),state)),later,schema)),follow(M.plan(Con{op,tail},schema,state),later,schema),Equal.cong(M.Plan,M.Plan,plan => M.combine(D.operate(schema,state,op),state,op,plan),M.plan(Lists.append(tail,later),schema,M.after(D.operate(schema,state,op),state)),follow(M.plan(tail,schema,M.after(D.operate(schema,state,op),state)),later,schema),actual_data_plan_for_concatenated_operations_is_exact_stage_composition(tail,later,schema,M.after(D.operate(schema,state,op),state))),each_real_primitive_result_preserves_exact_stage_composition(D.operate(schema,state,op),state,op,M.plan(tail,schema,M.after(D.operate(schema,state,op),state)),later,schema))
