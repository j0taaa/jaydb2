# Lift the independent lifetime relation to ALL principal table views.
# The three concrete replacement transforms are proved here, not supplied as
# an assumed postcondition. All Type-valued invariant proofs remain affine.
import Base
import ./VoucherLifetimeMeaning.bend as I
import ./VoucherLifetimeCreate.bend as Create
import ./VoucherLifetimeRetire.bend as Retire
import ./VoucherLifetimePermission.bend as Permission
import ./VoucherPairProofs.bend as P
import ../Initial.bend as Initial
import ../../../contract/Data.bend as D
import ../../../library/CollectionFrameProofs.bend as Frame
import ../../../proof/Orders.bend as O

def View(+owner: String,rows: Maybe<&2,List<&2,D.Row>>) -> Type:
  match rows:
    case None{}: Unit
    case Some{rows}: I.Lifetime(owner,rows)
def Owner(+owner: String,state: D.State) -> Type:
  View(owner,D.rows_collection(D.Application{owner},state))
def Global(+state: D.State) -> Type:
  @+owner: String -> Owner(owner,state)

type Update is Data:
  PairCreated{request: String,input: String}
  PairRetired{request: String}
  GateUpdated{enabled: Bool}
def replacement(update: Update,owner: String,old: List<&2,D.Row>) -> List<&2,D.Row>:
  match update:
    case PairCreated{request,input}: P.rows(owner,request,input,False{},old)
    case PairRetired{request}: Retire.rows(request,old)
    case GateUpdated{enabled}: D.insert_row(old,Permission.row(owner,enabled))
def transformed_state(+update: Update,+owner: String,before: D.State,old: List<&2,D.Row>) -> D.State:
  D.swap_collection(D.Application{owner},before,replacement(update,owner,old))

def preserves_rows(+update: Update,+owner: String,+old: List<&2,D.Row>,previous: I.Lifetime(owner,old)) -> I.Lifetime(owner,replacement(update,owner,old)):
  match update:
    case PairCreated{request,input}: Create.actual_pair_upserts_preserve_the_complete_bidirectional_all_request_lifetime_invariant(owner,request,input,old,previous)
    case PairRetired{request}: Retire.actual_pair_deletion_preserves_the_complete_bidirectional_all_request_lifetime_invariant(owner,request,old,previous)
    case GateUpdated{enabled}: Permission.actual_permission_row_upsert_preserves_the_complete_lifetime_invariant(owner,enabled,old,previous)

def local_from_owner(+owner: String,+before: D.State,+old: List<&2,D.Row>,found: {D.rows_collection(D.Application{owner},before) == Some{old} : Maybe<&2,List<&2,D.Row>>},previous: Owner(owner,before)) -> I.Lifetime(owner,old):
  %found : View(owner,_)
  previous

def from_new_rows(+owner: String,+before: D.State,+old: List<&2,D.Row>,+new: List<&2,D.Row>,found: {D.rows_collection(D.Application{owner},before) == Some{old} : Maybe<&2,List<&2,D.Row>>},current: I.Lifetime(owner,new)) -> Owner(owner,D.swap_collection(D.Application{owner},before,new)):
  %Equal.sym(Maybe<&2,List<&2,D.Row>>,D.rows_collection(D.Application{owner},D.swap_collection(D.Application{owner},before,new)),Some{new},Frame.replacing_an_existing_collection_has_the_exact_new_row_view(D.Application{owner},before,old,new,found)) : View(owner,_)
  current

def unchanged_view(+owner: String,+before: D.State,+after: D.State,same: {D.rows_collection(D.Application{owner},after) == D.rows_collection(D.Application{owner},before) : Maybe<&2,List<&2,D.Row>>},previous: Owner(owner,before)) -> Owner(owner,after):
  %Equal.sym(Maybe<&2,List<&2,D.Row>>,D.rows_collection(D.Application{owner},after),D.rows_collection(D.Application{owner},before),same) : View(owner,_)
  previous

def owner_case(same: Bool,+update: Update,+owner: String,+watched: String,+before: D.State,+old: List<&2,D.Row>,+found: {D.rows_collection(D.Application{owner},before) == Some{old} : Maybe<&2,List<&2,D.Row>>},actual: {String.eq(owner,watched) == same : Bool},previous: Global(before)) -> Owner(watched,transformed_state(update,owner,before,old)):
  match same:
    case True{}:
      %O.string_equal(owner,watched,actual) : Owner(_,transformed_state(update,owner,before,old))
      from_new_rows(owner,before,old,replacement(update,owner,old),found,preserves_rows(update,owner,old,local_from_owner(owner,before,old,found,previous(owner))))
    case False{}: unchanged_view(watched,before,transformed_state(update,owner,before,old),Frame.replacing_a_collection_preserves_every_separate_collection_view(D.Application{owner},D.Application{watched},before,replacement(update,owner,old),actual),previous(watched))

law the_three_proved_concrete_replacement_transforms_preserve_every_principal_lifetime:
  for +update: Update
  for +owner: String
  for +before: D.State
  for +old: List<&2,D.Row>
  for +found: {D.rows_collection(D.Application{owner},before) == Some{old} : Maybe<&2,List<&2,D.Row>>}
  for previous: Global(before)
  Global(transformed_state(update,owner,before,old))
def the_three_proved_concrete_replacement_transforms_preserve_every_principal_lifetime(update,owner,before,old,found,previous):
  watched => owner_case(String.eq(owner,watched),update,owner,watched,before,old,found,{==},previous)

def seed(users: List<&2,D.Row>) -> D.State: D.State{Initial.tables(),users}
def initial_owner_case(alice: Bool,bob: Bool,+owner: String,+users: List<&2,D.Row>,alice_actual: {String.eq("alice",owner) == alice : Bool},bob_actual: {String.eq("bob",owner) == bob : Bool}) -> Owner(owner,seed(users)):
  match alice bob:
    case True{} bob:
      %O.string_equal("alice",owner,alice_actual) : Owner(_,seed(users))
      Permission.the_actual_frozen_initial_gate_table_has_the_complete_lifetime_invariant("alice")
    case False{} True{}:
      %O.string_equal("bob",owner,bob_actual) : Owner(_,seed(users))
      Permission.the_actual_frozen_initial_gate_table_has_the_complete_lifetime_invariant("bob")
    case False{} False{}:
      %Equal.sym(Maybe<&2,List<&2,D.Row>>,D.rows_collection(D.Application{owner},seed(users)),None{},Equal.trans(Maybe<&2,List<&2,D.Row>>,Frame.view(Initial.tables(),owner),Frame.view([D.Table{"bob",[Initial.gate("bob")]}],owner),None{},Frame.different_head_table_does_not_change_the_observed_row_view("alice",[Initial.gate("alice")],[D.Table{"bob",[Initial.gate("bob")]}],owner,alice_actual),Frame.different_head_table_does_not_change_the_observed_row_view("bob",[Initial.gate("bob")],Nil{},owner,bob_actual))) : View(owner,_)
      Unit{}

law every_actual_frozen_seed_table_has_the_complete_global_lifetime_invariant:
  for +users: List<&2,D.Row>
  Global(seed(users))
def every_actual_frozen_seed_table_has_the_complete_global_lifetime_invariant(users):
  owner => initial_owner_case(String.eq("alice",owner),String.eq("bob",owner),owner,users,{==},{==})

law the_unchanged_administrator_origin_predicate_implies_the_independent_global_lifetime_invariant:
  for +state: D.State
  for origin: Initial.origin(state)
  Global(state)
def the_unchanged_administrator_origin_predicate_implies_the_independent_global_lifetime_invariant(state,origin):
  match state:
    case D.State{+tables,+users}:
      %Equal.sym(List<&2,D.Table>,tables,Initial.tables(),origin) : Global(D.State{_,users})
      every_actual_frozen_seed_table_has_the_complete_global_lifetime_invariant(users)
