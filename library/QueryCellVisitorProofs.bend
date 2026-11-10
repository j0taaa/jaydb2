# A nonvacuous one-read visitor discharges the contextual contract for EVERY
# Return, including unexpected ones. It projects cells and filters other
# returns. Arbitrary duplicate keys and arbitrary Return streams are allowed.
import Base
import ./QueryFilterMapProofs.bend as F
import ./QueryVisitorContracts.bend as Contract
import ../contract/Logic.bend as L
import ./QueryFilterMapModel.bend as M
import ./ReadPrefix.bend as Cut
import ./ReadPrefixComposition.bend as C
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Query.bend as Query
import ./Sequence.bend as Sequence

type Context is Data:
  Context{collection: D.Collection,returns: List<&2,S.Return>}

def collection(context: Context) -> D.Collection:
  match context:
    case Context{collection,returns}: collection

def at(returns: List<&2,S.Return>,index: Nat) -> S.Return:
  match returns index:
    case Nil{} index: S.UnitValue{}
    case Con{head,tail} 0n: head
    case Con{head,tail} 1n+previous: at(tail,previous)

def reply(context: Context,index: Nat) -> S.Return:
  match context:
    case Context{collection,returns}: at(returns,index)

def project(returned: S.Return) -> Maybe<&2,D.Value>:
  match returned:
    case S.Datum{D.Cell{value}}: Some{value}
    case S.Datum{D.RowAbsent{}}: None{}
    case S.Datum{D.Keys{keys}}: None{}
    case S.Datum{D.Count{count}}: None{}
    case S.Datum{D.Existence{exists}}: None{}
    case S.UnitValue{}: None{}

def received(done: Maybe<&2,D.Value> -> S.Action,returned: S.Return) -> S.Action:
  done(project(returned))

def visit(context: Context,key: String,done: Maybe<&2,D.Value> -> S.Action) -> S.Action:
  S.Access{D.ReadCell{collection(context),key,"value"},received(done)}

def cost(context: Context,key: String,index: Nat) -> Nat: 1n

def operations(context: Context,key: String,index: Nat) -> List<&2,D.Operation>:
  [D.ReadCell{collection(context),key,"value"}]

def item(context: Context,key: String,index: Nat) -> Maybe<&2,D.Value>:
  project(reply(context,index))

law the_cell_visitor_has_exactly_one_owned_read_and_preserves_its_continuation:
  for +context: Context
  for +key: String
  for +index: Nat
  for +remaining: Nat
  for -done: Maybe<&2,D.Value> -> S.Action
  {Cut.cut(~Context,~reply,context,Nat.add(cost(context,key,index),remaining),index,visit(context,key,done)) == C.attach(operations(context,key,index),Cut.cut(~Context,~reply,context,remaining,Nat.add(cost(context,key,index),index),done(item(context,key,index)))) : Cut.Prefix}
def the_cell_visitor_has_exactly_one_owned_read_and_preserves_its_continuation(context,key,index,remaining,done): {==}

def every_original_cell_visitor_call_has_its_local_contract(+context: Context,keys: List<&2,String>,+index: Nat) -> Contract.Calls(~Context,~visit,~reply,~cost,~operations,~item,context,keys,index):
  match keys:
    case Nil{}: Unit{}
    case Con{+key,tail}: L.Both{remaining => done => the_cell_visitor_has_exactly_one_owned_read_and_preserves_its_continuation(context,key,index,remaining,done),every_original_cell_visitor_call_has_its_local_contract(context,tail,1n+index)}

law filter_map_of_cell_visitors_has_exact_key_access_and_projected_payload_order:
  for +context: Context
  for +keys: List<&2,String>
  for +index: Nat
  for -done: D.Value -> S.Action
  {Cut.cut(~Context,~reply,context,M.budget(~Context,~cost,context,keys,index),index,Query.filter_map(~Context,~visit,context,keys,done)) == Cut.prefix(M.operations(~Context,~cost,~operations,context,keys,index),done(Sequence.values(M.items(~Context,~cost,~item,context,keys,index)))) : Cut.Prefix}
def filter_map_of_cell_visitors_has_exact_key_access_and_projected_payload_order(context,keys,index,done):
  F.actual_filter_map_owns_visitor_operations_in_key_order_and_exact_projected_handoff(~Context,~visit,~reply,~cost,~operations,~item,context,keys,index,done,every_original_cell_visitor_call_has_its_local_contract(context,keys,index))
