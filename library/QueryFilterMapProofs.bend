# Arbitrary visitors may refuse or never invoke their continuation. Each
# original call supplies its LOCAL contextual refinement, consumed once.
# No whole map trace/outcome or continuation/action copying is assumed.
import Base
import ./QueryFilterMapModel.bend as M
import ./QueryVisitorContracts.bend as Contract
import ../contract/Logic.bend as L
import ./ReadPrefix.bend as Cut
import ./ReadPrefixComposition.bend as C
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Query.bend as Query
import ./Sequence.bend as Sequence

law actual_filter_map_owns_visitor_operations_in_key_order_and_exact_projected_handoff:
  for ~Env: Data
  for ~visit: Env -> String -> (Maybe<&2,D.Value> -> S.Action) -> S.Action
  for ~reply: Env -> Nat -> S.Return
  for ~cost: Env -> String -> Nat -> Nat
  for ~ops: Env -> String -> Nat -> List<&2,D.Operation>
  for ~item: Env -> String -> Nat -> Maybe<&2,D.Value>
  for +env: Env
  for +keys: List<&2,String>
  for +index: Nat
  for -done: D.Value -> S.Action
  for contracts: Contract.Calls(~Env,~visit,~reply,~cost,~ops,~item,env,keys,index)
  {Cut.cut(~Env,~reply,env,M.budget(~Env,~cost,env,keys,index),index,Query.filter_map(~Env,~visit,env,keys,done)) == Cut.prefix(M.operations(~Env,~cost,~ops,env,keys,index),done(Sequence.values(M.items(~Env,~cost,~item,env,keys,index)))) : Cut.Prefix}
def actual_filter_map_owns_visitor_operations_in_key_order_and_exact_projected_handoff(Env,visit,reply,cost,ops,item,env,keys,index,done,contracts):
  match keys contracts:
    case Nil{} Unit{}: {==}
    case Con{+key,+tail} L.Both{local,rest_contracts}:
      Equal.trans(Cut.Prefix,Cut.cut(~Env,~reply,env,Nat.add(cost(env,key,index),M.budget(~Env,~cost,env,tail,Nat.add(cost(env,key,index),index))),index,visit(env,key,value => Query.filter_map(~Env,~visit,env,tail,rest => done(Query.include(value,rest))))),C.attach(ops(env,key,index),Cut.cut(~Env,~reply,env,M.budget(~Env,~cost,env,tail,Nat.add(cost(env,key,index),index)),Nat.add(cost(env,key,index),index),Query.filter_map(~Env,~visit,env,tail,rest => done(Query.include(item(env,key,index),rest))))),Cut.prefix(C.append(ops(env,key,index),M.operations(~Env,~cost,~ops,env,tail,Nat.add(cost(env,key,index),index))),done(Sequence.values(M.push(item(env,key,index),M.items(~Env,~cost,~item,env,tail,Nat.add(cost(env,key,index),index)))))),
        local(M.budget(~Env,~cost,env,tail,Nat.add(cost(env,key,index),index)),value => Query.filter_map(~Env,~visit,env,tail,rest => done(Query.include(value,rest)))),
        Equal.trans(Cut.Prefix,C.attach(ops(env,key,index),Cut.cut(~Env,~reply,env,M.budget(~Env,~cost,env,tail,Nat.add(cost(env,key,index),index)),Nat.add(cost(env,key,index),index),Query.filter_map(~Env,~visit,env,tail,rest => done(Query.include(item(env,key,index),rest))))),C.attach(ops(env,key,index),Cut.prefix(M.operations(~Env,~cost,~ops,env,tail,Nat.add(cost(env,key,index),index)),done(Query.include(item(env,key,index),Sequence.values(M.items(~Env,~cost,~item,env,tail,Nat.add(cost(env,key,index),index))))))),Cut.prefix(C.append(ops(env,key,index),M.operations(~Env,~cost,~ops,env,tail,Nat.add(cost(env,key,index),index))),done(Sequence.values(M.push(item(env,key,index),M.items(~Env,~cost,~item,env,tail,Nat.add(cost(env,key,index),index)))))),
        Equal.cong(Cut.Prefix,Cut.Prefix,p => C.attach(ops(env,key,index),p),Cut.cut(~Env,~reply,env,M.budget(~Env,~cost,env,tail,Nat.add(cost(env,key,index),index)),Nat.add(cost(env,key,index),index),Query.filter_map(~Env,~visit,env,tail,rest => done(Query.include(item(env,key,index),rest)))),Cut.prefix(M.operations(~Env,~cost,~ops,env,tail,Nat.add(cost(env,key,index),index)),done(Query.include(item(env,key,index),Sequence.values(M.items(~Env,~cost,~item,env,tail,Nat.add(cost(env,key,index),index)))))),actual_filter_map_owns_visitor_operations_in_key_order_and_exact_projected_handoff(~Env,~visit,~reply,~cost,~ops,~item,env,tail,Nat.add(cost(env,key,index),index),rest => done(Query.include(item(env,key,index),rest)),rest_contracts)),
        Equal.trans(Cut.Prefix,C.attach(ops(env,key,index),Cut.prefix(M.operations(~Env,~cost,~ops,env,tail,Nat.add(cost(env,key,index),index)),done(Query.include(item(env,key,index),Sequence.values(M.items(~Env,~cost,~item,env,tail,Nat.add(cost(env,key,index),index))))))),Cut.prefix(C.append(ops(env,key,index),M.operations(~Env,~cost,~ops,env,tail,Nat.add(cost(env,key,index),index))),done(Query.include(item(env,key,index),Sequence.values(M.items(~Env,~cost,~item,env,tail,Nat.add(cost(env,key,index),index)))))),Cut.prefix(C.append(ops(env,key,index),M.operations(~Env,~cost,~ops,env,tail,Nat.add(cost(env,key,index),index))),done(Sequence.values(M.push(item(env,key,index),M.items(~Env,~cost,~item,env,tail,Nat.add(cost(env,key,index),index)))))),
        C.attaching_known_prefixes_preserves_exact_list_concatenation(ops(env,key,index),M.operations(~Env,~cost,~ops,env,tail,Nat.add(cost(env,key,index),index)),done(Query.include(item(env,key,index),Sequence.values(M.items(~Env,~cost,~item,env,tail,Nat.add(cost(env,key,index),index)))))),
        Equal.cong(D.Value,Cut.Prefix,value => Cut.prefix(C.append(ops(env,key,index),M.operations(~Env,~cost,~ops,env,tail,Nat.add(cost(env,key,index),index))),done(value)),Query.include(item(env,key,index),Sequence.values(M.items(~Env,~cost,~item,env,tail,Nat.add(cost(env,key,index),index)))),Sequence.values(M.push(item(env,key,index),M.items(~Env,~cost,~item,env,tail,Nat.add(cost(env,key,index),index)))),Equal.sym(D.Value,Sequence.values(M.push(item(env,key,index),M.items(~Env,~cost,~item,env,tail,Nat.add(cost(env,key,index),index)))),Query.include(item(env,key,index),Sequence.values(M.items(~Env,~cost,~item,env,tail,Nat.add(cost(env,key,index),index)))),M.projected_items_encode_exactly_the_query_include_operation(item(env,key,index),M.items(~Env,~cost,~item,env,tail,Nat.add(cost(env,key,index),index))))))))
