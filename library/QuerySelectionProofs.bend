# Exact owned read prefix for arbitrary Return streams and continuations.
# The observer cuts BEFORE the continuation's own actions: no assumption of
# continuation completion, purity, or read-only behavior is needed.
import Base
import ./ReadPrefix.bend as Cut
import ./QuerySelectionModel.bend as Model
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Query.bend as Query
import ./ReadProgram.bend as Program

law read_fields_owns_exactly_the_requested_access_prefix_and_exact_selection_handoff:
  for ~Env: Data
  for ~reply: Env -> Nat -> S.Return
  for +env: Env
  for +names: List<&2,String>
  for +index: Nat
  for +collection: D.Collection
  for +key: String
  for -done: Query.Selection -> S.Action
  {Cut.cut(~Env,~reply,env,Model.count(names),index,Query.read_fields(collection,key,names,done)) == Cut.prefix(Model.operations(collection,key,names),done(Model.expected(~Env,~reply,env,index,names))) : Cut.Prefix}
def read_fields_owns_exactly_the_requested_access_prefix_and_exact_selection_handoff(Env,reply,env,names,index,collection,key,done):
  match names:
    case Nil{}: {==}
    case Con{+name,+tail}:
      Equal.trans(Cut.Prefix,Cut.cut(~Env,~reply,env,1n+Model.count(tail),index,Query.read_fields(collection,key,Con{name,tail},done)),Cut.prefix(Con{D.ReadCell{collection,key,name},Model.operations(collection,key,tail)},done(Query.combine(name,reply(env,index),Model.expected(~Env,~reply,env,1n+index,tail)))),Cut.prefix(Model.operations(collection,key,Con{name,tail}),done(Model.expected(~Env,~reply,env,index,Con{name,tail}))),
        Equal.cong(Cut.Prefix,Cut.Prefix,rest => Cut.prepend(D.ReadCell{collection,key,name},rest),
          Cut.cut(~Env,~reply,env,Model.count(tail),1n+index,Query.read_fields(collection,key,tail,result => done(Query.combine(name,reply(env,index),result)))),
          Cut.prefix(Model.operations(collection,key,tail),done(Query.combine(name,reply(env,index),Model.expected(~Env,~reply,env,1n+index,tail)))),
          read_fields_owns_exactly_the_requested_access_prefix_and_exact_selection_handoff(~Env,~reply,env,tail,1n+index,collection,key,result => done(Query.combine(name,reply(env,index),result)))),
        Equal.cong(Query.Selection,Cut.Prefix,result => Cut.prefix(Model.operations(collection,key,Con{name,tail}),done(result)),Query.combine(name,reply(env,index),Model.expected(~Env,~reply,env,1n+index,tail)),Model.expected(~Env,~reply,env,index,Con{name,tail}),Equal.sym(Query.Selection,Model.expected(~Env,~reply,env,index,Con{name,tail}),Query.combine(name,reply(env,index),Model.expected(~Env,~reply,env,1n+index,tail)),Model.independent_selection_meaning_has_exact_head_and_tail_composition(~Env,~reply,env,index,name,tail))))

# Validation determines the owned cut length BEFORE any read. An invalid
# selection hands control immediately to done(InvalidFields); done may itself
# perform actions, which are correctly outside this owned prefix.
def steps(valid: Bool,names: List<&2,String>) -> Nat:
  match valid:
    case True{}: Model.count(names)
    case False{}: 0n

def result(~Env: Data,~reply: Env -> Nat -> S.Return,valid: Bool,+env: Env,+index: Nat,+names: List<&2,String>) -> Query.Selection:
  match valid:
    case True{}: Model.expected(~Env,~reply,env,index,names)
    case False{}: Query.InvalidFields{}


def select_case(~Env: Data,~reply: Env -> Nat -> S.Return,valid: Bool,+env: Env,+index: Nat,+collection: D.Collection,+key: String,+names: List<&2,String>,-done: Query.Selection -> S.Action) ->
  {Cut.cut(~Env,~reply,env,steps(valid,names),index,Query.select_valid(valid,collection,key,names,done)) == Cut.prefix(Bool.pick(List<&2,D.Operation>,valid,Model.operations(collection,key,names),Nil{}),done(result(~Env,~reply,valid,env,index,names))) : Cut.Prefix}:
  match valid:
    case True{}: read_fields_owns_exactly_the_requested_access_prefix_and_exact_selection_handoff(~Env,~reply,env,names,index,collection,key,done)
    case False{}: {==}

law actual_select_validates_before_its_exact_ordered_owned_read_prefix:
  for ~Env: Data
  for ~reply: Env -> Nat -> S.Return
  for +env: Env
  for +index: Nat
  for +collection: D.Collection
  for +key: String
  for +names: List<&2,String>
  for -done: Query.Selection -> S.Action
  {Cut.cut(~Env,~reply,env,steps(Query.fields_valid(names),names),index,Query.select(collection,key,names,done)) == Cut.prefix(Bool.pick(List<&2,D.Operation>,Query.fields_valid(names),Model.operations(collection,key,names),Nil{}),done(result(~Env,~reply,Query.fields_valid(names),env,index,names))) : Cut.Prefix}
def actual_select_validates_before_its_exact_ordered_owned_read_prefix(Env,reply,env,index,collection,key,names,done):
  select_case(~Env,~reply,Query.fields_valid(names),env,index,collection,key,names,done)

law closed_read_program_has_the_exact_validated_prefix_and_final_action:
  for ~Env: Data
  for ~reply: Env -> Nat -> S.Return
  for +env: Env
  for +index: Nat
  for +collection: D.Collection
  for +key: String
  for +names: List<&2,String>
  {Cut.cut(~Env,~reply,env,steps(Query.fields_valid(names),names),index,Program.select(collection,key,names)) == Cut.prefix(Bool.pick(List<&2,D.Operation>,Query.fields_valid(names),Model.operations(collection,key,names),Nil{}),Program.selected(result(~Env,~reply,Query.fields_valid(names),env,index,names))) : Cut.Prefix}
def closed_read_program_has_the_exact_validated_prefix_and_final_action(Env,reply,env,index,collection,key,names):
  actual_select_validates_before_its_exact_ordered_owned_read_prefix(~Env,~reply,env,index,collection,key,names,Program.selected)
