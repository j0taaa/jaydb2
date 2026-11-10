# No duplicate group keys and no empty materialized groups. The public laws
# quantify only the original input; insertion invariants are derived internally.
import Base
import ../contract/Data.bend as D
import ./Sequence.bend as Sequence
import ../proof/Foundations.bend as F
import ../proof/Orders.bend as O

type Both<-P: Data,-Q: Data> is Data:
  Both{left: P,right: Q}

def Absent(+wanted: String,groups: List<&2,Sequence.Group>) -> Data:
  match groups:
    case Nil{}: Unit
    case Con{Sequence.Group{key,items},tail}: Both<{String.eq(wanted,key) == False{} : Bool},Absent(wanted,tail)>

def Unique(groups: List<&2,Sequence.Group>) -> Data:
  match groups:
    case Nil{}: Unit
    case Con{Sequence.Group{+key,items},+tail}: Both<Absent(key,tail),Unique(tail)>

def Nonempty(items: List<&2,D.Value>) -> Data:
  match items:
    case Nil{}: {False{} == True{} : Bool}
    case Con{x,tail}: Unit

def NonemptyGroups(groups: List<&2,Sequence.Group>) -> Data:
  match groups:
    case Nil{}: Unit
    case Con{Sequence.Group{key,items},tail}: Both<Nonempty(items),NonemptyGroups(tail)>

def inequality_inverse_case(reverse: Bool,+a: String,+b: String,different: {String.eq(a,b) == False{} : Bool},actual: {String.eq(b,a) == reverse : Bool}) -> {reverse == False{} : Bool}:
  match reverse:
    case False{}: {==}
    case True{}: F.absurd_boolean({True{} == False{} : Bool},Equal.trans(Bool,False{},String.eq(a,b),True{},Equal.sym(Bool,String.eq(a,b),False{},different),O.string_eq_inverse(b,a,actual)))

law string_inequality_is_symmetric:
  for +a: String
  for +b: String
  for different: {String.eq(a,b) == False{} : Bool}
  {String.eq(b,a) == False{} : Bool}
def string_inequality_is_symmetric(a,b,different):
  inequality_inverse_case(String.eq(b,a),a,b,different,{==})

def absent_choice(equal: Bool,+wanted: String,+key: String,+x: D.Value,+head: String,+items: List<&2,D.Value>,+tail: List<&2,Sequence.Group>,absent_head: {String.eq(wanted,head) == False{} : Bool},absent_tail: Absent(wanted,tail),recursive: Absent(wanted,Sequence.group_insert(key,x,tail))) ->
  Absent(wanted,Bool.pick(List<&2,Sequence.Group>,equal,Con{Sequence.Group{head,Con{x,items}},tail},Con{Sequence.Group{head,items},Sequence.group_insert(key,x,tail)})):
  match equal:
    case True{}: Both{absent_head,absent_tail}
    case False{}: Both{absent_head,recursive}

law insertion_preserves_every_other_absent_key:
  for +wanted: String
  for +key: String
  for +x: D.Value
  for +groups: List<&2,Sequence.Group>
  for +different: {String.eq(wanted,key) == False{} : Bool}
  for absent: Absent(wanted,groups)
  Absent(wanted,Sequence.group_insert(key,x,groups))
def insertion_preserves_every_other_absent_key(wanted,key,x,groups,different,absent):
  match groups absent:
    case Nil{} Unit{}: Both{different,Unit{}}
    case Con{Sequence.Group{+head,+items},+tail} Both{not_head,+not_tail}: absent_choice(String.eq(key,head),wanted,key,x,head,items,tail,not_head,not_tail,insertion_preserves_every_other_absent_key(wanted,key,x,tail,different,not_tail))

def unique_choice(equal: Bool,+key: String,+x: D.Value,+head: String,+items: List<&2,D.Value>,+tail: List<&2,Sequence.Group>,actual: {String.eq(key,head) == equal : Bool},absent_head: Absent(head,tail),unique_tail: Unique(tail),recursive: Unique(Sequence.group_insert(key,x,tail))) ->
  Unique(Bool.pick(List<&2,Sequence.Group>,equal,Con{Sequence.Group{head,Con{x,items}},tail},Con{Sequence.Group{head,items},Sequence.group_insert(key,x,tail)})):
  match equal:
    case True{}: Both{absent_head,unique_tail}
    case False{}: Both{insertion_preserves_every_other_absent_key(head,key,x,tail,string_inequality_is_symmetric(key,head,actual),absent_head),recursive}

law insertion_preserves_unique_group_keys:
  for +key: String
  for +x: D.Value
  for +groups: List<&2,Sequence.Group>
  for unique: Unique(groups)
  Unique(Sequence.group_insert(key,x,groups))
def insertion_preserves_unique_group_keys(key,x,groups,unique):
  match groups unique:
    case Nil{} Unit{}: Both{Unit{},Unit{}}
    case Con{Sequence.Group{+head,+items},+tail} Both{absent_head,+unique_tail}: unique_choice(String.eq(key,head),key,x,head,items,tail,{==},absent_head,unique_tail,insertion_preserves_unique_group_keys(key,x,tail,unique_tail))

def nonempty_choice(equal: Bool,+key: String,+x: D.Value,+head: String,+items: List<&2,D.Value>,+tail: List<&2,Sequence.Group>,head_nonempty: Nonempty(items),tail_nonempty: NonemptyGroups(tail),recursive: NonemptyGroups(Sequence.group_insert(key,x,tail))) ->
  NonemptyGroups(Bool.pick(List<&2,Sequence.Group>,equal,Con{Sequence.Group{head,Con{x,items}},tail},Con{Sequence.Group{head,items},Sequence.group_insert(key,x,tail)})):
  match equal:
    case True{}: Both{Unit{},tail_nonempty}
    case False{}: Both{head_nonempty,recursive}

law insertion_preserves_nonempty_materialized_groups:
  for +key: String
  for +x: D.Value
  for +groups: List<&2,Sequence.Group>
  for nonempty: NonemptyGroups(groups)
  NonemptyGroups(Sequence.group_insert(key,x,groups))
def insertion_preserves_nonempty_materialized_groups(key,x,groups,nonempty):
  match groups nonempty:
    case Nil{} Unit{}: Both{Unit{},Unit{}}
    case Con{Sequence.Group{+head,+items},+tail} Both{head_nonempty,+tail_nonempty}: nonempty_choice(String.eq(key,head),key,x,head,items,tail,head_nonempty,tail_nonempty,insertion_preserves_nonempty_materialized_groups(key,x,tail,tail_nonempty))

law actual_groups_have_unique_keys:
  for ~key: D.Value -> String
  for +xs: List<&2,D.Value>
  Unique(Sequence.group(~key,xs))
def actual_groups_have_unique_keys(key,xs):
  match xs:
    case Nil{}: Unit{}
    case Con{+x,+tail}: insertion_preserves_unique_group_keys(key(x),x,Sequence.group(~key,tail),actual_groups_have_unique_keys(~key,tail))

law actual_groups_have_nonempty_member_lists:
  for ~key: D.Value -> String
  for +xs: List<&2,D.Value>
  NonemptyGroups(Sequence.group(~key,xs))
def actual_groups_have_nonempty_member_lists(key,xs):
  match xs:
    case Nil{}: Unit{}
    case Con{+x,+tail}: insertion_preserves_nonempty_materialized_groups(key(x),x,Sequence.group(~key,tail),actual_groups_have_nonempty_member_lists(~key,tail))
