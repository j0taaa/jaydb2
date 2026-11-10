# Independent algebra of actual row removal. Removing ALL enumerated ORIGINAL
# keys empties every finite row list, even with duplicates/unsorted keys. No
# operation success, output-row, or completed rebuild invariant is assumed.
import Base
import ../contract/Data.bend as D
import ../proof/Orders.bend as O

def keep(kept: Bool,head: D.Row,tail: List<&2,D.Row>) -> List<&2,D.Row>:
  match kept:
    case False{}: tail
    case True{}: Con{head,tail}

law conditional_row_removal_is_exactly_not_equal_inclusion:
  for +equal: Bool
  for +head: D.Row
  for +tail: List<&2,D.Row>
  {Bool.pick(List<&2,D.Row>,equal,tail,Con{head,tail}) == keep(Bool.not(equal),head,tail) : List<&2,D.Row>}
def conditional_row_removal_is_exactly_not_equal_inclusion(equal,head,tail):
  match equal:
    case False{}: {==}
    case True{}: {==}

law actual_row_removal_excludes_exactly_the_matching_head_key:
  for +head: D.Row
  for +tail: List<&2,D.Row>
  for +key: String
  {D.remove_row(Con{head,tail},key) == keep(Bool.not(String.eq(D.row_key(head),key)),head,D.remove_row(tail,key)) : List<&2,D.Row>}
def actual_row_removal_excludes_exactly_the_matching_head_key(head,tail,key):
  match head:
    case D.Row{+name,+fields}: conditional_row_removal_is_exactly_not_equal_inclusion(String.eq(name,key),D.Row{name,fields},D.remove_row(tail,key))

law actual_row_removal_distributes_through_independent_head_inclusion:
  for +kept: Bool
  for +head: D.Row
  for +tail: List<&2,D.Row>
  for +key: String
  {D.remove_row(keep(kept,head,tail),key) == keep(kept && Bool.not(String.eq(D.row_key(head),key)),head,D.remove_row(tail,key)) : List<&2,D.Row>}
def actual_row_removal_distributes_through_independent_head_inclusion(kept,head,tail,key):
  match kept:
    case False{}: {==}
    case True{}: actual_row_removal_excludes_exactly_the_matching_head_key(head,tail,key)

law boolean_intersection_is_commutative:
  for a: Bool
  for b: Bool
  {a && b == b && a : Bool}
def boolean_intersection_is_commutative(a,b):
  match a b:
    case False{} False{}: {==}
    case False{} True{}: {==}
    case True{} False{}: {==}
    case True{} True{}: {==}

law removing_two_keys_commutes_for_all_row_lists:
  for +rows: List<&2,D.Row>
  for +first: String
  for +later: String
  {D.remove_row(D.remove_row(rows,first),later) == D.remove_row(D.remove_row(rows,later),first) : List<&2,D.Row>}
def removing_two_keys_commutes_for_all_row_lists(rows,first,later):
  match rows:
    case Nil{}: {==}
    case Con{+head,+tail}: Equal.trans(List<&2,D.Row>,D.remove_row(D.remove_row(Con{head,tail},first),later),D.remove_row(keep(Bool.not(String.eq(D.row_key(head),first)),head,D.remove_row(tail,first)),later),D.remove_row(D.remove_row(Con{head,tail},later),first),Equal.cong(List<&2,D.Row>,List<&2,D.Row>,rows => D.remove_row(rows,later),D.remove_row(Con{head,tail},first),keep(Bool.not(String.eq(D.row_key(head),first)),head,D.remove_row(tail,first)),actual_row_removal_excludes_exactly_the_matching_head_key(head,tail,first)),Equal.trans(List<&2,D.Row>,D.remove_row(keep(Bool.not(String.eq(D.row_key(head),first)),head,D.remove_row(tail,first)),later),keep(Bool.not(String.eq(D.row_key(head),first)) && Bool.not(String.eq(D.row_key(head),later)),head,D.remove_row(D.remove_row(tail,first),later)),D.remove_row(D.remove_row(Con{head,tail},later),first),actual_row_removal_distributes_through_independent_head_inclusion(Bool.not(String.eq(D.row_key(head),first)),head,D.remove_row(tail,first),later),Equal.trans(List<&2,D.Row>,keep(Bool.not(String.eq(D.row_key(head),first)) && Bool.not(String.eq(D.row_key(head),later)),head,D.remove_row(D.remove_row(tail,first),later)),keep(Bool.not(String.eq(D.row_key(head),first)) && Bool.not(String.eq(D.row_key(head),later)),head,D.remove_row(D.remove_row(tail,later),first)),D.remove_row(D.remove_row(Con{head,tail},later),first),Equal.cong(List<&2,D.Row>,List<&2,D.Row>,rows => keep(Bool.not(String.eq(D.row_key(head),first)) && Bool.not(String.eq(D.row_key(head),later)),head,rows),D.remove_row(D.remove_row(tail,first),later),D.remove_row(D.remove_row(tail,later),first),removing_two_keys_commutes_for_all_row_lists(tail,first,later)),Equal.trans(List<&2,D.Row>,keep(Bool.not(String.eq(D.row_key(head),first)) && Bool.not(String.eq(D.row_key(head),later)),head,D.remove_row(D.remove_row(tail,later),first)),keep(Bool.not(String.eq(D.row_key(head),later)) && Bool.not(String.eq(D.row_key(head),first)),head,D.remove_row(D.remove_row(tail,later),first)),D.remove_row(D.remove_row(Con{head,tail},later),first),Equal.cong(Bool,List<&2,D.Row>,b => keep(b,head,D.remove_row(D.remove_row(tail,later),first)),Bool.not(String.eq(D.row_key(head),first)) && Bool.not(String.eq(D.row_key(head),later)),Bool.not(String.eq(D.row_key(head),later)) && Bool.not(String.eq(D.row_key(head),first)),boolean_intersection_is_commutative(Bool.not(String.eq(D.row_key(head),first)),Bool.not(String.eq(D.row_key(head),later)))),Equal.trans(List<&2,D.Row>,keep(Bool.not(String.eq(D.row_key(head),later)) && Bool.not(String.eq(D.row_key(head),first)),head,D.remove_row(D.remove_row(tail,later),first)),D.remove_row(keep(Bool.not(String.eq(D.row_key(head),later)),head,D.remove_row(tail,later)),first),D.remove_row(D.remove_row(Con{head,tail},later),first),Equal.sym(List<&2,D.Row>,D.remove_row(keep(Bool.not(String.eq(D.row_key(head),later)),head,D.remove_row(tail,later)),first),keep(Bool.not(String.eq(D.row_key(head),later)) && Bool.not(String.eq(D.row_key(head),first)),head,D.remove_row(D.remove_row(tail,later),first)),actual_row_removal_distributes_through_independent_head_inclusion(Bool.not(String.eq(D.row_key(head),later)),head,D.remove_row(tail,later),first)),Equal.cong(List<&2,D.Row>,List<&2,D.Row>,rows => D.remove_row(rows,first),keep(Bool.not(String.eq(D.row_key(head),later)),head,D.remove_row(tail,later)),D.remove_row(Con{head,tail},later),Equal.sym(List<&2,D.Row>,D.remove_row(Con{head,tail},later),keep(Bool.not(String.eq(D.row_key(head),later)),head,D.remove_row(tail,later)),actual_row_removal_excludes_exactly_the_matching_head_key(head,tail,later))))))))

def all(keys: List<&2,String>,rows: List<&2,D.Row>) -> List<&2,D.Row>:
  match keys:
    case Nil{}: rows
    case Con{key,tail}: all(tail,D.remove_row(rows,key))

law removing_one_key_commutes_with_a_complete_independent_key_list:
  for +keys: List<&2,String>
  for +rows: List<&2,D.Row>
  for +key: String
  {D.remove_row(all(keys,rows),key) == all(keys,D.remove_row(rows,key)) : List<&2,D.Row>}
def removing_one_key_commutes_with_a_complete_independent_key_list(keys,rows,key):
  match keys:
    case Nil{}: {==}
    case Con{+head,+tail}:
      Equal.trans(List<&2,D.Row>,D.remove_row(all(tail,D.remove_row(rows,head)),key),all(tail,D.remove_row(D.remove_row(rows,head),key)),all(tail,D.remove_row(D.remove_row(rows,key),head)),removing_one_key_commutes_with_a_complete_independent_key_list(tail,D.remove_row(rows,head),key),Equal.cong(List<&2,D.Row>,List<&2,D.Row>,items => all(tail,items),D.remove_row(D.remove_row(rows,head),key),D.remove_row(D.remove_row(rows,key),head),removing_two_keys_commutes_for_all_row_lists(rows,head,key)))

law removing_the_head_own_key_excludes_that_head_without_a_validity_assumption:
  for +key: String
  for +fields: List<&2,D.Field>
  for +tail: List<&2,D.Row>
  {D.remove_row(Con{D.Row{key,fields},tail},key) == D.remove_row(tail,key) : List<&2,D.Row>}
def removing_the_head_own_key_excludes_that_head_without_a_validity_assumption(key,fields,tail):
  Equal.cong(Bool,List<&2,D.Row>,b => Bool.pick(List<&2,D.Row>,b,D.remove_row(tail,key),Con{D.Row{key,fields},D.remove_row(tail,key)}),String.eq(key,key),True{},O.string_eq_refl(key))

law removing_every_enumerated_original_key_empties_every_finite_source_table:
  for +rows: List<&2,D.Row>
  {all(D.keys_rows(rows),rows) == Nil{} : List<&2,D.Row>}
def removing_every_enumerated_original_key_empties_every_finite_source_table(rows):
  match rows:
    case Nil{}: {==}
    case Con{D.Row{+key,+fields},+tail}:
      Equal.trans(List<&2,D.Row>,all(D.keys_rows(tail),D.remove_row(Con{D.Row{key,fields},tail},key)),all(D.keys_rows(tail),D.remove_row(tail,key)),Nil{},Equal.cong(List<&2,D.Row>,List<&2,D.Row>,items => all(D.keys_rows(tail),items),D.remove_row(Con{D.Row{key,fields},tail},key),D.remove_row(tail,key),removing_the_head_own_key_excludes_that_head_without_a_validity_assumption(key,fields,tail)),Equal.trans(List<&2,D.Row>,all(D.keys_rows(tail),D.remove_row(tail,key)),D.remove_row(all(D.keys_rows(tail),tail),key),Nil{},Equal.sym(List<&2,D.Row>,D.remove_row(all(D.keys_rows(tail),tail),key),all(D.keys_rows(tail),D.remove_row(tail,key)),removing_one_key_commutes_with_a_complete_independent_key_list(D.keys_rows(tail),tail,key)),Equal.cong(List<&2,D.Row>,List<&2,D.Row>,items => D.remove_row(items,key),all(D.keys_rows(tail),tail),Nil{},removing_every_enumerated_original_key_empties_every_finite_source_table(tail))))
