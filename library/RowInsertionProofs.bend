# Independent exact replacement domain for sequential upserts. If the supplied
# complete rows have canonical UNIQUE keys, inserting them into empty storage
# returns EXACTLY those rows, not merely a renamed implementation fold.
import Base
import ../contract/Data.bend as D
import ./ValueScalarProofs.bend as Pair
import ./CollectionFrameProofs.bend as Frame
import ../proof/Foundations.bend as F
import ../proof/Orders.bend as O

def all(rows: List<&2,D.Row>,into: List<&2,D.Row>) -> List<&2,D.Row>:
  match rows:
    case Nil{}: into
    case Con{row,tail}: all(tail,D.insert_row(into,row))

def After(+previous: String,rows: List<&2,D.Row>) -> Data:
  match rows:
    case Nil{}: Unit
    case Con{row,tail}: Pair.Both<{String.is_lt(previous,D.row_key(row)) == True{} : Bool},After(previous,tail)>

def Canonical(rows: List<&2,D.Row>) -> Data:
  match rows:
    case Nil{}: Unit
    case Con{head,+tail}: Pair.Both<After(D.row_key(head),tail),Canonical(tail)>

law string_strict_order_is_irreflexive_on_all_character_data:
  for +key: String
  {String.is_lt(key,key) == False{} : Bool}
def string_strict_order_is_irreflexive_on_all_character_data(key): Equal.cong(Cmp,Bool,Cmp.is_lt,String.order(key,key),EQ{},O.string_refl(key))

def reverse_less_case(reverse: Bool,+first: String,+later: String,forward: {String.is_lt(first,later) == True{} : Bool},actual: {String.is_lt(later,first) == reverse : Bool}) -> {String.is_lt(later,first) == False{} : Bool}:
  match reverse:
    case False{}: actual
    case True{}: F.absurd_boolean({String.is_lt(later,first) == False{} : Bool},Equal.trans(Bool,False{},String.is_lt(first,first),True{},Equal.sym(Bool,String.is_lt(first,first),False{},string_strict_order_is_irreflexive_on_all_character_data(first)),O.string_lt_trans(first,later,first,forward,actual)))

law string_strict_order_is_asymmetric_on_all_character_data:
  for +first: String
  for +later: String
  for forward: {String.is_lt(first,later) == True{} : Bool}
  {String.is_lt(later,first) == False{} : Bool}
def string_strict_order_is_asymmetric_on_all_character_data(first,later,forward): reverse_less_case(String.is_lt(later,first),first,later,forward,{==})

law inserting_above_a_smaller_head_preserves_that_head_exactly:
  for +head: D.Row
  for +tail: List<&2,D.Row>
  for +new: D.Row
  for +ordered: {String.is_lt(D.row_key(head),D.row_key(new)) == True{} : Bool}
  {D.insert_row(Con{head,tail},new) == Con{head,D.insert_row(tail,new)} : List<&2,D.Row>}
def inserting_above_a_smaller_head_preserves_that_head_exactly(head,tail,new,ordered):
  match head new:
    case D.Row{+first,+fields} D.Row{+later,+values}:
      Equal.trans(List<&2,D.Row>,D.insert_row(Con{D.Row{first,fields},tail},D.Row{later,values}),Bool.pick(List<&2,D.Row>,String.eq(later,first),Con{D.Row{later,values},tail},Con{D.Row{first,fields},D.insert_row(tail,D.Row{later,values})}),Con{D.Row{first,fields},D.insert_row(tail,D.Row{later,values})},Equal.cong(Bool,List<&2,D.Row>,b => Bool.pick(List<&2,D.Row>,b,Con{D.Row{later,values},Con{D.Row{first,fields},tail}},Bool.pick(List<&2,D.Row>,String.eq(later,first),Con{D.Row{later,values},tail},Con{D.Row{first,fields},D.insert_row(tail,D.Row{later,values})})),String.is_lt(later,first),False{},string_strict_order_is_asymmetric_on_all_character_data(first,later,ordered)),Equal.cong(Bool,List<&2,D.Row>,b => Bool.pick(List<&2,D.Row>,b,Con{D.Row{later,values},tail},Con{D.Row{first,fields},D.insert_row(tail,D.Row{later,values})}),String.eq(later,first),False{},Frame.different_strings_have_symmetric_inequality(first,later,O.string_lt_neq(first,later,ordered))))

law larger_key_upserts_preserve_an_independent_smaller_prefix_head:
  for +rows: List<&2,D.Row>
  for +head: D.Row
  for +into: List<&2,D.Row>
  for ordered: After(D.row_key(head),rows)
  {all(rows,Con{head,into}) == Con{head,all(rows,into)} : List<&2,D.Row>}
def larger_key_upserts_preserve_an_independent_smaller_prefix_head(rows,head,into,ordered):
  match rows ordered:
    case Nil{} Unit{}: {==}
    case Con{+new,+tail} Pair.Both{first,rest}:
      Equal.trans(List<&2,D.Row>,all(tail,D.insert_row(Con{head,into},new)),all(tail,Con{head,D.insert_row(into,new)}),Con{head,all(tail,D.insert_row(into,new))},Equal.cong(List<&2,D.Row>,List<&2,D.Row>,items => all(tail,items),D.insert_row(Con{head,into},new),Con{head,D.insert_row(into,new)},inserting_above_a_smaller_head_preserves_that_head_exactly(head,into,new,first)),larger_key_upserts_preserve_an_independent_smaller_prefix_head(tail,head,D.insert_row(into,new),rest))

law upserting_canonical_unique_replacement_rows_into_empty_storage_is_exact_replacement:
  for +rows: List<&2,D.Row>
  for canonical: Canonical(rows)
  {all(rows,Nil{}) == rows : List<&2,D.Row>}
def upserting_canonical_unique_replacement_rows_into_empty_storage_is_exact_replacement(rows,canonical):
  match rows canonical:
    case Nil{} Unit{}: {==}
    case Con{+head,+tail} Pair.Both{after,rest}:
      Equal.trans(List<&2,D.Row>,all(tail,Con{head,Nil{}}),Con{head,all(tail,Nil{})},Con{head,tail},larger_key_upserts_preserve_an_independent_smaller_prefix_head(tail,head,Nil{},after),Equal.cong(List<&2,D.Row>,List<&2,D.Row>,items => Con{head,items},all(tail,Nil{}),tail,upserting_canonical_unique_replacement_rows_into_empty_storage_is_exact_replacement(tail,rest)))

law all_pair_key_order_transports_through_a_strictly_smaller_prefix:
  for +first: String
  for +later: String
  for +rows: List<&2,D.Row>
  for +ordered: {String.is_lt(first,later) == True{} : Bool}
  for rest: After(later,rows)
  After(first,rows)
def all_pair_key_order_transports_through_a_strictly_smaller_prefix(first,later,rows,ordered,rest):
  match rows rest:
    case Nil{} Unit{}: Unit{}
    case Con{+head,+tail} Pair.Both{next,more}: Pair.Both{O.string_lt_trans(first,later,D.row_key(head),ordered,next),all_pair_key_order_transports_through_a_strictly_smaller_prefix(first,later,tail,ordered,more)}

law adjacent_key_order_and_canonical_tail_imply_all_pair_prefix_order:
  for +previous: String
  for +rows: List<&2,D.Row>
  for +immediate: {D.rows_later(rows,previous) == True{} : Bool}
  for canonical: Canonical(rows)
  After(previous,rows)
def adjacent_key_order_and_canonical_tail_imply_all_pair_prefix_order(previous,rows,immediate,canonical):
  match rows canonical:
    case Nil{} Unit{}: Unit{}
    case Con{D.Row{+key,fields},+tail} Pair.Both{after,rest}: Pair.Both{immediate,all_pair_key_order_transports_through_a_strictly_smaller_prefix(previous,key,tail,immediate,after)}

law actual_valid_rows_have_independent_canonical_unique_keys:
  for +rows: List<&2,D.Row>
  for +schema: D.SchemaTable
  for +valid: {D.rows_valid_cases(rows,schema) == True{} : Bool}
  Canonical(rows)
def actual_valid_rows_have_independent_canonical_unique_keys(rows,schema,valid):
  match rows:
    case Nil{}: Unit{}
    case Con{D.Row{+key,+fields},+tail}:
      +tail_canonical = actual_valid_rows_have_independent_canonical_unique_keys(tail,schema,F.and_boolean_right(D.row_is_valid(schema,D.Row{key,fields}) && D.rows_later(tail,key),D.rows_valid_cases(tail,schema),valid))
      Pair.Both{adjacent_key_order_and_canonical_tail_imply_all_pair_prefix_order(key,tail,F.and_boolean_right(D.row_is_valid(schema,D.Row{key,fields}),D.rows_later(tail,key),F.and_boolean_left(D.row_is_valid(schema,D.Row{key,fields}) && D.rows_later(tail,key),D.rows_valid_cases(tail,schema),valid)),tail_canonical),tail_canonical}
