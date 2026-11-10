# Actual row upserts preserve every other key lookup and expose exactly the
# supplied new row at its own key, for ALL finite row DATA (no ordering premise).
import Base
import ../contract/Data.bend as D
import ./CollectionFrameProofs.bend as Frame
import ../proof/Orders.bend as O

law the_head_row_is_found_at_its_exact_own_key:
  for +row: D.Row
  for +tail: List<&2,D.Row>
  {D.find_row(Con{row,tail},D.row_key(row)) == Some{row} : Maybe<&2,D.Row>}
def the_head_row_is_found_at_its_exact_own_key(row,tail):
  match row:
    case D.Row{+key,+fields}: Equal.cong(Bool,Maybe<&2,D.Row>,same => Bool.pick(Maybe<&2,D.Row>,same,Some{D.Row{key,fields}},D.find_row(tail,key)),String.eq(key,key),True{},O.string_eq_refl(key))

law excluding_a_prefix_row_key_keeps_the_exact_tail_lookup:
  for +row: D.Row
  for +tail: List<&2,D.Row>
  for +wanted: String
  for different: {String.eq(D.row_key(row),wanted) == False{} : Bool}
  {D.find_row(Con{row,tail},wanted) == D.find_row(tail,wanted) : Maybe<&2,D.Row>}
def excluding_a_prefix_row_key_keeps_the_exact_tail_lookup(row,tail,wanted,different):
  match row:
    case D.Row{+key,+fields}: Equal.cong(Bool,Maybe<&2,D.Row>,same => Bool.pick(Maybe<&2,D.Row>,same,Some{D.Row{key,fields}},D.find_row(tail,wanted)),String.eq(key,wanted),False{},different)

def own_known(less: Bool,same: Bool,+head: D.Row,+tail: List<&2,D.Row>,+new: D.Row,+same_actual: {String.eq(D.row_key(new),D.row_key(head)) == same : Bool},recursive: {D.find_row(D.insert_row(tail,new),D.row_key(new)) == Some{new} : Maybe<&2,D.Row>}) -> {D.find_row(Bool.pick(List<&2,D.Row>,less,Con{new,Con{head,tail}},Bool.pick(List<&2,D.Row>,same,Con{new,tail},Con{head,D.insert_row(tail,new)})),D.row_key(new)) == Some{new} : Maybe<&2,D.Row>}:
  match less same:
    case True{} same: the_head_row_is_found_at_its_exact_own_key(new,Con{head,tail})
    case False{} True{}: the_head_row_is_found_at_its_exact_own_key(new,tail)
    case False{} False{}: Equal.trans(Maybe<&2,D.Row>,D.find_row(Con{head,D.insert_row(tail,new)},D.row_key(new)),D.find_row(D.insert_row(tail,new),D.row_key(new)),Some{new},excluding_a_prefix_row_key_keeps_the_exact_tail_lookup(head,D.insert_row(tail,new),D.row_key(new),Frame.different_strings_have_symmetric_inequality(D.row_key(new),D.row_key(head),same_actual)),recursive)


def own_case(less: Bool,same: Bool,+head: D.Row,+tail: List<&2,D.Row>,+new: D.Row,less_actual: {String.is_lt(D.row_key(new),D.row_key(head)) == less : Bool},+same_actual: {String.eq(D.row_key(new),D.row_key(head)) == same : Bool},recursive: {D.find_row(D.insert_row(tail,new),D.row_key(new)) == Some{new} : Maybe<&2,D.Row>}) -> {D.find_row(D.insert_row(Con{head,tail},new),D.row_key(new)) == Some{new} : Maybe<&2,D.Row>}:
  %Equal.sym(Bool,String.is_lt(D.row_key(new),D.row_key(head)),less,less_actual) : {D.find_row(Bool.pick(List<&2,D.Row>,_,Con{new,Con{head,tail}},Bool.pick(List<&2,D.Row>,String.eq(D.row_key(new),D.row_key(head)),Con{new,tail},Con{head,D.insert_row(tail,new)})),D.row_key(new)) == Some{new} : Maybe<&2,D.Row>}
  %Equal.sym(Bool,String.eq(D.row_key(new),D.row_key(head)),same,same_actual) : {D.find_row(Bool.pick(List<&2,D.Row>,less,Con{new,Con{head,tail}},Bool.pick(List<&2,D.Row>,_,Con{new,tail},Con{head,D.insert_row(tail,new)})),D.row_key(new)) == Some{new} : Maybe<&2,D.Row>}
  own_known(less,same,head,tail,new,same_actual,recursive)

law an_actual_upsert_exposes_exactly_the_new_row_at_its_own_key:
  for +rows: List<&2,D.Row>
  for +new: D.Row
  {D.find_row(D.insert_row(rows,new),D.row_key(new)) == Some{new} : Maybe<&2,D.Row>}
def an_actual_upsert_exposes_exactly_the_new_row_at_its_own_key(rows,new):
  match rows:
    case Nil{}: the_head_row_is_found_at_its_exact_own_key(new,Nil{})
    case Con{+head,+tail}: own_case(String.is_lt(D.row_key(new),D.row_key(head)),String.eq(D.row_key(new),D.row_key(head)),head,tail,new,{==},{==},an_actual_upsert_exposes_exactly_the_new_row_at_its_own_key(tail,new))

def prefix_lookup(+head: D.Row,+first: List<&2,D.Row>,+last: List<&2,D.Row>,+wanted: String,same: {D.find_row(first,wanted) == D.find_row(last,wanted) : Maybe<&2,D.Row>}) -> {D.find_row(Con{head,first},wanted) == D.find_row(Con{head,last},wanted) : Maybe<&2,D.Row>}:
  match head:
    case D.Row{+key,+fields}: Equal.cong(Maybe<&2,D.Row>,Maybe<&2,D.Row>,found => Bool.pick(Maybe<&2,D.Row>,String.eq(key,wanted),Some{D.Row{key,fields}},found),D.find_row(first,wanted),D.find_row(last,wanted),same)

def equal_prefix_exclusion(+new_key: String,+head_key: String,+wanted: String,same: {String.eq(new_key,head_key) == True{} : Bool},different: {String.eq(new_key,wanted) == False{} : Bool}) -> {String.eq(head_key,wanted) == False{} : Bool}:
  Equal.trans(Bool,String.eq(head_key,wanted),String.eq(new_key,wanted),False{},Equal.cong(String,Bool,key => String.eq(key,wanted),head_key,new_key,Equal.sym(String,new_key,head_key,O.string_equal(new_key,head_key,same))),different)

def other_known(less: Bool,same: Bool,+head: D.Row,+tail: List<&2,D.Row>,+new: D.Row,+wanted: String,+same_actual: {String.eq(D.row_key(new),D.row_key(head)) == same : Bool},+different: {String.eq(D.row_key(new),wanted) == False{} : Bool},recursive: {D.find_row(D.insert_row(tail,new),wanted) == D.find_row(tail,wanted) : Maybe<&2,D.Row>}) -> {D.find_row(Bool.pick(List<&2,D.Row>,less,Con{new,Con{head,tail}},Bool.pick(List<&2,D.Row>,same,Con{new,tail},Con{head,D.insert_row(tail,new)})),wanted) == D.find_row(Con{head,tail},wanted) : Maybe<&2,D.Row>}:
  match less same:
    case True{} same: excluding_a_prefix_row_key_keeps_the_exact_tail_lookup(new,Con{head,tail},wanted,different)
    case False{} True{}: Equal.trans(Maybe<&2,D.Row>,D.find_row(Con{new,tail},wanted),D.find_row(tail,wanted),D.find_row(Con{head,tail},wanted),excluding_a_prefix_row_key_keeps_the_exact_tail_lookup(new,tail,wanted,different),Equal.sym(Maybe<&2,D.Row>,D.find_row(Con{head,tail},wanted),D.find_row(tail,wanted),excluding_a_prefix_row_key_keeps_the_exact_tail_lookup(head,tail,wanted,equal_prefix_exclusion(D.row_key(new),D.row_key(head),wanted,same_actual,different))))
    case False{} False{}: prefix_lookup(head,D.insert_row(tail,new),tail,wanted,recursive)


def other_case(less: Bool,same: Bool,+head: D.Row,+tail: List<&2,D.Row>,+new: D.Row,+wanted: String,less_actual: {String.is_lt(D.row_key(new),D.row_key(head)) == less : Bool},+same_actual: {String.eq(D.row_key(new),D.row_key(head)) == same : Bool},+different: {String.eq(D.row_key(new),wanted) == False{} : Bool},recursive: {D.find_row(D.insert_row(tail,new),wanted) == D.find_row(tail,wanted) : Maybe<&2,D.Row>}) -> {D.find_row(D.insert_row(Con{head,tail},new),wanted) == D.find_row(Con{head,tail},wanted) : Maybe<&2,D.Row>}:
  %Equal.sym(Bool,String.is_lt(D.row_key(new),D.row_key(head)),less,less_actual) : {D.find_row(Bool.pick(List<&2,D.Row>,_,Con{new,Con{head,tail}},Bool.pick(List<&2,D.Row>,String.eq(D.row_key(new),D.row_key(head)),Con{new,tail},Con{head,D.insert_row(tail,new)})),wanted) == D.find_row(Con{head,tail},wanted) : Maybe<&2,D.Row>}
  %Equal.sym(Bool,String.eq(D.row_key(new),D.row_key(head)),same,same_actual) : {D.find_row(Bool.pick(List<&2,D.Row>,less,Con{new,Con{head,tail}},Bool.pick(List<&2,D.Row>,_,Con{new,tail},Con{head,D.insert_row(tail,new)})),wanted) == D.find_row(Con{head,tail},wanted) : Maybe<&2,D.Row>}
  other_known(less,same,head,tail,new,wanted,same_actual,different,recursive)

law an_actual_upsert_preserves_every_other_exact_key_lookup:
  for +rows: List<&2,D.Row>
  for +new: D.Row
  for +wanted: String
  for +different: {String.eq(D.row_key(new),wanted) == False{} : Bool}
  {D.find_row(D.insert_row(rows,new),wanted) == D.find_row(rows,wanted) : Maybe<&2,D.Row>}
def an_actual_upsert_preserves_every_other_exact_key_lookup(rows,new,wanted,different):
  match rows:
    case Nil{}: excluding_a_prefix_row_key_keeps_the_exact_tail_lookup(new,Nil{},wanted,different)
    case Con{+head,+tail}: other_case(String.is_lt(D.row_key(new),D.row_key(head)),String.eq(D.row_key(new),D.row_key(head)),head,tail,new,wanted,{==},{==},different,an_actual_upsert_preserves_every_other_exact_key_lookup(tail,new,wanted,different))
