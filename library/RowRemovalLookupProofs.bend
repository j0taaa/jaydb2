# Actual row deletion has exact lookup meaning on ALL finite row DATA.
import Base
import ./RowLookupProofs.bend as Row
import ../contract/Data.bend as D
import ../proof/Orders.bend as O

def own_known(same: Bool,+head: D.Row,+tail: List<&2,D.Row>,+key: String,actual: {String.eq(D.row_key(head),key) == same : Bool},recursive: {D.find_row(D.remove_row(tail,key),key) == None{} : Maybe<&2,D.Row>}) -> {D.find_row(Bool.pick(List<&2,D.Row>,same,D.remove_row(tail,key),Con{head,D.remove_row(tail,key)}),key) == None{} : Maybe<&2,D.Row>}:
  match same:
    case True{}: recursive
    case False{}: Equal.trans(Maybe<&2,D.Row>,D.find_row(Con{head,D.remove_row(tail,key)},key),D.find_row(D.remove_row(tail,key),key),None{},Row.excluding_a_prefix_row_key_keeps_the_exact_tail_lookup(head,D.remove_row(tail,key),key,actual),recursive)
def own_case(same: Bool,+head: D.Row,+tail: List<&2,D.Row>,+key: String,+actual: {String.eq(D.row_key(head),key) == same : Bool},recursive: {D.find_row(D.remove_row(tail,key),key) == None{} : Maybe<&2,D.Row>}) -> {D.find_row(D.remove_row(Con{head,tail},key),key) == None{} : Maybe<&2,D.Row>}:
  %Equal.sym(Bool,String.eq(D.row_key(head),key),same,actual) : {D.find_row(Bool.pick(List<&2,D.Row>,_,D.remove_row(tail,key),Con{head,D.remove_row(tail,key)}),key) == None{} : Maybe<&2,D.Row>}
  own_known(same,head,tail,key,actual,recursive)

law actual_row_removal_excludes_every_occurrence_of_its_own_key:
  for +rows: List<&2,D.Row>
  for +key: String
  {D.find_row(D.remove_row(rows,key),key) == None{} : Maybe<&2,D.Row>}
def actual_row_removal_excludes_every_occurrence_of_its_own_key(rows,key):
  match rows:
    case Nil{}: {==}
    case Con{+head,+tail}: own_case(String.eq(D.row_key(head),key),head,tail,key,{==},actual_row_removal_excludes_every_occurrence_of_its_own_key(tail,key))

def other_known(same: Bool,+head: D.Row,+tail: List<&2,D.Row>,+key: String,+wanted: String,actual: {String.eq(D.row_key(head),key) == same : Bool},different: {String.eq(key,wanted) == False{} : Bool},recursive: {D.find_row(D.remove_row(tail,key),wanted) == D.find_row(tail,wanted) : Maybe<&2,D.Row>}) -> {D.find_row(Bool.pick(List<&2,D.Row>,same,D.remove_row(tail,key),Con{head,D.remove_row(tail,key)}),wanted) == D.find_row(Con{head,tail},wanted) : Maybe<&2,D.Row>}:
  match same:
    case True{}: Equal.trans(Maybe<&2,D.Row>,D.find_row(D.remove_row(tail,key),wanted),D.find_row(tail,wanted),D.find_row(Con{head,tail},wanted),recursive,Equal.sym(Maybe<&2,D.Row>,D.find_row(Con{head,tail},wanted),D.find_row(tail,wanted),Row.excluding_a_prefix_row_key_keeps_the_exact_tail_lookup(head,tail,wanted,Equal.trans(Bool,String.eq(D.row_key(head),wanted),String.eq(key,wanted),False{},Equal.cong(String,Bool,k => String.eq(k,wanted),D.row_key(head),key,O.string_equal(D.row_key(head),key,actual)),different))))
    case False{}: Row.prefix_lookup(head,D.remove_row(tail,key),tail,wanted,recursive)
def other_case(same: Bool,+head: D.Row,+tail: List<&2,D.Row>,+key: String,+wanted: String,+actual: {String.eq(D.row_key(head),key) == same : Bool},different: {String.eq(key,wanted) == False{} : Bool},recursive: {D.find_row(D.remove_row(tail,key),wanted) == D.find_row(tail,wanted) : Maybe<&2,D.Row>}) -> {D.find_row(D.remove_row(Con{head,tail},key),wanted) == D.find_row(Con{head,tail},wanted) : Maybe<&2,D.Row>}:
  %Equal.sym(Bool,String.eq(D.row_key(head),key),same,actual) : {D.find_row(Bool.pick(List<&2,D.Row>,_,D.remove_row(tail,key),Con{head,D.remove_row(tail,key)}),wanted) == D.find_row(Con{head,tail},wanted) : Maybe<&2,D.Row>}
  other_known(same,head,tail,key,wanted,actual,different,recursive)

law actual_row_removal_preserves_every_other_exact_key_lookup:
  for +rows: List<&2,D.Row>
  for +key: String
  for +wanted: String
  for +different: {String.eq(key,wanted) == False{} : Bool}
  {D.find_row(D.remove_row(rows,key),wanted) == D.find_row(rows,wanted) : Maybe<&2,D.Row>}
def actual_row_removal_preserves_every_other_exact_key_lookup(rows,key,wanted,different):
  match rows:
    case Nil{}: {==}
    case Con{+head,+tail}: other_case(String.eq(D.row_key(head),key),head,tail,key,wanted,{==},different,actual_row_removal_preserves_every_other_exact_key_lookup(tail,key,wanted,different))
