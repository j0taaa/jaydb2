# Actual consecutive replacement semantics. Last replacement wins on every
# physical matching table; no canonicality/unique-table assumption is needed.
import Base
import ./CollectionFrameProofs.bend as Frame
import ../contract/Data.bend as D

def head_case(matched: Bool,+name: String,+rows: List<&2,D.Row>,+tail: List<&2,D.Table>,+wanted: String,+first: List<&2,D.Row>,+last: List<&2,D.Row>,+actual: {String.eq(name,wanted) == matched : Bool},recursive: {D.swap_table(D.swap_table(tail,wanted,first),wanted,last) == D.swap_table(tail,wanted,last) : List<&2,D.Table>}) -> {D.swap_table(D.swap_table(Con{D.Table{name,rows},tail},wanted,first),wanted,last) == D.swap_table(Con{D.Table{name,rows},tail},wanted,last) : List<&2,D.Table>}:
  match matched:
    case True{}: Equal.trans(List<&2,D.Table>,D.swap_table(D.swap_table(Con{D.Table{name,rows},tail},wanted,first),wanted,last),D.swap_table(Con{D.Table{name,first},D.swap_table(tail,wanted,first)},wanted,last),D.swap_table(Con{D.Table{name,rows},tail},wanted,last),Equal.cong(List<&2,D.Table>,List<&2,D.Table>,tables => D.swap_table(tables,wanted,last),D.swap_table(Con{D.Table{name,rows},tail},wanted,first),Con{D.Table{name,first},D.swap_table(tail,wanted,first)},Frame.matching_head_table_replaces_only_its_rows_before_the_recursive_tail(name,rows,tail,wanted,first,actual)),Equal.trans(List<&2,D.Table>,D.swap_table(Con{D.Table{name,first},D.swap_table(tail,wanted,first)},wanted,last),Con{D.Table{name,last},D.swap_table(D.swap_table(tail,wanted,first),wanted,last)},D.swap_table(Con{D.Table{name,rows},tail},wanted,last),Frame.matching_head_table_replaces_only_its_rows_before_the_recursive_tail(name,first,D.swap_table(tail,wanted,first),wanted,last,actual),Equal.trans(List<&2,D.Table>,Con{D.Table{name,last},D.swap_table(D.swap_table(tail,wanted,first),wanted,last)},Con{D.Table{name,last},D.swap_table(tail,wanted,last)},D.swap_table(Con{D.Table{name,rows},tail},wanted,last),Equal.cong(List<&2,D.Table>,List<&2,D.Table>,tables => Con{D.Table{name,last},tables},D.swap_table(D.swap_table(tail,wanted,first),wanted,last),D.swap_table(tail,wanted,last),recursive),Equal.sym(List<&2,D.Table>,D.swap_table(Con{D.Table{name,rows},tail},wanted,last),Con{D.Table{name,last},D.swap_table(tail,wanted,last)},Frame.matching_head_table_replaces_only_its_rows_before_the_recursive_tail(name,rows,tail,wanted,last,actual)))))
    case False{}: Equal.trans(List<&2,D.Table>,D.swap_table(D.swap_table(Con{D.Table{name,rows},tail},wanted,first),wanted,last),D.swap_table(Con{D.Table{name,rows},D.swap_table(tail,wanted,first)},wanted,last),D.swap_table(Con{D.Table{name,rows},tail},wanted,last),Equal.cong(List<&2,D.Table>,List<&2,D.Table>,tables => D.swap_table(tables,wanted,last),D.swap_table(Con{D.Table{name,rows},tail},wanted,first),Con{D.Table{name,rows},D.swap_table(tail,wanted,first)},Frame.mismatched_head_table_keeps_its_rows_before_the_recursive_tail(name,rows,tail,wanted,first,actual)),Equal.trans(List<&2,D.Table>,D.swap_table(Con{D.Table{name,rows},D.swap_table(tail,wanted,first)},wanted,last),Con{D.Table{name,rows},D.swap_table(D.swap_table(tail,wanted,first),wanted,last)},D.swap_table(Con{D.Table{name,rows},tail},wanted,last),Frame.mismatched_head_table_keeps_its_rows_before_the_recursive_tail(name,rows,D.swap_table(tail,wanted,first),wanted,last,actual),Equal.trans(List<&2,D.Table>,Con{D.Table{name,rows},D.swap_table(D.swap_table(tail,wanted,first),wanted,last)},Con{D.Table{name,rows},D.swap_table(tail,wanted,last)},D.swap_table(Con{D.Table{name,rows},tail},wanted,last),Equal.cong(List<&2,D.Table>,List<&2,D.Table>,tables => Con{D.Table{name,rows},tables},D.swap_table(D.swap_table(tail,wanted,first),wanted,last),D.swap_table(tail,wanted,last),recursive),Equal.sym(List<&2,D.Table>,D.swap_table(Con{D.Table{name,rows},tail},wanted,last),Con{D.Table{name,rows},D.swap_table(tail,wanted,last)},Frame.mismatched_head_table_keeps_its_rows_before_the_recursive_tail(name,rows,tail,wanted,last,actual)))))

law last_table_replacement_overrides_every_prior_replacement:
  for +tables: List<&2,D.Table>
  for +wanted: String
  for +first: List<&2,D.Row>
  for +last: List<&2,D.Row>
  {D.swap_table(D.swap_table(tables,wanted,first),wanted,last) == D.swap_table(tables,wanted,last) : List<&2,D.Table>}
def last_table_replacement_overrides_every_prior_replacement(tables,wanted,first,last):
  match tables:
    case Nil{}: {==}
    case Con{D.Table{+name,+rows},+tail}: head_case(String.eq(name,wanted),name,rows,tail,wanted,first,last,{==},last_table_replacement_overrides_every_prior_replacement(tail,wanted,first,last))

law last_collection_replacement_overrides_every_prior_replacement:
  for +collection: D.Collection
  for +state: D.State
  for +first: List<&2,D.Row>
  for +last: List<&2,D.Row>
  {D.swap_collection(collection,D.swap_collection(collection,state,first),last) == D.swap_collection(collection,state,last) : D.State}
def last_collection_replacement_overrides_every_prior_replacement(collection,state,first,last):
  match collection state:
    case D.Users{} D.State{tables,users}: {==}
    case D.Application{+name} D.State{+tables,+users}: Equal.cong(List<&2,D.Table>,D.State,ts => D.State{ts,users},D.swap_table(D.swap_table(tables,name,first),name,last),D.swap_table(tables,name,last),last_table_replacement_overrides_every_prior_replacement(tables,name,first,last))
