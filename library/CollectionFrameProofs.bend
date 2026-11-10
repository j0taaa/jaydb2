# Actual Data.swap_collection view laws, not a presumed business postcondition.
# Input collection existence is needed only for the replaced view; distinct
# other collection views are preserved for all State DATA, including missing
# collections and duplicate/unsorted physical table lists.
import Base
import ../contract/Data.bend as D
import ../proof/Foundations.bend as F
import ../proof/Orders.bend as O

def view(tables: List<&2,D.Table>,name: String) -> Maybe<&2,List<&2,D.Row>>:
  D.rows_table(D.find_table(tables,name))

law equal_head_table_is_the_exact_observed_row_view:
  for +name: String
  for +rows: List<&2,D.Row>
  for +tail: List<&2,D.Table>
  for +wanted: String
  for same: {String.eq(name,wanted) == True{} : Bool}
  {view(Con{D.Table{name,rows},tail},wanted) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
def equal_head_table_is_the_exact_observed_row_view(name,rows,tail,wanted,same):
  Equal.cong(Bool,Maybe<&2,List<&2,D.Row>>,b => D.rows_table(Bool.pick(Maybe<&2,D.Table>,b,Some{D.Table{name,rows}},D.find_table(tail,wanted))),String.eq(name,wanted),True{},same)

law different_head_table_does_not_change_the_observed_row_view:
  for +name: String
  for +rows: List<&2,D.Row>
  for +tail: List<&2,D.Table>
  for +wanted: String
  for different: {String.eq(name,wanted) == False{} : Bool}
  {view(Con{D.Table{name,rows},tail},wanted) == view(tail,wanted) : Maybe<&2,List<&2,D.Row>>}
def different_head_table_does_not_change_the_observed_row_view(name,rows,tail,wanted,different):
  Equal.cong(Bool,Maybe<&2,List<&2,D.Row>>,b => D.rows_table(Bool.pick(Maybe<&2,D.Table>,b,Some{D.Table{name,rows}},D.find_table(tail,wanted))),String.eq(name,wanted),False{},different)

law matching_head_table_replaces_only_its_rows_before_the_recursive_tail:
  for +name: String
  for +rows: List<&2,D.Row>
  for +tail: List<&2,D.Table>
  for +wanted: String
  for +replacement: List<&2,D.Row>
  for same: {String.eq(name,wanted) == True{} : Bool}
  {D.swap_table(Con{D.Table{name,rows},tail},wanted,replacement) == Con{D.Table{name,replacement},D.swap_table(tail,wanted,replacement)} : List<&2,D.Table>}
def matching_head_table_replaces_only_its_rows_before_the_recursive_tail(name,rows,tail,wanted,replacement,same):
  Equal.cong(Bool,List<&2,D.Table>,b => Con{Bool.pick(D.Table,b,D.Table{name,replacement},D.Table{name,rows}),D.swap_table(tail,wanted,replacement)},String.eq(name,wanted),True{},same)

law mismatched_head_table_keeps_its_rows_before_the_recursive_tail:
  for +name: String
  for +rows: List<&2,D.Row>
  for +tail: List<&2,D.Table>
  for +wanted: String
  for +replacement: List<&2,D.Row>
  for different: {String.eq(name,wanted) == False{} : Bool}
  {D.swap_table(Con{D.Table{name,rows},tail},wanted,replacement) == Con{D.Table{name,rows},D.swap_table(tail,wanted,replacement)} : List<&2,D.Table>}
def mismatched_head_table_keeps_its_rows_before_the_recursive_tail(name,rows,tail,wanted,replacement,different):
  Equal.cong(Bool,List<&2,D.Table>,b => Con{Bool.pick(D.Table,b,D.Table{name,replacement},D.Table{name,rows}),D.swap_table(tail,wanted,replacement)},String.eq(name,wanted),False{},different)

def same_case(same: Bool,+name: String,+rows: List<&2,D.Row>,+tail: List<&2,D.Table>,+wanted: String,+replacement: List<&2,D.Row>,+previous: List<&2,D.Row>,+actual: {String.eq(name,wanted) == same : Bool},found: {view(Con{D.Table{name,rows},tail},wanted) == Some{previous} : Maybe<&2,List<&2,D.Row>>},recursive: {view(tail,wanted) == Some{previous} : Maybe<&2,List<&2,D.Row>>} -> {view(D.swap_table(tail,wanted,replacement),wanted) == Some{replacement} : Maybe<&2,List<&2,D.Row>>}) -> {view(D.swap_table(Con{D.Table{name,rows},tail},wanted,replacement),wanted) == Some{replacement} : Maybe<&2,List<&2,D.Row>>}:
  match same:
    case True{}:
      Equal.trans(Maybe<&2,List<&2,D.Row>>,view(D.swap_table(Con{D.Table{name,rows},tail},wanted,replacement),wanted),view(Con{D.Table{name,replacement},D.swap_table(tail,wanted,replacement)},wanted),Some{replacement},Equal.cong(List<&2,D.Table>,Maybe<&2,List<&2,D.Row>>,tables => view(tables,wanted),D.swap_table(Con{D.Table{name,rows},tail},wanted,replacement),Con{D.Table{name,replacement},D.swap_table(tail,wanted,replacement)},matching_head_table_replaces_only_its_rows_before_the_recursive_tail(name,rows,tail,wanted,replacement,actual)),equal_head_table_is_the_exact_observed_row_view(name,replacement,D.swap_table(tail,wanted,replacement),wanted,actual))
    case False{}:
      Equal.trans(Maybe<&2,List<&2,D.Row>>,view(D.swap_table(Con{D.Table{name,rows},tail},wanted,replacement),wanted),view(Con{D.Table{name,rows},D.swap_table(tail,wanted,replacement)},wanted),Some{replacement},Equal.cong(List<&2,D.Table>,Maybe<&2,List<&2,D.Row>>,tables => view(tables,wanted),D.swap_table(Con{D.Table{name,rows},tail},wanted,replacement),Con{D.Table{name,rows},D.swap_table(tail,wanted,replacement)},mismatched_head_table_keeps_its_rows_before_the_recursive_tail(name,rows,tail,wanted,replacement,actual)),Equal.trans(Maybe<&2,List<&2,D.Row>>,view(Con{D.Table{name,rows},D.swap_table(tail,wanted,replacement)},wanted),view(D.swap_table(tail,wanted,replacement),wanted),Some{replacement},different_head_table_does_not_change_the_observed_row_view(name,rows,D.swap_table(tail,wanted,replacement),wanted,actual),recursive(Equal.trans(Maybe<&2,List<&2,D.Row>>,view(tail,wanted),view(Con{D.Table{name,rows},tail},wanted),Some{previous},Equal.sym(Maybe<&2,List<&2,D.Row>>,view(Con{D.Table{name,rows},tail},wanted),view(tail,wanted),different_head_table_does_not_change_the_observed_row_view(name,rows,tail,wanted,actual)),found))))

law swapping_an_existing_table_replaces_its_exact_input_row_view:
  for +tables: List<&2,D.Table>
  for +wanted: String
  for +previous: List<&2,D.Row>
  for +replacement: List<&2,D.Row>
  for found: {view(tables,wanted) == Some{previous} : Maybe<&2,List<&2,D.Row>>}
  {view(D.swap_table(tables,wanted,replacement),wanted) == Some{replacement} : Maybe<&2,List<&2,D.Row>>}
def swapping_an_existing_table_replaces_its_exact_input_row_view(tables,wanted,previous,replacement,found):
  match tables:
    case Nil{}: Empty.absurd({view(D.swap_table(Nil{},wanted,replacement),wanted) == Some{replacement} : Maybe<&2,List<&2,D.Row>>},F.none_negative_some(List<&2,D.Row>,previous,found))
    case Con{D.Table{+name,+rows},+tail}: same_case(String.eq(name,wanted),name,rows,tail,wanted,replacement,previous,{==},found,tail_found => swapping_an_existing_table_replaces_its_exact_input_row_view(tail,wanted,previous,replacement,tail_found))

law replacing_an_existing_collection_has_the_exact_new_row_view:
  for +collection: D.Collection
  for +state: D.State
  for +previous: List<&2,D.Row>
  for +replacement: List<&2,D.Row>
  for found: {D.rows_collection(collection,state) == Some{previous} : Maybe<&2,List<&2,D.Row>>}
  {D.rows_collection(collection,D.swap_collection(collection,state,replacement)) == Some{replacement} : Maybe<&2,List<&2,D.Row>>}
def replacing_an_existing_collection_has_the_exact_new_row_view(collection,state,previous,replacement,found):
  match collection state:
    case D.Users{} D.State{tables,users}: {==}
    case D.Application{+name} D.State{+tables,users}: swapping_an_existing_table_replaces_its_exact_input_row_view(tables,name,previous,replacement,found)

def same_names_cannot_be_separate(+head: String,+target: String,+watched: String,target_equal: {String.eq(head,target) == True{} : Bool},watched_equal: {String.eq(head,watched) == True{} : Bool},different: {String.eq(target,watched) == False{} : Bool}) -> Empty:
  +same = Equal.trans(String,target,head,watched,Equal.sym(String,head,target,O.string_equal(head,target,target_equal)),O.string_equal(head,watched,watched_equal))
  F.false_negative_true(Equal.trans(Bool,False{},String.eq(target,watched),True{},Equal.sym(Bool,String.eq(target,watched),False{},different),Equal.trans(Bool,String.eq(target,watched),String.eq(watched,watched),True{},Equal.cong(String,Bool,name => String.eq(name,watched),target,watched,same),O.string_eq_refl(watched))))

def unwatched_head_frame(+name: String,+rows: List<&2,D.Row>,+head_rows: List<&2,D.Row>,+tail: List<&2,D.Table>,+target: String,+watched: String,+replacement: List<&2,D.Row>,+not_watched: {String.eq(name,watched) == False{} : Bool},swapped: {D.swap_table(Con{D.Table{name,rows},tail},target,replacement) == Con{D.Table{name,head_rows},D.swap_table(tail,target,replacement)} : List<&2,D.Table>},recursive: {view(D.swap_table(tail,target,replacement),watched) == view(tail,watched) : Maybe<&2,List<&2,D.Row>>}) -> {view(D.swap_table(Con{D.Table{name,rows},tail},target,replacement),watched) == view(Con{D.Table{name,rows},tail},watched) : Maybe<&2,List<&2,D.Row>>}:
  Equal.trans(Maybe<&2,List<&2,D.Row>>,view(D.swap_table(Con{D.Table{name,rows},tail},target,replacement),watched),view(Con{D.Table{name,head_rows},D.swap_table(tail,target,replacement)},watched),view(Con{D.Table{name,rows},tail},watched),Equal.cong(List<&2,D.Table>,Maybe<&2,List<&2,D.Row>>,tables => view(tables,watched),D.swap_table(Con{D.Table{name,rows},tail},target,replacement),Con{D.Table{name,head_rows},D.swap_table(tail,target,replacement)},swapped),Equal.trans(Maybe<&2,List<&2,D.Row>>,view(Con{D.Table{name,head_rows},D.swap_table(tail,target,replacement)},watched),view(D.swap_table(tail,target,replacement),watched),view(Con{D.Table{name,rows},tail},watched),different_head_table_does_not_change_the_observed_row_view(name,head_rows,D.swap_table(tail,target,replacement),watched,not_watched),Equal.trans(Maybe<&2,List<&2,D.Row>>,view(D.swap_table(tail,target,replacement),watched),view(tail,watched),view(Con{D.Table{name,rows},tail},watched),recursive,Equal.sym(Maybe<&2,List<&2,D.Row>>,view(Con{D.Table{name,rows},tail},watched),view(tail,watched),different_head_table_does_not_change_the_observed_row_view(name,rows,tail,watched,not_watched)))))

def other_case(to_target: Bool,to_watched: Bool,+name: String,+rows: List<&2,D.Row>,+tail: List<&2,D.Table>,+target: String,+watched: String,+replacement: List<&2,D.Row>,+target_actual: {String.eq(name,target) == to_target : Bool},+watched_actual: {String.eq(name,watched) == to_watched : Bool},different: {String.eq(target,watched) == False{} : Bool},recursive: {view(D.swap_table(tail,target,replacement),watched) == view(tail,watched) : Maybe<&2,List<&2,D.Row>>}) -> {view(D.swap_table(Con{D.Table{name,rows},tail},target,replacement),watched) == view(Con{D.Table{name,rows},tail},watched) : Maybe<&2,List<&2,D.Row>>}:
  match to_target to_watched:
    case True{} True{}: Empty.absurd({view(D.swap_table(Con{D.Table{name,rows},tail},target,replacement),watched) == view(Con{D.Table{name,rows},tail},watched) : Maybe<&2,List<&2,D.Row>>},same_names_cannot_be_separate(name,target,watched,target_actual,watched_actual,different))
    case True{} False{}: unwatched_head_frame(name,rows,replacement,tail,target,watched,replacement,watched_actual,matching_head_table_replaces_only_its_rows_before_the_recursive_tail(name,rows,tail,target,replacement,target_actual),recursive)
    case False{} False{}: unwatched_head_frame(name,rows,rows,tail,target,watched,replacement,watched_actual,mismatched_head_table_keeps_its_rows_before_the_recursive_tail(name,rows,tail,target,replacement,target_actual),recursive)
    case False{} True{}:
      Equal.trans(Maybe<&2,List<&2,D.Row>>,view(D.swap_table(Con{D.Table{name,rows},tail},target,replacement),watched),view(Con{D.Table{name,rows},D.swap_table(tail,target,replacement)},watched),view(Con{D.Table{name,rows},tail},watched),Equal.cong(List<&2,D.Table>,Maybe<&2,List<&2,D.Row>>,tables => view(tables,watched),D.swap_table(Con{D.Table{name,rows},tail},target,replacement),Con{D.Table{name,rows},D.swap_table(tail,target,replacement)},mismatched_head_table_keeps_its_rows_before_the_recursive_tail(name,rows,tail,target,replacement,target_actual)),Equal.trans(Maybe<&2,List<&2,D.Row>>,view(Con{D.Table{name,rows},D.swap_table(tail,target,replacement)},watched),Some{rows},view(Con{D.Table{name,rows},tail},watched),equal_head_table_is_the_exact_observed_row_view(name,rows,D.swap_table(tail,target,replacement),watched,watched_actual),Equal.sym(Maybe<&2,List<&2,D.Row>>,view(Con{D.Table{name,rows},tail},watched),Some{rows},equal_head_table_is_the_exact_observed_row_view(name,rows,tail,watched,watched_actual))))

law swapping_one_named_table_preserves_every_distinct_named_collection_view:
  for +tables: List<&2,D.Table>
  for +target: String
  for +watched: String
  for +replacement: List<&2,D.Row>
  for +different: {String.eq(target,watched) == False{} : Bool}
  {view(D.swap_table(tables,target,replacement),watched) == view(tables,watched) : Maybe<&2,List<&2,D.Row>>}
def swapping_one_named_table_preserves_every_distinct_named_collection_view(tables,target,watched,replacement,different):
  match tables:
    case Nil{}: {==}
    case Con{D.Table{+name,+rows},+tail}: other_case(String.eq(name,target),String.eq(name,watched),name,rows,tail,target,watched,replacement,{==},{==},different,swapping_one_named_table_preserves_every_distinct_named_collection_view(tail,target,watched,replacement,different))

def Separate(target: D.Collection,watched: D.Collection) -> Data:
  match target watched:
    case D.Users{} D.Users{}: {False{} == True{} : Bool}
    case D.Users{} D.Application{name}: Unit
    case D.Application{name} D.Users{}: Unit
    case D.Application{target} D.Application{watched}: {String.eq(target,watched) == False{} : Bool}

law replacing_a_collection_preserves_every_separate_collection_view:
  for +target: D.Collection
  for +watched: D.Collection
  for +state: D.State
  for +replacement: List<&2,D.Row>
  for separate: Separate(target,watched)
  {D.rows_collection(watched,D.swap_collection(target,state,replacement)) == D.rows_collection(watched,state) : Maybe<&2,List<&2,D.Row>>}
def replacing_a_collection_preserves_every_separate_collection_view(target,watched,state,replacement,separate):
  match target watched state:
    case D.Users{} D.Users{} D.State{tables,users}: F.absurd_boolean({Some{replacement} == Some{users} : Maybe<&2,List<&2,D.Row>>},separate)
    case D.Users{} D.Application{name} D.State{tables,users}: {==}
    case D.Application{name} D.Users{} D.State{tables,users}: {==}
    case D.Application{+target} D.Application{+watched} D.State{+tables,users}: swapping_one_named_table_preserves_every_distinct_named_collection_view(tables,target,watched,replacement,separate)

def different_inverse_case(reverse: Bool,+first: String,+later: String,different: {String.eq(first,later) == False{} : Bool},actual: {String.eq(later,first) == reverse : Bool}) -> {String.eq(later,first) == False{} : Bool}:
  match reverse:
    case False{}: actual
    case True{}: F.absurd_boolean({String.eq(later,first) == False{} : Bool},Equal.trans(Bool,False{},String.eq(first,later),True{},Equal.sym(Bool,String.eq(first,later),False{},different),O.string_eq_inverse(later,first,actual)))

law different_strings_have_symmetric_inequality:
  for +first: String
  for +later: String
  for different: {String.eq(first,later) == False{} : Bool}
  {String.eq(later,first) == False{} : Bool}
def different_strings_have_symmetric_inequality(first,later,different): different_inverse_case(String.eq(later,first),first,later,different,{==})

law separate_collection_domains_are_symmetric:
  for +target: D.Collection
  for +watched: D.Collection
  for separate: Separate(target,watched)
  Separate(watched,target)
def separate_collection_domains_are_symmetric(target,watched,separate):
  match target watched:
    case D.Users{} D.Users{}: separate
    case D.Users{} D.Application{name}: Unit{}
    case D.Application{name} D.Users{}: Unit{}
    case D.Application{+target} D.Application{+watched}: different_strings_have_symmetric_inequality(target,watched,separate)
