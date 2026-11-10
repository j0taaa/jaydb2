# Stability means preserving the ENTIRE ordered sequence of every tied class,
# including payloads and duplicate occurrences. The only comparison-domain
# premise is that two members of that input class never compare strictly less.
# The earlier independent indexed filter theorem gives this projection its
# exact source-position, rank, completeness, and order meaning.
import Base
import ./SequenceFilterProofs.bend as Selection
import ../contract/Data.bend as D
import ./Sequence.bend as Sequence
import ./SortProof.bend as Sort
import ../proof/Foundations.bend as F

# If both occurrences belong to the same tied class, insertion cannot skip an
# earlier equal-class occurrence. In the other cases one is absent from the
# class projection and commuting the two include operations preserves it.
def commuting_class_projection(~less: D.Value -> D.Value -> Bool,~selected: D.Value -> Bool,
  ~tied: @+a: D.Value -> @+b: D.Value -> {selected(a) == True{} : Bool} -> {selected(b) == True{} : Bool} -> {less(a,b) == False{} : Bool},
  sx: Bool,sh: Bool,+x: D.Value,+h: D.Value,+tail: List<&2,D.Value>,x_selected: {selected(x) == sx : Bool},h_selected: {selected(h) == sh : Bool},late: {Bool.not(less(h,x)) == False{} : Bool}) ->
  {Sequence.include(sh,h,Sequence.include(sx,x,tail)) == Sequence.include(sx,x,Sequence.include(sh,h,tail)) : List<&2,D.Value>}:
  match sx sh:
    case False{} False{}: {==}
    case False{} True{}: {==}
    case True{} False{}: {==}
    case True{} True{}:
      F.absurd_boolean({Con{h,Con{x,tail}} == Con{x,Con{h,tail}} : List<&2,D.Value>},
        Equal.trans(Bool,False{},Bool.not(less(h,x)),True{},Equal.sym(Bool,Bool.not(less(h,x)),False{},late),Equal.cong(Bool,Bool,Bool.not,less(h,x),False{},tied(h,x,h_selected,x_selected))))

def insertion_class_choice(~less: D.Value -> D.Value -> Bool,~selected: D.Value -> Bool,
  ~tied: @+a: D.Value -> @+b: D.Value -> {selected(a) == True{} : Bool} -> {selected(b) == True{} : Bool} -> {less(a,b) == False{} : Bool},
  before: Bool,+x: D.Value,+h: D.Value,+tail: List<&2,D.Value>,actual: {Bool.not(less(h,x)) == before : Bool},
  recursive: {Sequence.filter(~selected,Sequence.insert(~less,x,tail)) == Sequence.include(selected(x),x,Sequence.filter(~selected,tail)) : List<&2,D.Value>}) ->
  {Sequence.filter(~selected,Bool.pick(List<&2,D.Value>,before,Con{x,Con{h,tail}},Con{h,Sequence.insert(~less,x,tail)})) == Sequence.include(selected(x),x,Sequence.filter(~selected,Con{h,tail})) : List<&2,D.Value>}:
  match before:
    case True{}: {==}
    case False{}:
      Equal.trans(List<&2,D.Value>,Sequence.include(selected(h),h,Sequence.filter(~selected,Sequence.insert(~less,x,tail))),Sequence.include(selected(h),h,Sequence.include(selected(x),x,Sequence.filter(~selected,tail))),Sequence.include(selected(x),x,Sequence.filter(~selected,Con{h,tail})),
        Equal.cong(List<&2,D.Value>,List<&2,D.Value>,rest => Sequence.include(selected(h),h,rest),Sequence.filter(~selected,Sequence.insert(~less,x,tail)),Sequence.include(selected(x),x,Sequence.filter(~selected,tail)),recursive),
        commuting_class_projection(~less,~selected,~tied,selected(x),selected(h),x,h,Sequence.filter(~selected,tail),{==},{==},actual))

law actual_insertion_preserves_the_ordered_tied_class_projection:
  for ~less: D.Value -> D.Value -> Bool
  for ~selected: D.Value -> Bool
  for ~tied: @+a: D.Value -> @+b: D.Value -> {selected(a) == True{} : Bool} -> {selected(b) == True{} : Bool} -> {less(a,b) == False{} : Bool}
  for +x: D.Value
  for +xs: List<&2,D.Value>
  {Sequence.filter(~selected,Sequence.insert(~less,x,xs)) == Sequence.include(selected(x),x,Sequence.filter(~selected,xs)) : List<&2,D.Value>}
def actual_insertion_preserves_the_ordered_tied_class_projection(less,selected,tied,x,xs):
  match xs:
    case Nil{}: {==}
    case Con{+h,+tail}:
      insertion_class_choice(~less,~selected,~tied,Bool.not(less(h,x)),x,h,tail,{==},actual_insertion_preserves_the_ordered_tied_class_projection(~less,~selected,~tied,x,tail))

law actual_sort_preserves_the_entire_ordered_tied_class:
  for ~less: D.Value -> D.Value -> Bool
  for ~selected: D.Value -> Bool
  for ~tied: @+a: D.Value -> @+b: D.Value -> {selected(a) == True{} : Bool} -> {selected(b) == True{} : Bool} -> {less(a,b) == False{} : Bool}
  for +xs: List<&2,D.Value>
  {Sequence.filter(~selected,Sequence.sort(~less,xs)) == Sequence.filter(~selected,xs) : List<&2,D.Value>}
def actual_sort_preserves_the_entire_ordered_tied_class(less,selected,tied,xs):
  match xs:
    case Nil{}: {==}
    case Con{+x,+tail}:
      Equal.trans(List<&2,D.Value>,Sequence.filter(~selected,Sequence.sort(~less,Con{x,tail})),Sequence.include(selected(x),x,Sequence.filter(~selected,Sequence.sort(~less,tail))),Sequence.filter(~selected,Con{x,tail}),
        actual_insertion_preserves_the_ordered_tied_class_projection(~less,~selected,~tied,x,Sequence.sort(~less,tail)),
        Equal.cong(List<&2,D.Value>,List<&2,D.Value>,rest => Sequence.include(selected(x),x,rest),Sequence.filter(~selected,Sequence.sort(~less,tail)),Sequence.filter(~selected,tail),actual_sort_preserves_the_entire_ordered_tied_class(~less,~selected,~tied,tail)))

# Fully discharged concrete library comparator: completed/non-completed task
# payloads retain their original order inside each Boolean key class.
def incomplete(v: D.Value) -> Bool:
  Bool.not(Sort.completed(v))

def completed_are_tied(+a: D.Value,+b: D.Value,first: {Sort.completed(a) == True{} : Bool},second: {Sort.completed(b) == True{} : Bool}) -> {Sort.completed_less(a,b) == False{} : Bool}:
  Equal.cong(Bool,Bool,completed => Bool.not(completed) && Sort.completed(b),Sort.completed(a),True{},first)

def and_false(b: Bool) -> {b && False{} == False{} : Bool}:
  match b:
    case True{}: {==}
    case False{}: {==}

def incomplete_are_tied(+a: D.Value,+b: D.Value,first: {incomplete(a) == True{} : Bool},second: {incomplete(b) == True{} : Bool}) -> {Sort.completed_less(a,b) == False{} : Bool}:
  Equal.trans(Bool,Sort.completed_less(a,b),Bool.not(Sort.completed(a)) && False{},False{},Equal.cong(Bool,Bool,completed => Bool.not(Sort.completed(a)) && completed,Sort.completed(b),False{},F.negation_true(Sort.completed(b),second)),and_false(Bool.not(Sort.completed(a))))

law completed_sort_retains_completed_payload_order:
  for +xs: List<&2,D.Value>
  {Sequence.filter(~Sort.completed,Sequence.sort(~Sort.completed_less,xs)) == Sequence.filter(~Sort.completed,xs) : List<&2,D.Value>}
def completed_sort_retains_completed_payload_order(xs):
  actual_sort_preserves_the_entire_ordered_tied_class(~Sort.completed_less,~Sort.completed,~completed_are_tied,xs)

law completed_sort_retains_incomplete_payload_order:
  for +xs: List<&2,D.Value>
  {Sequence.filter(~incomplete,Sequence.sort(~Sort.completed_less,xs)) == Sequence.filter(~incomplete,xs) : List<&2,D.Value>}
def completed_sort_retains_incomplete_payload_order(xs):
  actual_sort_preserves_the_entire_ordered_tied_class(~Sort.completed_less,~incomplete,~incomplete_are_tied,xs)

# Connect the equality above to the independent all-occurrence rank model;
# the specification is not merely equality of two implementation projections.
law sorted_tied_class_has_exact_original_source_occurrences_and_ranks:
  for ~less: D.Value -> D.Value -> Bool
  for ~selected: D.Value -> Bool
  for ~tied: @+a: D.Value -> @+b: D.Value -> {selected(a) == True{} : Bool} -> {selected(b) == True{} : Bool} -> {less(a,b) == False{} : Bool}
  for +xs: List<&2,D.Value>
  Selection.Meaning(~selected,xs,Sequence.filter(~selected,Sequence.sort(~less,xs)))
def sorted_tied_class_has_exact_original_source_occurrences_and_ranks(less,selected,tied,xs):
  %Equal.sym(List<&2,D.Value>,Sequence.filter(~selected,Sequence.sort(~less,xs)),Sequence.filter(~selected,xs),actual_sort_preserves_the_entire_ordered_tied_class(~less,~selected,~tied,xs)) : Selection.Meaning(~selected,xs,_)
  Selection.actual_filter_is_exact_complete_and_ordered_selection(~selected,xs)
