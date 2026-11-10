# Independent mathematical extremum specification: a returned input occurrence
# and a non-strict bound against EVERY list element, in ordinary integer order.
import Base
import ./Int64OrderProofs.bend as Order
import ./Value.bend as V
import ./Int64.bend as I
import ./Aggregate.bend as Aggregate
import ../contract/Logic.bend as L

type Both<-P: Data,-Q: Data> is Data:
  Both{left: P,right: Q}

def Member(+value: V.Int64,xs: List<&2,V.Int64>) -> Type:
  match xs:
    case Nil{}: Empty
    case Con{head,tail}: L.Disjunction<{value == head : V.Int64},Member(value,tail)>

def Edge(lower: Bool,a: V.Int64,b: V.Int64) -> Data:
  match lower:
    case True{}: Order.LessEqual(a,b)
    case False{}: Order.LessEqual(b,a)

def Bounds(+lower: Bool,+value: V.Int64,xs: List<&2,V.Int64>) -> Data:
  match xs:
    case Nil{}: Unit
    case Con{head,tail}: Both<Edge(lower,value,head),Bounds(lower,value,tail)>

type Extremum<-lower: Bool,-xs: List<&2,V.Int64>,-result: V.Int64> is Type:
  Extremum{member: Member(result,xs),bounds: Bounds(lower,result,xs)}

def edge_reflexive(lower: Bool,+a: V.Int64) -> Edge(lower,a,a):
  match lower:
    case True{}: Order.mathematical_nonstrict_order_is_reflexive(a)
    case False{}: Order.mathematical_nonstrict_order_is_reflexive(a)

def edge_transitive(lower: Bool,+a: V.Int64,+b: V.Int64,+c: V.Int64,ab: Edge(lower,a,b),bc: Edge(lower,b,c)) -> Edge(lower,a,c):
  match lower:
    case True{}: Order.mathematical_nonstrict_order_is_transitive(a,b,c,ab,bc)
    case False{}: Order.mathematical_nonstrict_order_is_transitive(c,b,a,bc,ab)

def fold(lower: Bool,+xs: List<&2,V.Int64>,+best: V.Int64) -> V.Int64:
  Bool.pick(V.Int64,lower,Aggregate.minimum(xs,best),Aggregate.maximum(xs,best))

def compare_for(+lower: Bool,+x: V.Int64,+best: V.Int64) -> Bool:
  I.lt(Bool.pick(V.Int64,lower,x,best),Bool.pick(V.Int64,lower,best,x))

def fold_step(lower: Bool,+x: V.Int64,+xs: List<&2,V.Int64>,+best: V.Int64) ->
  {fold(lower,Con{x,xs},best) == fold(lower,xs,Bool.pick(V.Int64,compare_for(lower,x,best),x,best)) : V.Int64}:
  match lower:
    case True{}: {==}
    case False{}: {==}

def selection_bounds(lower: Bool,selected: Bool,+x: V.Int64,+best: V.Int64,actual: {compare_for(lower,x,best) == selected : Bool}) ->
  Both<Edge(lower,Bool.pick(V.Int64,selected,x,best),best),Edge(lower,Bool.pick(V.Int64,selected,x,best),x)>:
  match lower selected:
    case True{} True{}: Both{Order.actual_strict_comparison_entails_mathematical_nonstrict_order(x,best,actual),Order.mathematical_nonstrict_order_is_reflexive(x)}
    case True{} False{}: Both{Order.mathematical_nonstrict_order_is_reflexive(best),Order.actual_reverse_not_less_entails_mathematical_nonstrict_order(best,x,actual)}
    case False{} True{}: Both{Order.actual_strict_comparison_entails_mathematical_nonstrict_order(best,x,actual),Order.mathematical_nonstrict_order_is_reflexive(x)}
    case False{} False{}: Both{Order.mathematical_nonstrict_order_is_reflexive(best),Order.actual_reverse_not_less_entails_mathematical_nonstrict_order(x,best,actual)}

def selection_membership(selected: Bool,+best: V.Int64,+x: V.Int64,+tail: List<&2,V.Int64>,+r: V.Int64,member: Member(r,Con{Bool.pick(V.Int64,selected,x,best),tail})) -> Member(r,Con{best,Con{x,tail}}):
  match selected member:
    case True{} L.Left{same}: L.Right{L.Left{same}}
    case True{} L.Right{tail_member}: L.Right{L.Right{tail_member}}
    case False{} L.Left{same}: L.Left{same}
    case False{} L.Right{tail_member}: L.Right{L.Right{tail_member}}

def extend_selected_extremum(+lower: Bool,+selected: Bool,+x: V.Int64,+best: V.Int64,+tail: List<&2,V.Int64>,+r: V.Int64,
  selection: Both<Edge(lower,Bool.pick(V.Int64,selected,x,best),best),Edge(lower,Bool.pick(V.Int64,selected,x,best),x)>,
  correct: Extremum<lower,Con{Bool.pick(V.Int64,selected,x,best),tail},r>) -> Extremum<lower,Con{best,Con{x,tail}},r>:
  match selection correct:
    case Both{chosen_best,chosen_x} Extremum{member,Both{+result_chosen,tail_bounds}}:
      Extremum{selection_membership(selected,best,x,tail,r,member),
        Both{edge_transitive(lower,r,Bool.pick(V.Int64,selected,x,best),best,result_chosen,chosen_best),Both{edge_transitive(lower,r,Bool.pick(V.Int64,selected,x,best),x,result_chosen,chosen_x),tail_bounds}}}

def empty_fold_extremum(lower: Bool,+best: V.Int64) -> Extremum<lower,Con{best,Nil{}},fold(lower,Nil{},best)>:
  match lower:
    case True{}: Extremum{L.Left{{==}},Both{Order.mathematical_nonstrict_order_is_reflexive(best),Unit{}}}
    case False{}: Extremum{L.Left{{==}},Both{Order.mathematical_nonstrict_order_is_reflexive(best),Unit{}}}

law actual_seeded_fold_returns_a_mathematical_extremum:
  for +lower: Bool
  for +xs: List<&2,V.Int64>
  for +best: V.Int64
  Extremum<lower,Con{best,xs},fold(lower,xs,best)>
def actual_seeded_fold_returns_a_mathematical_extremum(lower,xs,best):
  match xs:
    case Nil{}: empty_fold_extremum(lower,best)
    case Con{+x,+tail}:
      %Equal.sym(V.Int64,fold(lower,Con{x,tail},best),fold(lower,tail,Bool.pick(V.Int64,compare_for(lower,x,best),x,best)),fold_step(lower,x,tail,best)) : Extremum<lower,Con{best,Con{x,tail}},_>
      extend_selected_extremum(lower,compare_for(lower,x,best),x,best,tail,fold(lower,tail,Bool.pick(V.Int64,compare_for(lower,x,best),x,best)),selection_bounds(lower,compare_for(lower,x,best),x,best,{==}),actual_seeded_fold_returns_a_mathematical_extremum(lower,tail,Bool.pick(V.Int64,compare_for(lower,x,best),x,best)))

law actual_minimum_is_a_mathematical_input_extremum:
  for +xs: List<&2,V.Int64>
  for +best: V.Int64
  Extremum<True{},Con{best,xs},Aggregate.minimum(xs,best)>
def actual_minimum_is_a_mathematical_input_extremum(xs,best):
  actual_seeded_fold_returns_a_mathematical_extremum(True{},xs,best)

law actual_maximum_is_a_mathematical_input_extremum:
  for +xs: List<&2,V.Int64>
  for +best: V.Int64
  Extremum<False{},Con{best,xs},Aggregate.maximum(xs,best)>
def actual_maximum_is_a_mathematical_input_extremum(xs,best):
  actual_seeded_fold_returns_a_mathematical_extremum(False{},xs,best)

def ResultCorrect(+lower: Bool,+xs: List<&2,V.Int64>,result: Maybe<&2,V.Int64>) -> Type:
  match result:
    case None{}: {xs == Nil{} : List<&2,V.Int64>}
    case Some{r}: Extremum<lower,xs,r>

law minimum_value_is_exactly_a_nonempty_list_extremum:
  for +xs: List<&2,V.Int64>
  ResultCorrect(True{},xs,Aggregate.min_value(xs))
def minimum_value_is_exactly_a_nonempty_list_extremum(xs):
  match xs:
    case Nil{}: {==}
    case Con{+x,+tail}: actual_minimum_is_a_mathematical_input_extremum(tail,x)

law maximum_value_is_exactly_a_nonempty_list_extremum:
  for +xs: List<&2,V.Int64>
  ResultCorrect(False{},xs,Aggregate.max_value(xs))
def maximum_value_is_exactly_a_nonempty_list_extremum(xs):
  match xs:
    case Nil{}: {==}
    case Con{+x,+tail}: actual_maximum_is_a_mathematical_input_extremum(tail,x)
