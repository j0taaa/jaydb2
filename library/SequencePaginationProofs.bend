# Independent positional semantics: a slice is determined by its value at
# EVERY natural index and by its truncated arithmetic length. This does not
# define a second take/drop/page implementation as the specification.
import Base
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ./Sequence.bend as Sequence

def at(xs: List<&2,D.Value>,index: Nat) -> Maybe<&2,D.Value>:
  match xs:
    case Nil{}: None{}
    case Con{x,tail}:
      match index:
        case 0n: Some{x}
        case 1n+previous: at(tail,previous)

def append(xs: List<&2,D.Value>,ys: List<&2,D.Value>) -> List<&2,D.Value>:
  match xs:
    case Nil{}: ys
    case Con{x,tail}: Con{x,append(tail,ys)}

law subtraction_of_zero_preserves_a_natural:
  for +n: Nat
  {Nat.sub(n,0n) == n : Nat}
def subtraction_of_zero_preserves_a_natural(n):
  match n:
    case 0n: {==}
    case 1n+p: {==}

law choosing_between_missing_indices_is_missing:
  for choice: Bool
  {Bool.pick(Maybe<&2,D.Value>,choice,None{},None{}) == None{} : Maybe<&2,D.Value>}
def choosing_between_missing_indices_is_missing(choice):
  match choice:
    case True{}: {==}
    case False{}: {==}

law take_has_exact_indexed_prefix_contents:
  for +size: Nat
  for +xs: List<&2,D.Value>
  for +index: Nat
  {at(Sequence.take(size,xs),index) == Bool.pick(Maybe<&2,D.Value>,Nat.is_lt(index,size),at(xs,index),None{}) : Maybe<&2,D.Value>}
def take_has_exact_indexed_prefix_contents(size,xs,index):
  match size xs index:
    case 0n xs 0n: {==}
    case 0n xs 1n+i: {==}
    case 1n+n Nil{} index: Equal.sym(Maybe<&2,D.Value>,Bool.pick(Maybe<&2,D.Value>,Nat.is_lt(index,1n+n),None{},None{}),None{},choosing_between_missing_indices_is_missing(Nat.is_lt(index,1n+n)))
    case 1n+n Con{x,tail} 0n: {==}
    case 1n+n Con{x,+tail} 1n+i: take_has_exact_indexed_prefix_contents(n,tail,i)

law drop_has_exact_shifted_indexed_contents:
  for +offset: Nat
  for +xs: List<&2,D.Value>
  for +index: Nat
  {at(Sequence.drop(offset,xs),index) == at(xs,Nat.add(offset,index)) : Maybe<&2,D.Value>}
def drop_has_exact_shifted_indexed_contents(offset,xs,index):
  match offset xs:
    case 0n xs: {==}
    case 1n+previous Nil{}: {==}
    case 1n+previous Con{x,+tail}: drop_has_exact_shifted_indexed_contents(previous,tail,index)

law take_has_exact_truncated_length:
  for +size: Nat
  for +xs: List<&2,D.Value>
  {Sequence.length(Sequence.take(size,xs)) == Nat.min(size,Sequence.length(xs)) : Nat}
def take_has_exact_truncated_length(size,xs):
  match size xs:
    case 0n xs: {==}
    case 1n+n Nil{}: {==}
    case 1n+n Con{x,+tail}: Equal.cong(Nat,Nat,n => 1n+n,Sequence.length(Sequence.take(n,tail)),Nat.min(n,Sequence.length(tail)),take_has_exact_truncated_length(n,tail))

law drop_has_exact_saturating_length:
  for +offset: Nat
  for +xs: List<&2,D.Value>
  {Sequence.length(Sequence.drop(offset,xs)) == Nat.sub(Sequence.length(xs),offset) : Nat}
def drop_has_exact_saturating_length(offset,xs):
  match offset xs:
    case 0n +xs: Equal.sym(Nat,Nat.sub(Sequence.length(xs),0n),Sequence.length(xs),subtraction_of_zero_preserves_a_natural(Sequence.length(xs)))
    case 1n+previous Nil{}: {==}
    case 1n+previous Con{x,+tail}: drop_has_exact_saturating_length(previous,tail)

law take_and_drop_reconstruct_the_entire_input:
  for +offset: Nat
  for +xs: List<&2,D.Value>
  {append(Sequence.take(offset,xs),Sequence.drop(offset,xs)) == xs : List<&2,D.Value>}
def take_and_drop_reconstruct_the_entire_input(offset,xs):
  match offset xs:
    case 0n xs: {==}
    case 1n+previous Nil{}: {==}
    case 1n+previous Con{+x,+tail}: Equal.cong(List<&2,D.Value>,List<&2,D.Value>,rest => Con{x,rest},append(Sequence.take(previous,tail),Sequence.drop(previous,tail)),tail,take_and_drop_reconstruct_the_entire_input(previous,tail))

law page_has_exact_offset_and_capped_indexed_contents:
  for +offset: Nat
  for +size: Nat
  for +xs: List<&2,D.Value>
  for +index: Nat
  {at(Sequence.page(offset,size,xs),index) == Bool.pick(Maybe<&2,D.Value>,Nat.is_lt(index,size),at(xs,Nat.add(offset,index)),None{}) : Maybe<&2,D.Value>}
def page_has_exact_offset_and_capped_indexed_contents(offset,size,xs,index):
  Equal.trans(Maybe<&2,D.Value>,at(Sequence.page(offset,size,xs),index),Bool.pick(Maybe<&2,D.Value>,Nat.is_lt(index,size),at(Sequence.drop(offset,xs),index),None{}),Bool.pick(Maybe<&2,D.Value>,Nat.is_lt(index,size),at(xs,Nat.add(offset,index)),None{}),take_has_exact_indexed_prefix_contents(size,Sequence.drop(offset,xs),index),
    Equal.cong(Maybe<&2,D.Value>,Maybe<&2,D.Value>,value => Bool.pick(Maybe<&2,D.Value>,Nat.is_lt(index,size),value,None{}),at(Sequence.drop(offset,xs),index),at(xs,Nat.add(offset,index)),drop_has_exact_shifted_indexed_contents(offset,xs,index)))

law page_has_exact_truncated_slice_length:
  for +offset: Nat
  for +size: Nat
  for +xs: List<&2,D.Value>
  {Sequence.length(Sequence.page(offset,size,xs)) == Nat.min(size,Nat.sub(Sequence.length(xs),offset)) : Nat}
def page_has_exact_truncated_slice_length(offset,size,xs):
  Equal.trans(Nat,Sequence.length(Sequence.page(offset,size,xs)),Nat.min(size,Sequence.length(Sequence.drop(offset,xs))),Nat.min(size,Nat.sub(Sequence.length(xs),offset)),take_has_exact_truncated_length(size,Sequence.drop(offset,xs)),Equal.cong(Nat,Nat,length => Nat.min(size,length),Sequence.length(Sequence.drop(offset,xs)),Nat.sub(Sequence.length(xs),offset),drop_has_exact_saturating_length(offset,xs)))

# All-index equality together with the exact length specifies the whole slice,
# including order, duplicates, boundaries, and offsets beyond the input.
def Slice(+xs: List<&2,D.Value>,+offset: Nat,+size: Nat,+result: List<&2,D.Value>) -> Type:
  L.E<{Sequence.length(result) == Nat.min(size,Nat.sub(Sequence.length(xs),offset)) : Nat},
    @index: Nat -> {at(result,index) == Bool.pick(Maybe<&2,D.Value>,Nat.is_lt(index,size),at(xs,Nat.add(offset,index)),None{}) : Maybe<&2,D.Value>}>

law actual_page_is_the_exact_indexed_slice:
  for +offset: Nat
  for +size: Nat
  for +xs: List<&2,D.Value>
  Slice(xs,offset,size,Sequence.page(offset,size,xs))
def actual_page_is_the_exact_indexed_slice(offset,size,xs):
  L.Both{page_has_exact_truncated_slice_length(offset,size,xs),index => page_has_exact_offset_and_capped_indexed_contents(offset,size,xs,index)}
