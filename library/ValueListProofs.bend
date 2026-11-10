# Proper list-tail shape is the EXACT domain of Value.list. Heads remain
# arbitrary Value DATA, including invalid nested text/records. Whole nested
# value validity is deliberately a different contract property.
import Base
import ./ValueScalarProofs.bend as Scalar
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ./Value.bend as V
import ./Sequence.bend as Sequence
import ../proof/Foundations.bend as F


def Shape(input: D.Value) -> Data:
  match input:
    case D.VListEmpty{}: Unit
    case D.VList{head,tail}: Shape(tail)
    case _: {False{} == True{} : Bool}

def Meaning(+input: D.Value,result: Maybe<&2,List<&2,D.Value>>) -> Type:
  match result:
    case Some{items}: Scalar.Both<{Sequence.values(items) == input : D.Value},Shape(input)>
    case None{}: Shape(input) -> Empty


def tail_case(+head: D.Value,+tail: D.Value,result: Maybe<&2,List<&2,D.Value>>,correct: Meaning(tail,result)) -> Meaning(D.VList{head,tail},V.list_cons(head,result)):
  match result:
    case None{}: correct
    case Some{+items}:
      match correct:
        case Scalar.Both{exact,shape}: Scalar.Both{Equal.cong(D.Value,D.Value,rest => D.VList{head,rest},Sequence.values(items),tail,exact),shape}

law actual_list_decoder_accepts_exactly_proper_list_tail_shapes:
  for +input: D.Value
  Meaning(input,V.list(input))
def actual_list_decoder_accepts_exactly_proper_list_tail_shapes(input):
  match input:
    case D.VListEmpty{}: Scalar.Both{{==},Unit{}}
    case D.VList{+head,+tail}: tail_case(head,tail,V.list(tail),actual_list_decoder_accepts_exactly_proper_list_tail_shapes(tail))
    case D.VAbsent{}: impossible => F.false_negative_true(impossible)
    case D.VBool{b}: impossible => F.false_negative_true(impossible)
    case D.VInt{h,l}: impossible => F.false_negative_true(impossible)
    case D.VText{s}: impossible => F.false_negative_true(impossible)
    case D.VRecordEmpty{}: impossible => F.false_negative_true(impossible)
    case D.VRecord{n,v,t}: impossible => F.false_negative_true(impossible)

law serializing_any_obtained_value_list_has_proper_list_shape:
  for +items: List<&2,D.Value>
  Shape(Sequence.values(items))
def serializing_any_obtained_value_list_has_proper_list_shape(items):
  match items:
    case Nil{}: Unit{}
    case Con{head,tail}: serializing_any_obtained_value_list_has_proper_list_shape(tail)

law converting_an_obtained_list_to_value_and_back_preserves_every_element:
  for +items: List<&2,D.Value>
  {V.list(Sequence.values(items)) == Some{items} : Maybe<&2,List<&2,D.Value>>}
def converting_an_obtained_list_to_value_and_back_preserves_every_element(items):
  match items:
    case Nil{}: {==}
    case Con{+head,+tail}: Equal.cong(Maybe<&2,List<&2,D.Value>>,Maybe<&2,List<&2,D.Value>>,decoded => V.list_cons(head,decoded),V.list(Sequence.values(tail)),Some{tail},converting_an_obtained_list_to_value_and_back_preserves_every_element(tail))


def Representation(+input: D.Value) -> Type:
  Exists(List<&2,D.Value>,items => L.E<{V.list(input) == Some{items} : Maybe<&2,List<&2,D.Value>>},{Sequence.values(items) == input : D.Value}>)

def representation_case(+input: D.Value,result: Maybe<&2,List<&2,D.Value>>,actual: {V.list(input) == result : Maybe<&2,List<&2,D.Value>>},correct: Meaning(input,result),shape: Shape(input)) -> Representation(input):
  match result:
    case None{}: L.ex_false(Representation(input),correct(shape))
    case Some{+items}:
      match correct:
        case Scalar.Both{exact,list_shape}: Tuple{items,L.Both{actual,exact}}

law every_proper_list_shape_is_accepted_with_exact_reverse_roundtrip:
  for +input: D.Value
  for shape: Shape(input)
  Representation(input)
def every_proper_list_shape_is_accepted_with_exact_reverse_roundtrip(input,shape):
  representation_case(input,V.list(input),{==},actual_list_decoder_accepts_exactly_proper_list_tail_shapes(input),shape)


def reencoded(result: Maybe<&2,List<&2,D.Value>>) -> D.Value:
  match result:
    case None{}: D.VListEmpty{}
    case Some{items}: Sequence.values(items)

def reverse_case(+input: D.Value,result: Maybe<&2,List<&2,D.Value>>,correct: Meaning(input,result),shape: Shape(input)) -> {reencoded(result) == input : D.Value}:
  match result:
    case None{}: L.ex_false({D.VListEmpty{} == input : D.Value},correct(shape))
    case Some{items}:
      match correct:
        case Scalar.Both{exact,list_shape}: exact

law accepted_shape_roundtrips_through_the_actual_list_decoder_and_serializer:
  for +input: D.Value
  for shape: Shape(input)
  {reencoded(V.list(input)) == input : D.Value}
def accepted_shape_roundtrips_through_the_actual_list_decoder_and_serializer(input,shape):
  reverse_case(input,V.list(input),actual_list_decoder_accepts_exactly_proper_list_tail_shapes(input),shape)
