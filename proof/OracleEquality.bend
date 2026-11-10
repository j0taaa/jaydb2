# Runtime matching uses the existing structural comparator, never source rendering.
import Base
import ../contract/Data.bend as D
import ../library/Value.bend as V
import ../library/StructuralEqualityProofs.bend as Comparison
import ./Orders.bend as O
import ./Foundations.bend as F

def arguments_equal(a: D.Value, b: D.Value) -> Bool:
  V.equal(a, b)

def arguments_sound(a: D.Value, b: D.Value, h: {arguments_equal(a, b) == True{} : Bool}) -> {a == b : D.Value}:
  Comparison.equal_sound(a, b, h)

def context_sound(a: D.Context, b: D.Context, h: {D.context_equal(a, b) == True{} : Bool}) -> {a == b : D.Context}:
  match a b:
    case D.Context{+ai, +ak} D.Context{+bi, +bk}:
      +h = h
      %O.string_equal(ai, bi, F.and_boolean_left(String.eq(ai, bi), String.eq(ak, bk), h)) :
        {D.Context{ai, ak} == D.Context{_, bk} : D.Context}
      Equal.cong(String, D.Context, k => D.Context{ai, k}, ak, bk,
        O.string_equal(ak, bk, F.and_boolean_right(String.eq(ai, bi), String.eq(ak, bk), h)))
