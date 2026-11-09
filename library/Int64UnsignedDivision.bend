# Complete actual unsigned restoring division for every nonzero divisor whose
# magnitude is at most 2^63. The dividend may be any unsigned 64-bit word.
import Base
import ./Int64DivisionTrace.bend as Trace
import ./Int64QuotientResidue.bend as Q
import ./Int64NoQuotientLoss.bend as NoLoss
import ./Int64DivisionSource.bend as Source
import ./Int64NaturalOrder.bend as O
import ./Int64Flags.bend as G
import ./Int64Proofs.bend as A
import ./Int64NatProduct.bend as N
import ./Int64.bend as I
import ./Value.bend as V
import ../contract/Logic.bend as L

def Euclidean(+a: V.Int64,+d: V.Int64,+result: I.Division) -> Type:
  L.E<{A.unsigned(a) == Nat.add(Nat.mul(A.unsigned(d),A.unsigned(Trace.quotient(result))),A.unsigned(Trace.remainder(result))) : Nat},
    L.E<{Nat.is_lt(A.unsigned(Trace.remainder(result)),A.unsigned(d)) == True{} : Bool},
      {I.unsigned_lt(Trace.remainder(result),d) == True{} : Bool}>>

law zero_quotient_residue:
  for +width: Nat
  Q.Residue<width,0n,0n>
def zero_quotient_residue(width):
  Q.Residue{0n,{==}}

law zero_initial_total:
  for +d: V.Int64
  {Trace.total(d,0n,V.Int64{0,0}) == 0n : Nat}
def zero_initial_total(d):
  Equal.cong(Nat,Nat,v => Nat.add(v,0n),Nat.mul(A.unsigned(d),0n),0n,N.mul_zero_right(A.unsigned(d)))

law actual_source_from_zero_prefix:
  for +a: V.Int64
  for +d: V.Int64
  {Source.actual_feed(64n,a,Trace.total(d,0n,V.Int64{0,0})) == A.unsigned(a) : Nat}
def actual_source_from_zero_prefix(a,d):
  Equal.trans(Nat,Source.actual_feed(64n,a,Trace.total(d,0n,V.Int64{0,0})),Source.actual_feed(64n,a,0n),A.unsigned(a),
    Equal.cong(Nat,Nat,prefix => Source.actual_feed(64n,a,prefix),Trace.total(d,0n,V.Int64{0,0}),0n,zero_initial_total(d)),Source.sixty_four_actual_input_bits_recover_value(a))

law zero_remainder_below_positive_divisor:
  for +d: V.Int64
  for +p: Nat
  for measure: {A.unsigned(d) == 1n+p : Nat}
  {I.unsigned_lt(V.Int64{0,0},d) == True{} : Bool}
def zero_remainder_below_positive_divisor(d,p,measure):
  Equal.trans(Bool,I.unsigned_lt(V.Int64{0,0},d),Nat.is_lt(0n,A.unsigned(d)),True{},O.actual_unsigned_lt_is_natural_order(V.Int64{0,0},d),
    Equal.cong(Nat,Bool,v => Nat.is_lt(0n,v),A.unsigned(d),1n+p,measure))

def finish_actual_loop(+a: V.Int64,+d: V.Int64,+result: I.Division,
  positive: G.Positive<d>,
  trace: Trace.Trace<64n,a,d,0n,V.Int64{0,0},result>) -> Euclidean(a,d,result):
  match trace:
    case Trace.Trace{+natural_q,residue,arithmetic,+small}:
      L.Both{NoLoss.eliminate_quotient_wraps(a,d,Trace.quotient(result),Trace.remainder(result),natural_q,positive,residue,
        Equal.trans(Nat,A.unsigned(a),Source.actual_feed(64n,a,Trace.total(d,0n,V.Int64{0,0})),Trace.total(d,natural_q,Trace.remainder(result)),
          Equal.sym(Nat,Source.actual_feed(64n,a,Trace.total(d,0n,V.Int64{0,0})),A.unsigned(a),actual_source_from_zero_prefix(a,d)),arithmetic)),
        L.Both{Equal.trans(Bool,Nat.is_lt(A.unsigned(Trace.remainder(result)),A.unsigned(d)),I.unsigned_lt(Trace.remainder(result),d),True{},
          Equal.sym(Bool,I.unsigned_lt(Trace.remainder(result),d),Nat.is_lt(A.unsigned(Trace.remainder(result)),A.unsigned(d)),O.actual_unsigned_lt_is_natural_order(Trace.remainder(result),d)),small),small}}

def division_from_positive_divisor(+a: V.Int64,+d: V.Int64,positive: G.Positive<d>,
  bound: {Cmp.is_le(Word.cmp(64n,A.bits(d),A.sign_threshold(63n))) == True{} : Bool}) -> Euclidean(a,d,I.divide_step(64n,a,d,V.Int64{0,0},V.Int64{0,0})):
  match positive:
    case G.Positive{+p,+measure}:
      finish_actual_loop(a,d,I.divide_step(64n,a,d,V.Int64{0,0},V.Int64{0,0}),G.Positive{p,measure},
        Trace.actual_restoring_loop_trace(64n,a,d,V.Int64{0,0},V.Int64{0,0},0n,zero_quotient_residue(64n),zero_remainder_below_positive_divisor(d,p,measure),bound))

# No loop equation, result, arithmetic invariant or carry correctness is a
# premise. The divisor hypotheses express the actual supported input domain.
law actual_unsigned_division:
  for +a: V.Int64
  for +d: V.Int64
  for nonzero: {I.zero(d) == False{} : Bool}
  for bound: {Cmp.is_le(Word.cmp(64n,A.bits(d),A.sign_threshold(63n))) == True{} : Bool}
  Euclidean(a,d,I.divide_step(64n,a,d,V.Int64{0,0},V.Int64{0,0}))
def actual_unsigned_division(a,d,nonzero,bound):
  division_from_positive_divisor(a,d,G.nonzero_has_positive_measure(d,nonzero),bound)
