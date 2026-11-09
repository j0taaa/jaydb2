# A positive divisor and a representable dividend exclude every nonzero
# quotient carry coefficient. This proves actual quotient bits were not lost.
import Base
import ./Int64QuotientResidue.bend as Q
import ./Int64UnsignedStep.bend as Overflow
import ./Int64Flags.bend as G
import ./Int64Proofs.bend as A
import ./Int64.bend as I
import ./Value.bend as V
import ../contract/Logic.bend as L

law positive_residue_exceeds_radix:
  for +width: Nat
  for +word_value: Nat
  for +natural: Nat
  for +p: Nat
  for exact: {natural == Nat.add(word_value,Nat.mul(1n+p,A.modulus(width))) : Nat}
  Overflow.Beyond<width,natural>
def positive_residue_exceeds_radix(width,word_value,natural,p,exact):
  +rest = Nat.mul(p,A.modulus(width))
  Overflow.Beyond{Nat.add(word_value,rest),
    Equal.trans(Nat,natural,Nat.add(word_value,Nat.add(A.modulus(width),rest)),Nat.add(Nat.add(word_value,rest),A.modulus(width)),exact,
      Equal.trans(Nat,Nat.add(word_value,Nat.add(A.modulus(width),rest)),Nat.add(Nat.add(word_value,A.modulus(width)),rest),Nat.add(Nat.add(word_value,rest),A.modulus(width)),
        Equal.sym(Nat,Nat.add(Nat.add(word_value,A.modulus(width)),rest),Nat.add(word_value,Nat.add(A.modulus(width),rest)),A.add_associative(word_value,A.modulus(width),rest)),
        Overflow.move_radix_middle(width,word_value,rest)))}

def positive_divisor_preserves_excess(+d: V.Int64,+natural: Nat,
  positive: G.Positive<d>,beyond: Overflow.Beyond<64n,natural>) -> Overflow.Beyond<64n,Nat.mul(A.unsigned(d),natural)>:
  match positive:
    case G.Positive{+p,measure}:
      Overflow.beyond_rewrite(64n,Nat.mul(A.unsigned(d),natural),Nat.mul(1n+p,natural),Equal.cong(Nat,Nat,v => Nat.mul(v,natural),A.unsigned(d),1n+p,measure),Overflow.positive_product_is_beyond(64n,p,natural,beyond))

law eliminate_quotient_wraps:
  for +a: V.Int64
  for +d: V.Int64
  for +q: V.Int64
  for +r: V.Int64
  for +natural: Nat
  for positive: G.Positive<d>
  for residue: Q.Residue<64n,A.unsigned(q),natural>
  for exact: {A.unsigned(a) == Nat.add(Nat.mul(A.unsigned(d),natural),A.unsigned(r)) : Nat}
  {A.unsigned(a) == Nat.add(Nat.mul(A.unsigned(d),A.unsigned(q)),A.unsigned(r)) : Nat}
def eliminate_quotient_wraps(a,d,q,r,natural,positive,residue,exact):
  match residue:
    case Q.Residue{0n,source}:
      Equal.trans(Nat,A.unsigned(a),Nat.add(Nat.mul(A.unsigned(d),natural),A.unsigned(r)),Nat.add(Nat.mul(A.unsigned(d),A.unsigned(q)),A.unsigned(r)),exact,
        Equal.cong(Nat,Nat,v => Nat.add(Nat.mul(A.unsigned(d),v),A.unsigned(r)),natural,A.unsigned(q),Equal.trans(Nat,natural,Nat.add(A.unsigned(q),0n),A.unsigned(q),source,A.add_zero_right(A.unsigned(q)))))
    case Q.Residue{1n+p,source}:
      L.ex_false({A.unsigned(a) == Nat.add(Nat.mul(A.unsigned(d),A.unsigned(q)),A.unsigned(r)) : Nat},
        Overflow.excess_excludes_every_word(A.unsigned(a),a,
          Overflow.beyond_rewrite(64n,A.unsigned(a),Nat.add(Nat.mul(A.unsigned(d),natural),A.unsigned(r)),exact,
            Overflow.beyond_append(64n,Nat.mul(A.unsigned(d),natural),A.unsigned(r),positive_divisor_preserves_excess(d,natural,positive,positive_residue_exceeds_radix(64n,A.unsigned(q),natural,p,source)))),{==}))
