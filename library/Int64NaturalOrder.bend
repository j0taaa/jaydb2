# Actual unsigned comparison agrees with independent unbounded natural order.
import Base
import ./Int64Flags.bend as G
import ./Int64Proofs.bend as A
import ./Int64.bend as I
import ./Value.bend as V

law even_even_compare:
  for +a: Nat
  for +b: Nat
  {Nat.cmp(Nat.double(a),Nat.double(b)) == Nat.cmp(a,b) : Cmp}
def even_even_compare(a,b):
  match a b:
    case 0n 0n: {==}
    case 0n 1n+p: {==}
    case 1n+p 0n: {==}
    case 1n+p 1n+q: even_even_compare(p,q)

law even_odd_compare:
  for +a: Nat
  for +b: Nat
  {Nat.cmp(Nat.double(a),1n+Nat.double(b)) == Word.cmp.fin(False{},True{},Nat.cmp(a,b)) : Cmp}
def even_odd_compare(a,b):
  match a b:
    case 0n 0n: {==}
    case 0n 1n+p: {==}
    case 1n+p 0n: {==}
    case 1n+p 1n+q: even_odd_compare(p,q)

law odd_even_compare:
  for +a: Nat
  for +b: Nat
  {Nat.cmp(1n+Nat.double(a),Nat.double(b)) == Word.cmp.fin(True{},False{},Nat.cmp(a,b)) : Cmp}
def odd_even_compare(a,b):
  match a b:
    case 0n 0n: {==}
    case 0n 1n+p: {==}
    case 1n+p 0n: {==}
    case 1n+p 1n+q: odd_even_compare(p,q)

law equal_bit_comparison:
  for +bit: Bool
  for +c: Cmp
  {Word.cmp.fin(bit,bit,c) == c : Cmp}
def equal_bit_comparison(bit,c):
  match bit c:
    case False{} LT{}: {==}
    case False{} EQ{}: {==}
    case False{} GT{}: {==}
    case True{} LT{}: {==}
    case True{} EQ{}: {==}
    case True{} GT{}: {==}

law binary_compare:
  for +ab: Bool
  for +bb: Bool
  for +a: Nat
  for +b: Nat
  {Nat.cmp(A.place(ab,a),A.place(bb,b)) == Word.cmp.fin(ab,bb,Nat.cmp(a,b)) : Cmp}
def binary_compare(ab,bb,a,b):
  match ab bb:
    case False{} False{}:
      Equal.trans(Cmp,Nat.cmp(Nat.double(a),Nat.double(b)),Nat.cmp(a,b),Word.cmp.fin(False{},False{},Nat.cmp(a,b)),even_even_compare(a,b),Equal.sym(Cmp,Word.cmp.fin(False{},False{},Nat.cmp(a,b)),Nat.cmp(a,b),equal_bit_comparison(False{},Nat.cmp(a,b))))
    case False{} True{}: even_odd_compare(a,b)
    case True{} False{}: odd_even_compare(a,b)
    case True{} True{}:
      Equal.trans(Cmp,Nat.cmp(Nat.double(a),Nat.double(b)),Nat.cmp(a,b),Word.cmp.fin(True{},True{},Nat.cmp(a,b)),even_even_compare(a,b),Equal.sym(Cmp,Word.cmp.fin(True{},True{},Nat.cmp(a,b)),Nat.cmp(a,b),equal_bit_comparison(True{},Nat.cmp(a,b))))

law word_comparison_is_natural_order:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Nat.cmp(Word.to_nat(n,a),Word.to_nat(n,b)) == Word.cmp(n,a,b) : Cmp}
def word_comparison_is_natural_order(n,a,b):
  match n:
    case 0n: {==}
    case 1n+p:
      match a b:
        case WCon{False{},+at} WCon{False{},+bt}:
          Equal.trans(Cmp,Nat.cmp(A.place(False{},Word.to_nat(p,at)),A.place(False{},Word.to_nat(p,bt))),Word.cmp.fin(False{},False{},Nat.cmp(Word.to_nat(p,at),Word.to_nat(p,bt))),Word.cmp.fin(False{},False{},Word.cmp(p,at,bt)),
            binary_compare(False{},False{},Word.to_nat(p,at),Word.to_nat(p,bt)),
            Equal.cong(Cmp,Cmp,c => Word.cmp.fin(False{},False{},c),Nat.cmp(Word.to_nat(p,at),Word.to_nat(p,bt)),Word.cmp(p,at,bt),word_comparison_is_natural_order(p,at,bt)))
        case WCon{False{},+at} WCon{True{},+bt}:
          Equal.trans(Cmp,Nat.cmp(A.place(False{},Word.to_nat(p,at)),A.place(True{},Word.to_nat(p,bt))),Word.cmp.fin(False{},True{},Nat.cmp(Word.to_nat(p,at),Word.to_nat(p,bt))),Word.cmp.fin(False{},True{},Word.cmp(p,at,bt)),
            binary_compare(False{},True{},Word.to_nat(p,at),Word.to_nat(p,bt)),
            Equal.cong(Cmp,Cmp,c => Word.cmp.fin(False{},True{},c),Nat.cmp(Word.to_nat(p,at),Word.to_nat(p,bt)),Word.cmp(p,at,bt),word_comparison_is_natural_order(p,at,bt)))
        case WCon{True{},+at} WCon{False{},+bt}:
          Equal.trans(Cmp,Nat.cmp(A.place(True{},Word.to_nat(p,at)),A.place(False{},Word.to_nat(p,bt))),Word.cmp.fin(True{},False{},Nat.cmp(Word.to_nat(p,at),Word.to_nat(p,bt))),Word.cmp.fin(True{},False{},Word.cmp(p,at,bt)),
            binary_compare(True{},False{},Word.to_nat(p,at),Word.to_nat(p,bt)),
            Equal.cong(Cmp,Cmp,c => Word.cmp.fin(True{},False{},c),Nat.cmp(Word.to_nat(p,at),Word.to_nat(p,bt)),Word.cmp(p,at,bt),word_comparison_is_natural_order(p,at,bt)))
        case WCon{True{},+at} WCon{True{},+bt}:
          Equal.trans(Cmp,Nat.cmp(A.place(True{},Word.to_nat(p,at)),A.place(True{},Word.to_nat(p,bt))),Word.cmp.fin(True{},True{},Nat.cmp(Word.to_nat(p,at),Word.to_nat(p,bt))),Word.cmp.fin(True{},True{},Word.cmp(p,at,bt)),
            binary_compare(True{},True{},Word.to_nat(p,at),Word.to_nat(p,bt)),
            Equal.cong(Cmp,Cmp,c => Word.cmp.fin(True{},True{},c),Nat.cmp(Word.to_nat(p,at),Word.to_nat(p,bt)),Word.cmp(p,at,bt),word_comparison_is_natural_order(p,at,bt)))

law actual_unsigned_lt_is_natural_order:
  for +a: V.Int64
  for +b: V.Int64
  {I.unsigned_lt(a,b) == Nat.is_lt(A.unsigned(a),A.unsigned(b)) : Bool}
def actual_unsigned_lt_is_natural_order(a,b):
  Equal.trans(Bool,I.unsigned_lt(a,b),Cmp.is_lt(Word.cmp(64n,A.bits(a),A.bits(b))),Nat.is_lt(A.unsigned(a),A.unsigned(b)),G.unsigned_lt_is_word_order(a,b),
    Equal.cong(Cmp,Bool,Cmp.is_lt,Word.cmp(64n,A.bits(a),A.bits(b)),Nat.cmp(A.unsigned(a),A.unsigned(b)),
      Equal.sym(Cmp,Nat.cmp(A.unsigned(a),A.unsigned(b)),Word.cmp(64n,A.bits(a),A.bits(b)),word_comparison_is_natural_order(64n,A.bits(a),A.bits(b)))))
