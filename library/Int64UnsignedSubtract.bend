# Mathematical unsigned subtraction under its actual no-borrow comparison.
import Base
import ./Int64Flags.bend as G
import ./Int64Proofs.bend as A
import ./Int64SubProofs.bend as Sub
import ./Int64.bend as I
import ./Value.bend as V
import ../proof/CodecSumsBits.bend as S
import ../proof/Foundations.bend as F

law subtraction_is_complemented_addition:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +carry: Bool
  {Word.adc(n,a,b,True{},carry) == Word.adc(n,a,Word.not(n,b),False{},carry) : Word(n)}
def subtraction_is_complemented_addition(n,a,b,carry):
  match n:
    case 0n: {==}
    case 1n+p:
      match a b carry:
        case WCon{False{},+at} WCon{False{},+bt} False{}:
          Equal.cong(Word(p),Word(1n+p),w => WCon{True{},w},Word.adc(p,at,bt,True{},False{}),Word.adc(p,at,Word.not(p,bt),False{},False{}),subtraction_is_complemented_addition(p,at,bt,False{}))
        case WCon{False{},+at} WCon{False{},+bt} True{}:
          Equal.cong(Word(p),Word(1n+p),w => WCon{False{},w},Word.adc(p,at,bt,True{},True{}),Word.adc(p,at,Word.not(p,bt),False{},True{}),subtraction_is_complemented_addition(p,at,bt,True{}))
        case WCon{False{},+at} WCon{True{},+bt} False{}:
          Equal.cong(Word(p),Word(1n+p),w => WCon{False{},w},Word.adc(p,at,bt,True{},False{}),Word.adc(p,at,Word.not(p,bt),False{},False{}),subtraction_is_complemented_addition(p,at,bt,False{}))
        case WCon{False{},+at} WCon{True{},+bt} True{}:
          Equal.cong(Word(p),Word(1n+p),w => WCon{True{},w},Word.adc(p,at,bt,True{},False{}),Word.adc(p,at,Word.not(p,bt),False{},False{}),subtraction_is_complemented_addition(p,at,bt,False{}))
        case WCon{True{},+at} WCon{False{},+bt} False{}:
          Equal.cong(Word(p),Word(1n+p),w => WCon{False{},w},Word.adc(p,at,bt,True{},True{}),Word.adc(p,at,Word.not(p,bt),False{},True{}),subtraction_is_complemented_addition(p,at,bt,True{}))
        case WCon{True{},+at} WCon{False{},+bt} True{}:
          Equal.cong(Word(p),Word(1n+p),w => WCon{True{},w},Word.adc(p,at,bt,True{},True{}),Word.adc(p,at,Word.not(p,bt),False{},True{}),subtraction_is_complemented_addition(p,at,bt,True{}))
        case WCon{True{},+at} WCon{True{},+bt} False{}:
          Equal.cong(Word(p),Word(1n+p),w => WCon{True{},w},Word.adc(p,at,bt,True{},False{}),Word.adc(p,at,Word.not(p,bt),False{},False{}),subtraction_is_complemented_addition(p,at,bt,False{}))
        case WCon{True{},+at} WCon{True{},+bt} True{}:
          Equal.cong(Word(p),Word(1n+p),w => WCon{False{},w},Word.adc(p,at,bt,True{},True{}),Word.adc(p,at,Word.not(p,bt),False{},True{}),subtraction_is_complemented_addition(p,at,bt,True{}))

law complement_gap_is_radix:
  for +n: Nat
  for +b: Word(n)
  {Nat.add(Word.to_nat(n,b),1n+Word.to_nat(n,Word.not(n,b))) == A.modulus(n) : Nat}
def complement_gap_is_radix(n,b):
  Equal.trans(Nat,Nat.add(Word.to_nat(n,b),1n+Word.to_nat(n,Word.not(n,b))),1n+Nat.add(Word.to_nat(n,b),Word.to_nat(n,Word.not(n,b))),A.modulus(n),
    A.add_right_successor(Word.to_nat(n,b),Word.to_nat(n,Word.not(n,b))),Equal.cong(Nat,Nat,v => 1n+v,Nat.add(Word.to_nat(n,b),Word.to_nat(n,Word.not(n,b))),A.maximum_value(n),A.complement_value(n,b)))

law cancel_complemented_adder:
  for +width: Nat
  for +x: Nat
  for +y: Nat
  for +gap: Nat
  for +r: Nat
  for +carry: Bool
  for truth: {carry == True{} : Bool}
  for exact: {Nat.add(x,gap) == Nat.add(r,A.spill(width,carry)) : Nat}
  for complement: {Nat.add(y,gap) == A.modulus(width) : Nat}
  {x == Nat.add(y,r) : Nat}
def cancel_complemented_adder(width,x,y,gap,r,carry,truth,exact,complement):
  match carry:
    case False{}: F.absurd_boolean({x == Nat.add(y,r) : Nat},truth)
    case True{}:
      A.add_right_cancel(gap,x,Nat.add(y,r),Equal.trans(Nat,Nat.add(x,gap),Nat.add(r,A.modulus(width)),Nat.add(Nat.add(y,r),gap),exact,
        Equal.trans(Nat,Nat.add(r,A.modulus(width)),Nat.add(r,Nat.add(y,gap)),Nat.add(Nat.add(y,r),gap),
          Equal.cong(Nat,Nat,v => Nat.add(r,v),A.modulus(width),Nat.add(y,gap),Equal.sym(Nat,Nat.add(y,gap),A.modulus(width),complement)),
          Equal.trans(Nat,Nat.add(r,Nat.add(y,gap)),Nat.add(Nat.add(r,y),gap),Nat.add(Nat.add(y,r),gap),
            Equal.sym(Nat,Nat.add(Nat.add(r,y),gap),Nat.add(r,Nat.add(y,gap)),A.add_associative(r,y,gap)),
            Equal.cong(Nat,Nat,v => Nat.add(v,gap),Nat.add(r,y),Nat.add(y,r),A.add_commutative(r,y))))))

law true_carry_order:
  for +order: Cmp
  {Sub.carry_order(True{},order) == Bool.not(Cmp.is_lt(order)) : Bool}
def true_carry_order(order):
  match order:
    case LT{}: {==}
    case EQ{}: {==}
    case GT{}: {==}

law not_false_is_true:
  for +b: Bool
  for false: {b == False{} : Bool}
  {Bool.not(b) == True{} : Bool}
def not_false_is_true(b,false):
  Equal.cong(Bool,Bool,Bool.not,b,False{},false)

law word_subtract_without_borrow:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for no_borrow: {Cmp.is_lt(Word.cmp(n,a,b)) == False{} : Bool}
  {Word.to_nat(n,a) == Nat.add(Word.to_nat(n,b),Word.to_nat(n,Word.sub(n,a,b))) : Nat}
def word_subtract_without_borrow(n,a,b,no_borrow):
  Equal.trans(Nat,Word.to_nat(n,a),Nat.add(Word.to_nat(n,b),Word.to_nat(n,Word.adc(n,a,Word.not(n,b),False{},True{}))),Nat.add(Word.to_nat(n,b),Word.to_nat(n,Word.sub(n,a,b))),
    cancel_complemented_adder(n,Word.to_nat(n,a),Word.to_nat(n,b),1n+Word.to_nat(n,Word.not(n,b)),Word.to_nat(n,Word.adc(n,a,Word.not(n,b),False{},True{})),S.carry(n,a,Word.not(n,b),True{}),
      Equal.trans(Bool,S.carry(n,a,Word.not(n,b),True{}),Sub.carry_order(True{},Word.cmp(n,a,b)),True{},Sub.subtraction_carry_reflects_comparison(n,a,b,True{}),
        Equal.trans(Bool,Sub.carry_order(True{},Word.cmp(n,a,b)),Bool.not(Cmp.is_lt(Word.cmp(n,a,b))),True{},true_carry_order(Word.cmp(n,a,b)),not_false_is_true(Cmp.is_lt(Word.cmp(n,a,b)),no_borrow))),
      Equal.trans(Nat,Nat.add(Word.to_nat(n,a),1n+Word.to_nat(n,Word.not(n,b))),Nat.add(Word.to_nat(n,a),Nat.add(Word.to_nat(n,Word.not(n,b)),1n)),Nat.add(Word.to_nat(n,Word.adc(n,a,Word.not(n,b),False{},True{})),A.spill(n,S.carry(n,a,Word.not(n,b),True{}))),
        Equal.cong(Nat,Nat,v => Nat.add(Word.to_nat(n,a),v),1n+Word.to_nat(n,Word.not(n,b)),Nat.add(Word.to_nat(n,Word.not(n,b)),1n),Equal.sym(Nat,Nat.add(Word.to_nat(n,Word.not(n,b)),1n),1n+Word.to_nat(n,Word.not(n,b)),A.add_commutative(Word.to_nat(n,Word.not(n,b)),1n))),A.adc_natural(n,a,Word.not(n,b),True{})),complement_gap_is_radix(n,b)),
    Equal.cong(Word(n),Nat,w => Nat.add(Word.to_nat(n,b),Word.to_nat(n,w)),Word.adc(n,a,Word.not(n,b),False{},True{}),Word.sub(n,a,b),Equal.sym(Word(n),Word.sub(n,a,b),Word.adc(n,a,Word.not(n,b),False{},True{}),subtraction_is_complemented_addition(n,a,b,True{}))))

law actual_unsigned_subtract_is_natural_difference:
  for +a: V.Int64
  for +b: V.Int64
  for no_borrow: {I.unsigned_lt(a,b) == False{} : Bool}
  {A.unsigned(a) == Nat.add(A.unsigned(b),A.unsigned(I.wrapping_sub(a,b))) : Nat}
def actual_unsigned_subtract_is_natural_difference(a,b,no_borrow):
  Equal.trans(Nat,A.unsigned(a),Nat.add(A.unsigned(b),Word.to_nat(64n,Word.sub(64n,A.bits(a),A.bits(b)))),Nat.add(A.unsigned(b),A.unsigned(I.wrapping_sub(a,b))),
    word_subtract_without_borrow(64n,A.bits(a),A.bits(b),Equal.trans(Bool,Cmp.is_lt(Word.cmp(64n,A.bits(a),A.bits(b))),I.unsigned_lt(a,b),False{},
      Equal.sym(Bool,I.unsigned_lt(a,b),Cmp.is_lt(Word.cmp(64n,A.bits(a),A.bits(b))),G.unsigned_lt_is_word_order(a,b)),no_borrow)),
    Equal.cong(Word(64n),Nat,w => Nat.add(A.unsigned(b),Word.to_nat(64n,w)),Word.sub(64n,A.bits(a),A.bits(b)),A.bits(I.wrapping_sub(a,b)),
      Equal.sym(Word(64n),A.bits(I.wrapping_sub(a,b)),Word.sub(64n,A.bits(a),A.bits(b)),Sub.wrapping_sub_is_full_word_sub(a,b))))
