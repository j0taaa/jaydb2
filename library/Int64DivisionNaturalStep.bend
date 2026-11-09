# Independent natural arithmetic of one Euclidean restoring-division step.
import Base
import ./Int64NaturalOrder.bend as O
import ./Int64NatProduct.bend as N
import ./Int64ShiftArithmetic.bend as T
import ./Int64Proofs.bend as A
import ../proof/Foundations.bend as F

law compare_cancels_prefix:
  for +prefix: Nat
  for +a: Nat
  for +b: Nat
  {Nat.cmp(Nat.add(prefix,a),Nat.add(prefix,b)) == Nat.cmp(a,b) : Cmp}
def compare_cancels_prefix(prefix,a,b):
  match prefix:
    case 0n: {==}
    case 1n+p: compare_cancels_prefix(p,a,b)

law lt_is_literal:
  for +c: Cmp
  for less: {Cmp.is_lt(c) == True{} : Bool}
  {c == LT{} : Cmp}
def lt_is_literal(c,less):
  match c:
    case LT{}: {==}
    case EQ{}: F.absurd_boolean({EQ{} == LT{} : Cmp},less)
    case GT{}: F.absurd_boolean({GT{} == LT{} : Cmp},less)

law placed_remainder_below_doubled_divisor:
  for +bit: Bool
  for +r: Nat
  for +d: Nat
  for small: {Nat.is_lt(r,d) == True{} : Bool}
  {Nat.is_lt(A.place(bit,r),Nat.double(d)) == True{} : Bool}
def placed_remainder_below_doubled_divisor(bit,r,d,small):
  match bit:
    case False{}:
      Equal.trans(Bool,Nat.is_lt(Nat.double(r),Nat.double(d)),Nat.is_lt(r,d),True{},Equal.cong(Cmp,Bool,Cmp.is_lt,Nat.cmp(Nat.double(r),Nat.double(d)),Nat.cmp(r,d),O.even_even_compare(r,d)),small)
    case True{}:
      Equal.cong(Cmp,Bool,Cmp.is_lt,Nat.cmp(1n+Nat.double(r),Nat.double(d)),LT{},
        Equal.trans(Cmp,Nat.cmp(1n+Nat.double(r),Nat.double(d)),Word.cmp.fin(True{},False{},Nat.cmp(r,d)),LT{},O.odd_even_compare(r,d),
          Equal.cong(Cmp,Cmp,c => Word.cmp.fin(True{},False{},c),Nat.cmp(r,d),LT{},lt_is_literal(Nat.cmp(r,d),small))))

law subtraction_restores_strict_remainder:
  for +bit: Bool
  for +r: Nat
  for +d: Nat
  for +next: Nat
  for +remainder: Nat
  for small: {Nat.is_lt(r,d) == True{} : Bool}
  for formed: {next == A.place(bit,r) : Nat}
  for difference: {next == Nat.add(d,remainder) : Nat}
  {Nat.is_lt(remainder,d) == True{} : Bool}
def subtraction_restores_strict_remainder(bit,r,d,next,remainder,small,formed,difference):
  Equal.trans(Bool,Nat.is_lt(remainder,d),Nat.is_lt(Nat.add(d,remainder),Nat.add(d,d)),True{},
    Equal.sym(Bool,Nat.is_lt(Nat.add(d,remainder),Nat.add(d,d)),Nat.is_lt(remainder,d),Equal.cong(Cmp,Bool,Cmp.is_lt,Nat.cmp(Nat.add(d,remainder),Nat.add(d,d)),Nat.cmp(remainder,d),compare_cancels_prefix(d,remainder,d))),
    Equal.trans(Bool,Nat.is_lt(Nat.add(d,remainder),Nat.add(d,d)),Nat.is_lt(next,Nat.double(d)),True{},
      Equal.trans(Bool,Nat.is_lt(Nat.add(d,remainder),Nat.add(d,d)),Nat.is_lt(next,Nat.add(d,d)),Nat.is_lt(next,Nat.double(d)),
        Equal.cong(Nat,Bool,v => Nat.is_lt(v,Nat.add(d,d)),Nat.add(d,remainder),next,Equal.sym(Nat,next,Nat.add(d,remainder),difference)),
        Equal.cong(Nat,Bool,v => Nat.is_lt(next,v),Nat.add(d,d),Nat.double(d),Equal.sym(Nat,Nat.double(d),Nat.add(d,d),T.double_is_self_sum(d)))),
      Equal.trans(Bool,Nat.is_lt(next,Nat.double(d)),Nat.is_lt(A.place(bit,r),Nat.double(d)),True{},Equal.cong(Nat,Bool,v => Nat.is_lt(v,Nat.double(d)),next,A.place(bit,r),formed),placed_remainder_below_doubled_divisor(bit,r,d,small))))

law doubled_right_product:
  for +a: Nat
  for +b: Nat
  {Nat.mul(a,Nat.double(b)) == Nat.double(Nat.mul(a,b)) : Nat}
def doubled_right_product(a,b):
  Equal.trans(Nat,Nat.mul(a,Nat.double(b)),Nat.mul(a,Nat.add(b,b)),Nat.double(Nat.mul(a,b)),Equal.cong(Nat,Nat,v => Nat.mul(a,v),Nat.double(b),Nat.add(b,b),T.double_is_self_sum(b)),
    Equal.trans(Nat,Nat.mul(a,Nat.add(b,b)),Nat.add(Nat.mul(a,b),Nat.mul(a,b)),Nat.double(Nat.mul(a,b)),N.mul_add_right(a,b,b),Equal.sym(Nat,Nat.double(Nat.mul(a,b)),Nat.add(Nat.mul(a,b),Nat.mul(a,b)),T.double_is_self_sum(Nat.mul(a,b)))))

law place_sum:
  for +bit: Bool
  for +a: Nat
  for +b: Nat
  {A.place(bit,Nat.add(a,b)) == Nat.add(Nat.double(a),A.place(bit,b)) : Nat}
def place_sum(bit,a,b):
  match bit:
    case False{}: A.double_sum(a,b)
    case True{}:
      Equal.trans(Nat,1n+Nat.double(Nat.add(a,b)),1n+Nat.add(Nat.double(a),Nat.double(b)),Nat.add(Nat.double(a),1n+Nat.double(b)),Equal.cong(Nat,Nat,v => 1n+v,Nat.double(Nat.add(a,b)),Nat.add(Nat.double(a),Nat.double(b)),A.double_sum(a,b)),
        Equal.sym(Nat,Nat.add(Nat.double(a),1n+Nat.double(b)),1n+Nat.add(Nat.double(a),Nat.double(b)),A.add_right_successor(Nat.double(a),Nat.double(b))))

law binary_dividend_step:
  for +bit: Bool
  for +d: Nat
  for +q: Nat
  for +r: Nat
  {A.place(bit,Nat.add(Nat.mul(d,q),r)) == Nat.add(Nat.mul(d,Nat.double(q)),A.place(bit,r)) : Nat}
def binary_dividend_step(bit,d,q,r):
  Equal.trans(Nat,A.place(bit,Nat.add(Nat.mul(d,q),r)),Nat.add(Nat.double(Nat.mul(d,q)),A.place(bit,r)),Nat.add(Nat.mul(d,Nat.double(q)),A.place(bit,r)),place_sum(bit,Nat.mul(d,q),r),
    Equal.cong(Nat,Nat,v => Nat.add(v,A.place(bit,r)),Nat.double(Nat.mul(d,q)),Nat.mul(d,Nat.double(q)),Equal.sym(Nat,Nat.mul(d,Nat.double(q)),Nat.double(Nat.mul(d,q)),doubled_right_product(d,q))))

law quotient_bit_accounts_for_subtraction:
  for +subtract: Bool
  for +d: Nat
  for +q: Nat
  for +remainder: Nat
  {Nat.add(Nat.mul(d,A.place(subtract,q)),remainder) == Nat.add(Nat.mul(d,Nat.double(q)),Bool.pick(Nat,subtract,Nat.add(d,remainder),remainder)) : Nat}
def quotient_bit_accounts_for_subtraction(subtract,d,q,remainder):
  match subtract:
    case False{}: {==}
    case True{}:
      Equal.trans(Nat,Nat.add(Nat.mul(d,1n+Nat.double(q)),remainder),Nat.add(Nat.add(d,Nat.mul(d,Nat.double(q))),remainder),Nat.add(Nat.mul(d,Nat.double(q)),Nat.add(d,remainder)),
        Equal.cong(Nat,Nat,v => Nat.add(v,remainder),Nat.mul(d,1n+Nat.double(q)),Nat.add(d,Nat.mul(d,Nat.double(q))),N.mul_successor_right(d,Nat.double(q))),
        Equal.trans(Nat,Nat.add(Nat.add(d,Nat.mul(d,Nat.double(q))),remainder),Nat.add(d,Nat.add(Nat.mul(d,Nat.double(q)),remainder)),Nat.add(Nat.mul(d,Nat.double(q)),Nat.add(d,remainder)),A.add_associative(d,Nat.mul(d,Nat.double(q)),remainder),N.swap_middle(d,Nat.mul(d,Nat.double(q)),remainder)))
