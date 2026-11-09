# Unbounded natural multiplication facts, independent of the machine algorithm.
import Base
import ./Int64Proofs.bend as A
import ./Int64ShiftArithmetic.bend as T

law swap_middle:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}
def swap_middle(a, b, c):
  %A.add_associative(a, b, c) : { _ == Nat.add(b, Nat.add(a, c)) : Nat}
  %Equal.sym(Nat, Nat.add(a,b), Nat.add(b,a), A.add_commutative(a,b)) : {Nat.add(_,c) == Nat.add(b,Nat.add(a,c)) : Nat}
  A.add_associative(b,a,c)

law rotate_sum:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(a, Nat.add(b,c)) == Nat.add(c, Nat.add(a,b)) : Nat}
def rotate_sum(a,b,c):
  Equal.trans(Nat, Nat.add(a,Nat.add(b,c)), Nat.add(Nat.add(a,b),c), Nat.add(c,Nat.add(a,b)),
    Equal.sym(Nat,Nat.add(Nat.add(a,b),c),Nat.add(a,Nat.add(b,c)),A.add_associative(a,b,c)),
    A.add_commutative(Nat.add(a,b),c))

law mul_zero_right:
  for +a: Nat
  {Nat.mul(a,0n) == 0n : Nat}
def mul_zero_right(a):
  match a:
    case 0n: {==}
    case 1n+p: mul_zero_right(p)

law mul_add_left:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(Nat.add(a,b),c) == Nat.add(Nat.mul(a,c),Nat.mul(b,c)) : Nat}
def mul_add_left(a,b,c):
  match a:
    case 0n: {==}
    case 1n+p:
      Equal.trans(Nat, Nat.add(c,Nat.mul(Nat.add(p,b),c)), Nat.add(c,Nat.add(Nat.mul(p,c),Nat.mul(b,c))),
        Nat.add(Nat.add(c,Nat.mul(p,c)),Nat.mul(b,c)),
        Equal.cong(Nat,Nat,n => Nat.add(c,n),Nat.mul(Nat.add(p,b),c),Nat.add(Nat.mul(p,c),Nat.mul(b,c)),mul_add_left(p,b,c)),
        Equal.sym(Nat,Nat.add(Nat.add(c,Nat.mul(p,c)),Nat.mul(b,c)),Nat.add(c,Nat.add(Nat.mul(p,c),Nat.mul(b,c))),A.add_associative(c,Nat.mul(p,c),Nat.mul(b,c))))

law four_sum:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  {Nat.add(Nat.add(a,b),Nat.add(c,d)) == Nat.add(Nat.add(a,c),Nat.add(b,d)) : Nat}
def four_sum(a,b,c,d):
  Equal.trans(Nat,Nat.add(Nat.add(a,b),Nat.add(c,d)),Nat.add(a,Nat.add(b,Nat.add(c,d))),Nat.add(Nat.add(a,c),Nat.add(b,d)),A.add_associative(a,b,Nat.add(c,d)),
    Equal.trans(Nat,Nat.add(a,Nat.add(b,Nat.add(c,d))),Nat.add(a,Nat.add(c,Nat.add(b,d))),Nat.add(Nat.add(a,c),Nat.add(b,d)),
      Equal.cong(Nat,Nat,n => Nat.add(a,n),Nat.add(b,Nat.add(c,d)),Nat.add(c,Nat.add(b,d)),swap_middle(b,c,d)),
      Equal.sym(Nat,Nat.add(Nat.add(a,c),Nat.add(b,d)),Nat.add(a,Nat.add(c,Nat.add(b,d))),A.add_associative(a,c,Nat.add(b,d)))))

law mul_add_right:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(a,Nat.add(b,c)) == Nat.add(Nat.mul(a,b),Nat.mul(a,c)) : Nat}
def mul_add_right(a,b,c):
  match a:
    case 0n: {==}
    case 1n+p:
      Equal.trans(Nat,Nat.add(Nat.add(b,c),Nat.mul(p,Nat.add(b,c))),Nat.add(Nat.add(b,c),Nat.add(Nat.mul(p,b),Nat.mul(p,c))),
        Nat.add(Nat.add(b,Nat.mul(p,b)),Nat.add(c,Nat.mul(p,c))),
        Equal.cong(Nat,Nat,n => Nat.add(Nat.add(b,c),n),Nat.mul(p,Nat.add(b,c)),Nat.add(Nat.mul(p,b),Nat.mul(p,c)),mul_add_right(p,b,c)),
        four_sum(b,c,Nat.mul(p,b),Nat.mul(p,c)))

law mul_one_right:
  for +a: Nat
  {Nat.mul(a,1n) == a : Nat}
def mul_one_right(a):
  match a:
    case 0n: {==}
    case 1n+p: Equal.cong(Nat,Nat,n => 1n+n,Nat.mul(p,1n),p,mul_one_right(p))

law mul_successor_right:
  for +a: Nat
  for +b: Nat
  {Nat.mul(a,1n+b) == Nat.add(a,Nat.mul(a,b)) : Nat}
def mul_successor_right(a,b):
  Equal.trans(Nat,Nat.mul(a,1n+b),Nat.add(Nat.mul(a,1n),Nat.mul(a,b)),Nat.add(a,Nat.mul(a,b)),mul_add_right(a,1n,b),
    Equal.cong(Nat,Nat,n => Nat.add(n,Nat.mul(a,b)),Nat.mul(a,1n),a,mul_one_right(a)))

law mul_commutative:
  for +a: Nat
  for +b: Nat
  {Nat.mul(a,b) == Nat.mul(b,a) : Nat}
def mul_commutative(a,b):
  match a:
    case 0n: Equal.sym(Nat,Nat.mul(b,0n),0n,mul_zero_right(b))
    case 1n+p:
      Equal.trans(Nat,Nat.add(b,Nat.mul(p,b)),Nat.add(b,Nat.mul(b,p)),Nat.mul(b,1n+p),
        Equal.cong(Nat,Nat,n => Nat.add(b,n),Nat.mul(p,b),Nat.mul(b,p),mul_commutative(p,b)),
        Equal.sym(Nat,Nat.mul(b,1n+p),Nat.add(b,Nat.mul(b,p)),mul_successor_right(b,p)))

law mul_associative:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(Nat.mul(a,b),c) == Nat.mul(a,Nat.mul(b,c)) : Nat}
def mul_associative(a,b,c):
  match a:
    case 0n: {==}
    case 1n+p:
      Equal.trans(Nat,Nat.mul(Nat.add(b,Nat.mul(p,b)),c),Nat.add(Nat.mul(b,c),Nat.mul(Nat.mul(p,b),c)),Nat.add(Nat.mul(b,c),Nat.mul(p,Nat.mul(b,c))),
        mul_add_left(b,Nat.mul(p,b),c),Equal.cong(Nat,Nat,n => Nat.add(Nat.mul(b,c),n),Nat.mul(Nat.mul(p,b),c),Nat.mul(p,Nat.mul(b,c)),mul_associative(p,b,c)))

law double_product:
  for +a: Nat
  for +b: Nat
  {Nat.mul(Nat.double(b),a) == Nat.mul(b,Nat.double(a)) : Nat}
def double_product(a,b):
  %Equal.sym(Nat,Nat.double(b),Nat.add(b,b),T.double_is_self_sum(b)) : {Nat.mul(_,a) == Nat.mul(b,Nat.double(a)) : Nat}
  %Equal.sym(Nat,Nat.double(a),Nat.add(a,a),T.double_is_self_sum(a)) : {Nat.mul(Nat.add(b,b),a) == Nat.mul(b,_) : Nat}
  Equal.trans(Nat,Nat.mul(Nat.add(b,b),a),Nat.add(Nat.mul(b,a),Nat.mul(b,a)),Nat.mul(b,Nat.add(a,a)),mul_add_left(b,b,a),
    Equal.sym(Nat,Nat.mul(b,Nat.add(a,a)),Nat.add(Nat.mul(b,a),Nat.mul(b,a)),mul_add_right(b,a,a)))

# One binary multiplier step preserves acc + b*a before machine truncation.
law binary_product_step:
  for +odd: Bool
  for +a: Nat
  for +b: Nat
  for +acc: Nat
  {Nat.add(acc,Nat.mul(A.place(odd,b),a)) == Nat.add(Bool.pick(Nat,odd,Nat.add(acc,a),acc),Nat.mul(b,Nat.double(a))) : Nat}
def binary_product_step(odd,a,b,acc):
  match odd:
    case False{}:
      Equal.cong(Nat,Nat,n => Nat.add(acc,n),Nat.mul(Nat.double(b),a),Nat.mul(b,Nat.double(a)),double_product(a,b))
    case True{}:
      Equal.trans(Nat,Nat.add(acc,Nat.add(a,Nat.mul(Nat.double(b),a))),Nat.add(acc,Nat.add(a,Nat.mul(b,Nat.double(a)))),Nat.add(Nat.add(acc,a),Nat.mul(b,Nat.double(a))),
        Equal.cong(Nat,Nat,n => Nat.add(acc,Nat.add(a,n)),Nat.mul(Nat.double(b),a),Nat.mul(b,Nat.double(a)),double_product(a,b)),
        Equal.sym(Nat,Nat.add(Nat.add(acc,a),Nat.mul(b,Nat.double(a))),Nat.add(acc,Nat.add(a,Nat.mul(b,Nat.double(a)))),A.add_associative(acc,a,Nat.mul(b,Nat.double(a)))))
