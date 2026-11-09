# Symbolic binary scaling. No closed large unary radix is evaluated.
import Base
import ./Int64Proofs.bend as A
import ./Int64NatProduct.bend as N
import ./Int64ShiftArithmetic.bend as T
import ../proof/CodecAcceptanceTags.bend as Tags

def scale(steps: Nat,value: Nat) -> Nat:
  match steps:
    case 0n: value
    case 1n+p: scale(p,Nat.double(value))

law scaling_is_radix_multiplication:
  for +width: Nat
  for +value: Nat
  {scale(width,value) == Nat.mul(value,A.modulus(width)) : Nat}
def scaling_is_radix_multiplication(width,value):
  match width:
    case 0n: Equal.sym(Nat,Nat.mul(value,1n),value,N.mul_one_right(value))
    case 1n+p:
      Equal.trans(Nat,scale(p,Nat.double(value)),Nat.mul(Nat.double(value),A.modulus(p)),Nat.mul(value,A.modulus(1n+p)),
        scaling_is_radix_multiplication(p,Nat.double(value)),N.double_product(A.modulus(p),value))

law scaling_is_injective:
  for +width: Nat
  for +a: Nat
  for +b: Nat
  for same: {scale(width,a) == scale(width,b) : Nat}
  {a == b : Nat}
def scaling_is_injective(width,a,b,same):
  match width:
    case 0n: same
    case 1n+p:
      Tags.double_injective(a,b,scaling_is_injective(p,Nat.double(a),Nat.double(b),same))

law doubled_left_factor:
  for +a: Nat
  for +b: Nat
  {Nat.mul(Nat.double(a),b) == Nat.double(Nat.mul(a,b)) : Nat}
def doubled_left_factor(a,b):
  Equal.trans(Nat,Nat.mul(Nat.double(a),b),Nat.mul(Nat.add(a,a),b),Nat.double(Nat.mul(a,b)),
    Equal.cong(Nat,Nat,n => Nat.mul(n,b),Nat.double(a),Nat.add(a,a),T.double_is_self_sum(a)),
    Equal.trans(Nat,Nat.mul(Nat.add(a,a),b),Nat.add(Nat.mul(a,b),Nat.mul(a,b)),Nat.double(Nat.mul(a,b)),N.mul_add_left(a,a,b),
      Equal.sym(Nat,Nat.double(Nat.mul(a,b)),Nat.add(Nat.mul(a,b),Nat.mul(a,b)),T.double_is_self_sum(Nat.mul(a,b)))))

law placed_prefix_product:
  for +width: Nat
  for +bit: Bool
  for +prefix: Nat
  {Nat.mul(A.place(bit,prefix),A.modulus(width)) == Nat.add(A.spill(width,bit),Nat.double(Nat.mul(prefix,A.modulus(width)))) : Nat}
def placed_prefix_product(width,bit,prefix):
  match bit:
    case False{}: doubled_left_factor(prefix,A.modulus(width))
    case True{}:
      Equal.cong(Nat,Nat,n => Nat.add(A.modulus(width),n),Nat.mul(Nat.double(prefix),A.modulus(width)),Nat.double(Nat.mul(prefix,A.modulus(width))),doubled_left_factor(prefix,A.modulus(width)))
