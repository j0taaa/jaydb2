# All quotient carries are accounted for mathematically. A final representable
# dividend will force this nonnegative carry coefficient to be zero.
import Base
import ./Int64RadixScale.bend as R
import ./Int64BitInsert.bend as B
import ./Int64Proofs.bend as A
import ./Int64NatProduct.bend as N
import ./Int64ShiftArithmetic.bend as T
import ./Int64.bend as I
import ./Value.bend as V

type Residue<-width: Nat,-word_value: Nat,-natural: Nat> is Type:
  Residue{wraps: Nat,exact: {natural == Nat.add(word_value,Nat.mul(wraps,A.modulus(width))) : Nat}}

law place_left_sum:
  for +bit: Bool
  for +a: Nat
  for +b: Nat
  {A.place(bit,Nat.add(a,b)) == Nat.add(A.place(bit,a),Nat.double(b)) : Nat}
def place_left_sum(bit,a,b):
  match bit:
    case False{}: A.double_sum(a,b)
    case True{}:
      Equal.cong(Nat,Nat,v => 1n+v,Nat.double(Nat.add(a,b)),Nat.add(Nat.double(a),Nat.double(b)),A.double_sum(a,b))

law bit_times_radix:
  for +width: Nat
  for +bit: Bool
  {Nat.mul(A.bit(bit),A.modulus(width)) == A.spill(width,bit) : Nat}
def bit_times_radix(width,bit):
  match bit:
    case False{}: {==}
    case True{}: A.add_zero_right(A.modulus(width))

law next_coefficient_product:
  for +width: Nat
  for +carry: Bool
  for +wraps: Nat
  {Nat.mul(Nat.add(A.bit(carry),Nat.double(wraps)),A.modulus(width)) == Nat.add(A.spill(width,carry),Nat.double(Nat.mul(wraps,A.modulus(width)))) : Nat}
def next_coefficient_product(width,carry,wraps):
  Equal.trans(Nat,Nat.mul(Nat.add(A.bit(carry),Nat.double(wraps)),A.modulus(width)),Nat.add(Nat.mul(A.bit(carry),A.modulus(width)),Nat.mul(Nat.double(wraps),A.modulus(width))),Nat.add(A.spill(width,carry),Nat.double(Nat.mul(wraps,A.modulus(width)))),N.mul_add_left(A.bit(carry),Nat.double(wraps),A.modulus(width)),
    Equal.trans(Nat,Nat.add(Nat.mul(A.bit(carry),A.modulus(width)),Nat.mul(Nat.double(wraps),A.modulus(width))),Nat.add(A.spill(width,carry),Nat.mul(Nat.double(wraps),A.modulus(width))),Nat.add(A.spill(width,carry),Nat.double(Nat.mul(wraps,A.modulus(width)))),
      Equal.cong(Nat,Nat,v => Nat.add(v,Nat.mul(Nat.double(wraps),A.modulus(width))),Nat.mul(A.bit(carry),A.modulus(width)),A.spill(width,carry),bit_times_radix(width,carry)),
      Equal.cong(Nat,Nat,v => Nat.add(A.spill(width,carry),v),Nat.mul(Nat.double(wraps),A.modulus(width)),Nat.double(Nat.mul(wraps,A.modulus(width))),R.doubled_left_factor(wraps,A.modulus(width)))))

law bit_step_preserves_residue:
  for +width: Nat
  for +word_value: Nat
  for +natural: Nat
  for +next_value: Nat
  for +bit: Bool
  for +carry: Bool
  for residue: Residue<width,word_value,natural>
  for actual: {A.place(bit,word_value) == Nat.add(next_value,A.spill(width,carry)) : Nat}
  Residue<width,next_value,A.place(bit,natural)>
def bit_step_preserves_residue(width,word_value,natural,next_value,bit,carry,residue,actual):
  match residue:
    case Residue{+wraps,exact}:
      Residue{Nat.add(A.bit(carry),Nat.double(wraps)),
        Equal.trans(Nat,A.place(bit,natural),A.place(bit,Nat.add(word_value,Nat.mul(wraps,A.modulus(width)))),Nat.add(next_value,Nat.mul(Nat.add(A.bit(carry),Nat.double(wraps)),A.modulus(width))),
          Equal.cong(Nat,Nat,v => A.place(bit,v),natural,Nat.add(word_value,Nat.mul(wraps,A.modulus(width))),exact),
          Equal.trans(Nat,A.place(bit,Nat.add(word_value,Nat.mul(wraps,A.modulus(width)))),Nat.add(A.place(bit,word_value),Nat.double(Nat.mul(wraps,A.modulus(width)))),Nat.add(next_value,Nat.mul(Nat.add(A.bit(carry),Nat.double(wraps)),A.modulus(width))),place_left_sum(bit,word_value,Nat.mul(wraps,A.modulus(width))),
            Equal.trans(Nat,Nat.add(A.place(bit,word_value),Nat.double(Nat.mul(wraps,A.modulus(width)))),Nat.add(Nat.add(next_value,A.spill(width,carry)),Nat.double(Nat.mul(wraps,A.modulus(width)))),Nat.add(next_value,Nat.mul(Nat.add(A.bit(carry),Nat.double(wraps)),A.modulus(width))),
              Equal.cong(Nat,Nat,v => Nat.add(v,Nat.double(Nat.mul(wraps,A.modulus(width)))),A.place(bit,word_value),Nat.add(next_value,A.spill(width,carry)),actual),
              Equal.trans(Nat,Nat.add(Nat.add(next_value,A.spill(width,carry)),Nat.double(Nat.mul(wraps,A.modulus(width)))),Nat.add(next_value,Nat.add(A.spill(width,carry),Nat.double(Nat.mul(wraps,A.modulus(width))))),Nat.add(next_value,Nat.mul(Nat.add(A.bit(carry),Nat.double(wraps)),A.modulus(width))),A.add_associative(next_value,A.spill(width,carry),Nat.double(Nat.mul(wraps,A.modulus(width)))),
                Equal.cong(Nat,Nat,v => Nat.add(next_value,v),Nat.add(A.spill(width,carry),Nat.double(Nat.mul(wraps,A.modulus(width)))),Nat.mul(Nat.add(A.bit(carry),Nat.double(wraps)),A.modulus(width)),Equal.sym(Nat,Nat.mul(Nat.add(A.bit(carry),Nat.double(wraps)),A.modulus(width)),Nat.add(A.spill(width,carry),Nat.double(Nat.mul(wraps,A.modulus(width)))),next_coefficient_product(width,carry,wraps)))))))}

law actual_quotient_bit_preserves_residue:
  for +q: V.Int64
  for +natural: Nat
  for +bit: Bool
  for residue: Residue<64n,A.unsigned(q),natural>
  Residue<64n,A.unsigned(B.insert(q,bit)),A.place(bit,natural)>
def actual_quotient_bit_preserves_residue(q,natural,bit,residue):
  bit_step_preserves_residue(64n,A.unsigned(q),natural,A.unsigned(B.insert(q,bit)),bit,I.negative(q),residue,B.actual_insert_natural(q,bit))
