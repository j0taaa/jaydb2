# Every actual input bit consumed by the restoring loop is accounted for.
import Base
import ./Int64MSBFeed.bend as F
import ./Int64RadixScale.bend as R
import ./Int64Proofs.bend as A
import ./Int64Shifts.bend as W
import ./Int64.bend as I
import ./Value.bend as V

law full_word_feed_is_value:
  for +n: Nat
  for +word: Word(n)
  {F.feed(n,n,word,0n) == Word.to_nat(n,word) : Nat}
def full_word_feed_is_value(n,word):
  Equal.sym(Nat,Word.to_nat(n,word),F.feed(n,n,word,0n),R.scaling_is_injective(n,Word.to_nat(n,word),F.feed(n,n,word,0n),
    Equal.trans(Nat,R.scale(n,Word.to_nat(n,word)),R.scale(n,Nat.add(Word.to_nat(n,word),0n)),R.scale(n,F.feed(n,n,word,0n)),
      Equal.cong(Nat,Nat,v => R.scale(n,v),Word.to_nat(n,word),Nat.add(Word.to_nat(n,word),0n),Equal.sym(Nat,Nat.add(Word.to_nat(n,word),0n),Word.to_nat(n,word),A.add_zero_right(Word.to_nat(n,word)))),
      Equal.trans(Nat,R.scale(n,Nat.add(Word.to_nat(n,word),0n)),Nat.add(Word.to_nat(n,F.shifts(n,n,word)),Nat.mul(F.feed(n,n,word,0n),A.modulus(n))),R.scale(n,F.feed(n,n,word,0n)),F.weighted_feed_invariant(n,n,word,0n),
        Equal.trans(Nat,Nat.add(Word.to_nat(n,F.shifts(n,n,word)),Nat.mul(F.feed(n,n,word,0n),A.modulus(n))),Nat.mul(F.feed(n,n,word,0n),A.modulus(n)),R.scale(n,F.feed(n,n,word,0n)),
          Equal.cong(Nat,Nat,v => Nat.add(v,Nat.mul(F.feed(n,n,word,0n),A.modulus(n))),Word.to_nat(n,F.shifts(n,n,word)),0n,
            Equal.trans(Nat,Word.to_nat(n,F.shifts(n,n,word)),Word.to_nat(n,Word.zero(n)),0n,Equal.cong(Word(n),Nat,w => Word.to_nat(n,w),F.shifts(n,n,word),Word.zero(n),F.width_left_shifts_exhaust_word(n,word)),F.word_zero_has_zero_measure(n))),
          Equal.sym(Nat,R.scale(n,F.feed(n,n,word,0n)),Nat.mul(F.feed(n,n,word,0n),A.modulus(n)),R.scaling_is_radix_multiplication(n,F.feed(n,n,word,0n))))))))

def actual_feed(steps: Nat,+input: V.Int64,prefix: Nat) -> Nat:
  match steps:
    case 0n: prefix
    case 1n+p: actual_feed(p,I.shl(input),A.place(I.negative(input),prefix))

law actual_feed_is_word_feed:
  for +steps: Nat
  for +input: V.Int64
  for +prefix: Nat
  {actual_feed(steps,input,prefix) == F.feed(steps,64n,A.bits(input),prefix) : Nat}
def actual_feed_is_word_feed(steps,input,prefix):
  match steps:
    case 0n: {==}
    case 1n+p:
      Equal.trans(Nat,actual_feed(p,I.shl(input),A.place(I.negative(input),prefix)),F.feed(p,64n,A.bits(I.shl(input)),A.place(I.negative(input),prefix)),F.feed(1n+p,64n,A.bits(input),prefix),actual_feed_is_word_feed(p,I.shl(input),A.place(I.negative(input),prefix)),
        Equal.trans(Nat,F.feed(p,64n,A.bits(I.shl(input)),A.place(I.negative(input),prefix)),F.feed(p,64n,Word.shl(64n,A.bits(input)),A.place(I.negative(input),prefix)),F.feed(1n+p,64n,A.bits(input),prefix),
          Equal.cong(Word(64n),Nat,w => F.feed(p,64n,w,A.place(I.negative(input),prefix)),A.bits(I.shl(input)),Word.shl(64n,A.bits(input)),W.shl_is_full_word_shift(input)),
          Equal.cong(Bool,Nat,b => F.feed(p,64n,Word.shl(64n,A.bits(input)),A.place(b,prefix)),I.negative(input),A.top(64n,A.bits(input)),A.negative_is_sign_bit(input))))

law sixty_four_actual_input_bits_recover_value:
  for +input: V.Int64
  {actual_feed(64n,input,0n) == A.unsigned(input) : Nat}
def sixty_four_actual_input_bits_recover_value(input):
  Equal.trans(Nat,actual_feed(64n,input,0n),F.feed(64n,64n,A.bits(input),0n),A.unsigned(input),actual_feed_is_word_feed(64n,input,0n),full_word_feed_is_value(64n,A.bits(input)))
