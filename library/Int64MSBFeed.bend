# Reading every most-significant bit through the actual word left shift recovers
# the independent unbounded natural value of the original word.
import Base
import ./Int64RadixScale.bend as R
import ./Int64Proofs.bend as A
import ./Int64Shifts.bend as W
import ./Int64ShiftArithmetic.bend as T

def shifts(steps: Nat,+width: Nat,word: Word(width)) -> Word(width):
  match steps:
    case 0n: word
    case 1n+p: shifts(p,width,Word.shl(width,word))

law shifts_preserve_low_zero:
  for +steps: Nat
  for +n: Nat
  for +word: Word(n)
  {shifts(steps,1n+n,WCon{False{},word}) == WCon{False{},shifts(steps,n,word)} : Word(1n+n)}
def shifts_preserve_low_zero(steps,n,word):
  match steps:
    case 0n: {==}
    case 1n+p:
      %W.shift_is_put_zero(n,word) :
        {shifts(p,1n+n,WCon{False{},_}) == WCon{False{},shifts(p,n,Word.shl(n,word))} : Word(1n+n)}
      shifts_preserve_low_zero(p,n,Word.shl(n,word))

law width_left_shifts_exhaust_word:
  for +n: Nat
  for +word: Word(n)
  {shifts(n,n,word) == Word.zero(n) : Word(n)}
def width_left_shifts_exhaust_word(n,word):
  match n:
    case 0n:
      match word:
        case WNil{}: {==}
    case 1n+p:
      match word:
        case WCon{+bit,+tail}:
          Equal.trans(Word(1n+p),shifts(p,1n+p,WCon{False{},Word.shl.put(p,bit,tail)}),WCon{False{},shifts(p,p,Word.shl.put(p,bit,tail))},Word.zero(1n+p),
            shifts_preserve_low_zero(p,p,Word.shl.put(p,bit,tail)),
            Equal.cong(Word(p),Word(1n+p),w => WCon{False{},w},shifts(p,p,Word.shl.put(p,bit,tail)),Word.zero(p),width_left_shifts_exhaust_word(p,Word.shl.put(p,bit,tail))))

law word_zero_has_zero_measure:
  for +n: Nat
  {Word.to_nat(n,Word.zero(n)) == 0n : Nat}
def word_zero_has_zero_measure(n):
  match n:
    case 0n: {==}
    case 1n+p:
      Equal.cong(Nat,Nat,Nat.double,Word.to_nat(p,Word.zero(p)),0n,word_zero_has_zero_measure(p))

def feed(steps: Nat,+width: Nat,+word: Word(width),prefix: Nat) -> Nat:
  match steps:
    case 0n: prefix
    case 1n+p: feed(p,width,Word.shl(width,word),A.place(A.top(width,word),prefix))

law weighted_shift_step:
  for +width: Nat
  for +word: Word(width)
  for +prefix: Nat
  {Nat.double(Nat.add(Word.to_nat(width,word),Nat.mul(prefix,A.modulus(width)))) ==
    Nat.add(Word.to_nat(width,Word.shl(width,word)),Nat.mul(A.place(A.top(width,word),prefix),A.modulus(width))) : Nat}
def weighted_shift_step(width,word,prefix):
  Equal.trans(Nat,Nat.double(Nat.add(Word.to_nat(width,word),Nat.mul(prefix,A.modulus(width)))),Nat.add(Nat.double(Word.to_nat(width,word)),Nat.double(Nat.mul(prefix,A.modulus(width)))),Nat.add(Word.to_nat(width,Word.shl(width,word)),Nat.mul(A.place(A.top(width,word),prefix),A.modulus(width))),A.double_sum(Word.to_nat(width,word),Nat.mul(prefix,A.modulus(width))),
    Equal.trans(Nat,Nat.add(Nat.double(Word.to_nat(width,word)),Nat.double(Nat.mul(prefix,A.modulus(width)))),Nat.add(Nat.add(Word.to_nat(width,Word.shl(width,word)),A.spill(width,A.top(width,word))),Nat.double(Nat.mul(prefix,A.modulus(width)))),Nat.add(Word.to_nat(width,Word.shl(width,word)),Nat.mul(A.place(A.top(width,word),prefix),A.modulus(width))),
      Equal.cong(Nat,Nat,v => Nat.add(v,Nat.double(Nat.mul(prefix,A.modulus(width)))),Nat.double(Word.to_nat(width,word)),Nat.add(Word.to_nat(width,Word.shl(width,word)),A.spill(width,A.top(width,word))),T.shift_word_natural(width,word)),
      Equal.trans(Nat,Nat.add(Nat.add(Word.to_nat(width,Word.shl(width,word)),A.spill(width,A.top(width,word))),Nat.double(Nat.mul(prefix,A.modulus(width)))),Nat.add(Word.to_nat(width,Word.shl(width,word)),Nat.add(A.spill(width,A.top(width,word)),Nat.double(Nat.mul(prefix,A.modulus(width))))),Nat.add(Word.to_nat(width,Word.shl(width,word)),Nat.mul(A.place(A.top(width,word),prefix),A.modulus(width))),
        A.add_associative(Word.to_nat(width,Word.shl(width,word)),A.spill(width,A.top(width,word)),Nat.double(Nat.mul(prefix,A.modulus(width)))),
        Equal.cong(Nat,Nat,v => Nat.add(Word.to_nat(width,Word.shl(width,word)),v),Nat.add(A.spill(width,A.top(width,word)),Nat.double(Nat.mul(prefix,A.modulus(width)))),Nat.mul(A.place(A.top(width,word),prefix),A.modulus(width)),Equal.sym(Nat,Nat.mul(A.place(A.top(width,word),prefix),A.modulus(width)),Nat.add(A.spill(width,A.top(width,word)),Nat.double(Nat.mul(prefix,A.modulus(width)))),R.placed_prefix_product(width,A.top(width,word),prefix))))))

law weighted_feed_invariant:
  for +steps: Nat
  for +width: Nat
  for +word: Word(width)
  for +prefix: Nat
  {R.scale(steps,Nat.add(Word.to_nat(width,word),Nat.mul(prefix,A.modulus(width)))) ==
    Nat.add(Word.to_nat(width,shifts(steps,width,word)),Nat.mul(feed(steps,width,word,prefix),A.modulus(width))) : Nat}
def weighted_feed_invariant(steps,width,word,prefix):
  match steps:
    case 0n: {==}
    case 1n+p:
      Equal.trans(Nat,R.scale(p,Nat.double(Nat.add(Word.to_nat(width,word),Nat.mul(prefix,A.modulus(width))))),
        R.scale(p,Nat.add(Word.to_nat(width,Word.shl(width,word)),Nat.mul(A.place(A.top(width,word),prefix),A.modulus(width)))),
        Nat.add(Word.to_nat(width,shifts(p,width,Word.shl(width,word))),Nat.mul(feed(p,width,Word.shl(width,word),A.place(A.top(width,word),prefix)),A.modulus(width))),
        Equal.cong(Nat,Nat,v => R.scale(p,v),Nat.double(Nat.add(Word.to_nat(width,word),Nat.mul(prefix,A.modulus(width)))),Nat.add(Word.to_nat(width,Word.shl(width,word)),Nat.mul(A.place(A.top(width,word),prefix),A.modulus(width))),weighted_shift_step(width,word,prefix)),
        weighted_feed_invariant(p,width,Word.shl(width,word),A.place(A.top(width,word),prefix)))
