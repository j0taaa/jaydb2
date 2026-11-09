# The actual shl+one-bit-add operation, including exact lost-bit accounting.
import Base
import ./Int64Proofs.bend as A
import ./Int64Shifts.bend as W
import ./Int64ShiftArithmetic.bend as T
import ./Int64.bend as I
import ./Value.bend as V
import ../proof/CodecSumsBits.bend as S
import ../proof/CodecWordsWord.bend as Words

law double_plus_bit_is_adder_input:
  for +bit: Bool
  for +value: Nat
  {A.place(bit,value) == Nat.add(value,Nat.add(value,A.bit(bit))) : Nat}
def double_plus_bit_is_adder_input(bit,value):
  match bit:
    case False{}:
      Equal.trans(Nat,Nat.double(value),Nat.add(value,value),Nat.add(value,Nat.add(value,0n)),T.double_is_self_sum(value),
        Equal.cong(Nat,Nat,v => Nat.add(value,v),value,Nat.add(value,0n),Equal.sym(Nat,Nat.add(value,0n),value,A.add_zero_right(value))))
    case True{}:
      Equal.trans(Nat,1n+Nat.double(value),1n+Nat.add(value,value),Nat.add(value,Nat.add(value,1n)),Equal.cong(Nat,Nat,v => 1n+v,Nat.double(value),Nat.add(value,value),T.double_is_self_sum(value)),
        Equal.trans(Nat,1n+Nat.add(value,value),Nat.add(value,1n+value),Nat.add(value,Nat.add(value,1n)),Equal.sym(Nat,Nat.add(value,1n+value),1n+Nat.add(value,value),A.add_right_successor(value,value)),
          Equal.cong(Nat,Nat,v => Nat.add(value,v),1n+value,Nat.add(value,1n),Equal.sym(Nat,Nat.add(value,1n),1n+value,A.add_commutative(value,1n)))))

law put_natural:
  for +n: Nat
  for +word: Word(1n+n)
  for +bit: Bool
  {A.place(bit,Word.to_nat(1n+n,word)) == Nat.add(Word.to_nat(1n+n,Word.shl.put(1n+n,bit,word)),A.spill(1n+n,A.top(1n+n,word))) : Nat}
def put_natural(n,word,bit):
  Equal.trans(Nat,A.place(bit,Word.to_nat(1n+n,word)),Nat.add(Word.to_nat(1n+n,word),Nat.add(Word.to_nat(1n+n,word),A.bit(bit))),Nat.add(Word.to_nat(1n+n,Word.shl.put(1n+n,bit,word)),A.spill(1n+n,A.top(1n+n,word))),double_plus_bit_is_adder_input(bit,Word.to_nat(1n+n,word)),
    Equal.trans(Nat,Nat.add(Word.to_nat(1n+n,word),Nat.add(Word.to_nat(1n+n,word),A.bit(bit))),Nat.add(Word.to_nat(1n+n,Word.adc(1n+n,word,word,False{},bit)),A.spill(1n+n,S.carry(1n+n,word,word,bit))),Nat.add(Word.to_nat(1n+n,Word.shl.put(1n+n,bit,word)),A.spill(1n+n,A.top(1n+n,word))),A.adc_natural(1n+n,word,word,bit),
      Equal.trans(Nat,Nat.add(Word.to_nat(1n+n,Word.adc(1n+n,word,word,False{},bit)),A.spill(1n+n,S.carry(1n+n,word,word,bit))),Nat.add(Word.to_nat(1n+n,Word.shl.put(1n+n,bit,word)),A.spill(1n+n,S.carry(1n+n,word,word,bit))),Nat.add(Word.to_nat(1n+n,Word.shl.put(1n+n,bit,word)),A.spill(1n+n,A.top(1n+n,word))),
        Equal.cong(Word(1n+n),Nat,w => Nat.add(Word.to_nat(1n+n,w),A.spill(1n+n,S.carry(1n+n,word,word,bit))),Word.adc(1n+n,word,word,False{},bit),Word.shl.put(1n+n,bit,word),T.double_adder_is_shift(1n+n,word,bit)),
        Equal.cong(Bool,Nat,c => Nat.add(Word.to_nat(1n+n,Word.shl.put(1n+n,bit,word)),A.spill(1n+n,c)),S.carry(1n+n,word,word,bit),A.top(1n+n,word),
          Equal.trans(Bool,S.carry(1n+n,word,word,bit),W.end_bit(1n+n,bit,word),A.top(1n+n,word),T.double_carry_is_end(1n+n,word,bit),W.end_bit_is_top(n,bit,word))))))

law shift_add_bit_is_put:
  for +n: Nat
  for +word: Word(1n+n)
  for +bit: Bool
  {Word.add(1n+n,Word.shl(1n+n,word),WCon{bit,Word.zero(n)}) == Word.shl.put(1n+n,bit,word) : Word(1n+n)}
def shift_add_bit_is_put(n,word,bit):
  match word bit:
    case WCon{+head,+tail} False{}:
      Equal.cong(Word(n),Word(1n+n),w => WCon{False{},w},Word.add(n,Word.shl.put(n,head,tail),Word.zero(n)),Word.shl.put(n,head,tail),Words.sum_zero_right(n,Word.shl.put(n,head,tail)))
    case WCon{+head,+tail} True{}:
      Equal.cong(Word(n),Word(1n+n),w => WCon{True{},w},Word.add(n,Word.shl.put(n,head,tail),Word.zero(n)),Word.shl.put(n,head,tail),Words.sum_zero_right(n,Word.shl.put(n,head,tail)))

def bit_word(bit: Bool) -> V.Int64:
  V.Int64{0,Bool.to_u32(bit)}

def insert(+number: V.Int64,bit: Bool) -> V.Int64:
  I.wrapping_add(I.shl(number),bit_word(bit))

law bit_word_bits:
  for +bit: Bool
  {A.bits(bit_word(bit)) == WCon{bit,Word.zero(63n)} : Word(64n)}
def bit_word_bits(bit):
  match bit:
    case False{}: {==}
    case True{}: {==}

law actual_insert_is_word_put:
  for +number: V.Int64
  for +bit: Bool
  {A.bits(insert(number,bit)) == Word.shl.put(64n,bit,A.bits(number)) : Word(64n)}
def actual_insert_is_word_put(number,bit):
  Equal.trans(Word(64n),A.bits(insert(number,bit)),Word.add(64n,A.bits(I.shl(number)),A.bits(bit_word(bit))),Word.shl.put(64n,bit,A.bits(number)),A.wrapping_add_is_full_word_add(I.shl(number),bit_word(bit)),
    Equal.trans(Word(64n),Word.add(64n,A.bits(I.shl(number)),A.bits(bit_word(bit))),Word.add(64n,Word.shl(64n,A.bits(number)),A.bits(bit_word(bit))),Word.shl.put(64n,bit,A.bits(number)),
      Equal.cong(Word(64n),Word(64n),w => Word.add(64n,w,A.bits(bit_word(bit))),A.bits(I.shl(number)),Word.shl(64n,A.bits(number)),W.shl_is_full_word_shift(number)),
      Equal.trans(Word(64n),Word.add(64n,Word.shl(64n,A.bits(number)),A.bits(bit_word(bit))),Word.add(64n,Word.shl(64n,A.bits(number)),WCon{bit,Word.zero(63n)}),Word.shl.put(64n,bit,A.bits(number)),
        Equal.cong(Word(64n),Word(64n),w => Word.add(64n,Word.shl(64n,A.bits(number)),w),A.bits(bit_word(bit)),WCon{bit,Word.zero(63n)},bit_word_bits(bit)),shift_add_bit_is_put(63n,A.bits(number),bit))))

law actual_insert_natural:
  for +number: V.Int64
  for +bit: Bool
  {A.place(bit,A.unsigned(number)) == Nat.add(A.unsigned(insert(number,bit)),A.spill(64n,I.negative(number))) : Nat}
def actual_insert_natural(number,bit):
  Equal.trans(Nat,A.place(bit,A.unsigned(number)),Nat.add(Word.to_nat(64n,Word.shl.put(64n,bit,A.bits(number))),A.spill(64n,A.top(64n,A.bits(number)))),Nat.add(A.unsigned(insert(number,bit)),A.spill(64n,I.negative(number))),put_natural(63n,A.bits(number),bit),
    Equal.trans(Nat,Nat.add(Word.to_nat(64n,Word.shl.put(64n,bit,A.bits(number))),A.spill(64n,A.top(64n,A.bits(number)))),Nat.add(A.unsigned(insert(number,bit)),A.spill(64n,A.top(64n,A.bits(number)))),Nat.add(A.unsigned(insert(number,bit)),A.spill(64n,I.negative(number))),
      Equal.cong(Word(64n),Nat,w => Nat.add(Word.to_nat(64n,w),A.spill(64n,A.top(64n,A.bits(number)))),Word.shl.put(64n,bit,A.bits(number)),A.bits(insert(number,bit)),Equal.sym(Word(64n),A.bits(insert(number,bit)),Word.shl.put(64n,bit,A.bits(number)),actual_insert_is_word_put(number,bit))),
      Equal.cong(Bool,Nat,b => Nat.add(A.unsigned(insert(number,bit)),A.spill(64n,b)),A.top(64n,A.bits(number)),I.negative(number),Equal.sym(Bool,I.negative(number),A.top(64n,A.bits(number)),A.negative_is_sign_bit(number)))))

law actual_insert_without_loss:
  for +number: V.Int64
  for +bit: Bool
  for clear: {I.negative(number) == False{} : Bool}
  {A.unsigned(insert(number,bit)) == A.place(bit,A.unsigned(number)) : Nat}
def actual_insert_without_loss(number,bit,clear):
  Equal.sym(Nat,A.place(bit,A.unsigned(number)),A.unsigned(insert(number,bit)),
    Equal.trans(Nat,A.place(bit,A.unsigned(number)),Nat.add(A.unsigned(insert(number,bit)),A.spill(64n,I.negative(number))),A.unsigned(insert(number,bit)),actual_insert_natural(number,bit),
      Equal.trans(Nat,Nat.add(A.unsigned(insert(number,bit)),A.spill(64n,I.negative(number))),Nat.add(A.unsigned(insert(number,bit)),0n),A.unsigned(insert(number,bit)),
        Equal.cong(Bool,Nat,b => Nat.add(A.unsigned(insert(number,bit)),A.spill(64n,b)),I.negative(number),False{},clear),A.add_zero_right(A.unsigned(insert(number,bit))))))

law shift_add_bit_has_no_addition_carry:
  for +n: Nat
  for +word: Word(1n+n)
  for +bit: Bool
  {S.carry(1n+n,Word.shl(1n+n,word),WCon{bit,Word.zero(n)},False{}) == False{} : Bool}
def shift_add_bit_has_no_addition_carry(n,word,bit):
  match word bit:
    case WCon{+head,+tail} False{}: S.carry_zero(n,Word.shl.put(n,head,tail))
    case WCon{+head,+tail} True{}: S.carry_zero(n,Word.shl.put(n,head,tail))
