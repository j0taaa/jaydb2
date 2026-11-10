# General mathematical interpretation of sign-bit-flipped word comparison.
# This is induction over arbitrary widths, without a closed unary 2^64 value.
import Base
import ./Int64Proofs.bend as A
import ./Int64NaturalOrder.bend as Natural

def flip_sign(width: Nat,word: Word(width)) -> Word(width):
  match width:
    case 0n: WNil{}
    case 1n+p:
      match p word:
        case 0n WCon{bit,WNil{}}: WCon{Bool.not(bit),WNil{}}
        case 1n+rest WCon{bit,tail}: WCon{bit,flip_sign(1n+rest,tail)}

def cross_left(+width: Nat,a: Word(width),+b: Word(width)) -> Nat:
  Nat.add(Word.to_nat(width,a),A.spill(width,A.top(width,b)))

law word_constructor_has_the_expected_natural_value:
  for +width: Nat
  for +bit: Bool
  for +word: Word(width)
  {Word.to_nat(1n+width,WCon{bit,word}) == A.place(bit,Word.to_nat(width,word)) : Nat}
def word_constructor_has_the_expected_natural_value(width,bit,word):
  match bit:
    case False{}: {==}
    case True{}: {==}

law cross_sum_ignores_other_low_bit:
  for +width: Nat
  for +bit: Bool
  for +other_bit: Bool
  for +word: Word(1n+width)
  for +other: Word(1n+width)
  {cross_left(2n+width,WCon{bit,word},WCon{other_bit,other}) == A.place(bit,cross_left(1n+width,word,other)) : Nat}
def cross_sum_ignores_other_low_bit(width,bit,other_bit,word,other):
  Equal.trans(Nat,cross_left(2n+width,WCon{bit,word},WCon{other_bit,other}),Nat.add(A.place(bit,Word.to_nat(1n+width,word)),A.spill(2n+width,A.top(1n+width,other))),A.place(bit,cross_left(1n+width,word,other)),
    Equal.cong(Nat,Nat,value => Nat.add(value,A.spill(2n+width,A.top(1n+width,other))),Word.to_nat(2n+width,WCon{bit,word}),A.place(bit,Word.to_nat(1n+width,word)),word_constructor_has_the_expected_natural_value(1n+width,bit,word)),
    Equal.sym(Nat,A.place(bit,cross_left(1n+width,word,other)),Nat.add(A.place(bit,Word.to_nat(1n+width,word)),A.spill(2n+width,A.top(1n+width,other))),A.place_spill(1n+width,bit,Word.to_nat(1n+width,word),A.top(1n+width,other))))

law flipped_comparison_is_signed_cross_sum_comparison:
  for +width: Nat
  for +a: Word(width)
  for +b: Word(width)
  {Nat.cmp(cross_left(width,a,b),cross_left(width,b,a)) == Word.cmp(width,flip_sign(width,a),flip_sign(width,b)) : Cmp}
def flipped_comparison_is_signed_cross_sum_comparison(width,a,b):
  match width:
    case 0n: {==}
    case 1n+p:
      match p a b:
        case 0n WCon{False{},WNil{}} WCon{False{},WNil{}}: {==}
        case 0n WCon{False{},WNil{}} WCon{True{},WNil{}}: {==}
        case 0n WCon{True{},WNil{}} WCon{False{},WNil{}}: {==}
        case 0n WCon{True{},WNil{}} WCon{True{},WNil{}}: {==}
        case 1n+n WCon{+ab,+at} WCon{+bb,+bt}:
          Equal.trans(Cmp,Nat.cmp(cross_left(2n+n,WCon{ab,at},WCon{bb,bt}),cross_left(2n+n,WCon{bb,bt},WCon{ab,at})),Nat.cmp(A.place(ab,cross_left(1n+n,at,bt)),A.place(bb,cross_left(1n+n,bt,at))),Word.cmp(2n+n,flip_sign(2n+n,WCon{ab,at}),flip_sign(2n+n,WCon{bb,bt})),
            Equal.trans(Cmp,Nat.cmp(cross_left(2n+n,WCon{ab,at},WCon{bb,bt}),cross_left(2n+n,WCon{bb,bt},WCon{ab,at})),Nat.cmp(A.place(ab,cross_left(1n+n,at,bt)),cross_left(2n+n,WCon{bb,bt},WCon{ab,at})),Nat.cmp(A.place(ab,cross_left(1n+n,at,bt)),A.place(bb,cross_left(1n+n,bt,at))),
              Equal.cong(Nat,Cmp,x => Nat.cmp(x,cross_left(2n+n,WCon{bb,bt},WCon{ab,at})),cross_left(2n+n,WCon{ab,at},WCon{bb,bt}),A.place(ab,cross_left(1n+n,at,bt)),cross_sum_ignores_other_low_bit(n,ab,bb,at,bt)),
              Equal.cong(Nat,Cmp,y => Nat.cmp(A.place(ab,cross_left(1n+n,at,bt)),y),cross_left(2n+n,WCon{bb,bt},WCon{ab,at}),A.place(bb,cross_left(1n+n,bt,at)),cross_sum_ignores_other_low_bit(n,bb,ab,bt,at))),
            Equal.trans(Cmp,Nat.cmp(A.place(ab,cross_left(1n+n,at,bt)),A.place(bb,cross_left(1n+n,bt,at))),Word.cmp.fin(ab,bb,Nat.cmp(cross_left(1n+n,at,bt),cross_left(1n+n,bt,at))),Word.cmp.fin(ab,bb,Word.cmp(1n+n,flip_sign(1n+n,at),flip_sign(1n+n,bt))),
              Natural.binary_compare(ab,bb,cross_left(1n+n,at,bt),cross_left(1n+n,bt,at)),
              Equal.cong(Cmp,Cmp,c => Word.cmp.fin(ab,bb,c),Nat.cmp(cross_left(1n+n,at,bt),cross_left(1n+n,bt,at)),Word.cmp(1n+n,flip_sign(1n+n,at),flip_sign(1n+n,bt)),flipped_comparison_is_signed_cross_sum_comparison(1n+n,at,bt))))

law flip_sign_is_xor_threshold:
  for +width: Nat
  for +word: Word(1n+width)
  {flip_sign(1n+width,word) == Word.xor(1n+width,word,A.sign_threshold(width)) : Word(1n+width)}
def flip_sign_is_xor_threshold(width,word):
  match width word:
    case 0n WCon{False{},WNil{}}: {==}
    case 0n WCon{True{},WNil{}}: {==}
    case 1n+p WCon{False{},+tail}:
      Equal.cong(Word(1n+p),Word(2n+p),t => WCon{False{},t},flip_sign(1n+p,tail),Word.xor(1n+p,tail,A.sign_threshold(p)),flip_sign_is_xor_threshold(p,tail))
    case 1n+p WCon{True{},+tail}:
      Equal.cong(Word(1n+p),Word(2n+p),t => WCon{True{},t},flip_sign(1n+p,tail),Word.xor(1n+p,tail,A.sign_threshold(p)),flip_sign_is_xor_threshold(p,tail))
