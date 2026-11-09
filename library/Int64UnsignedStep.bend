# Each actual shift-and-add step either preserves its mathematical total or
# constructs a whole-radix excess, which no 64-bit unsigned value can equal.
import Base
import ./Int64NatProduct.bend as P
import ./Int64Flags.bend as G
import ./Int64ShiftArithmetic.bend as T
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A
import ../contract/Logic.bend as L
import ../proof/Foundations.bend as F
import ../proof/CodecSumsBits.bend as S

def total(+a: V.Int64, +b: V.Int64, accumulator: V.Int64) -> Nat:
  Nat.add(A.unsigned(accumulator),Nat.mul(A.unsigned(b),A.unsigned(a)))

def selected_value(odd: Bool, +a: V.Int64, +accumulator: V.Int64) -> Nat:
  Bool.pick(Nat,odd,Nat.add(A.unsigned(accumulator),A.unsigned(a)),A.unsigned(accumulator))

def expanded(+odd: Bool, +a: V.Int64, +b: V.Int64, +accumulator: V.Int64) -> Nat:
  Nat.add(selected_value(odd,a,accumulator),Nat.mul(A.unsigned(I.shr(b)),Nat.double(A.unsigned(a))))

def selected_word(odd: Bool, +a: V.Int64, +accumulator: V.Int64) -> V.Int64:
  Bool.pick(V.Int64,odd,I.wrapping_add(accumulator,a),accumulator)

def next_total(+odd: Bool, +a: V.Int64, +b: V.Int64, +accumulator: V.Int64) -> Nat:
  total(I.shl(a),I.shr(b),selected_word(odd,a,accumulator))

type Beyond<-width: Nat,-value: Nat> is Type:
  Beyond{excess: Nat,exact: {value == Nat.add(excess,A.modulus(width)) : Nat}}

law excess_excludes_every_word:
  for +value: Nat
  for +r: V.Int64
  for beyond: Beyond<64n,value>
  for same: {A.unsigned(r) == value : Nat}
  Empty
def excess_excludes_every_word(value,r,beyond,same):
  match beyond:
    case Beyond{+excess,exact}:
      F.false_negative_true(A.contradict_radix_gap(64n,A.unsigned(r),excess,A.word_value_is_bounded(64n,A.bits(r)),
        Equal.trans(Nat,A.unsigned(r),value,Nat.add(excess,A.modulus(64n)),same,exact)))

law current_is_binary_expansion:
  for +a: V.Int64
  for +b: V.Int64
  for +accumulator: V.Int64
  for +odd: Bool
  for parity: {I.odd(b) == odd : Bool}
  {total(a,b,accumulator) == expanded(odd,a,b,accumulator) : Nat}
def current_is_binary_expansion(a,b,accumulator,odd,parity):
  Equal.trans(Nat,total(a,b,accumulator),
    Nat.add(A.unsigned(accumulator),Nat.mul(A.place(odd,A.unsigned(I.shr(b))),A.unsigned(a))),expanded(odd,a,b,accumulator),
    Equal.cong(Nat,Nat,n => Nat.add(A.unsigned(accumulator),Nat.mul(n,A.unsigned(a))),A.unsigned(b),A.place(odd,A.unsigned(I.shr(b))),
      Equal.trans(Nat,A.unsigned(b),A.place(I.odd(b),A.unsigned(I.shr(b))),A.place(odd,A.unsigned(I.shr(b))),G.right_shift_natural(b),
        Equal.cong(Bool,Nat,o => A.place(o,A.unsigned(I.shr(b))),I.odd(b),odd,parity))),
    P.binary_product_step(odd,A.unsigned(a),A.unsigned(I.shr(b)),A.unsigned(accumulator)))

law exact_add_with_carry:
  for +accumulator: V.Int64
  for +a: V.Int64
  for +carry: Bool
  for carried: {I.unsigned_lt(I.wrapping_add(accumulator,a),accumulator) == carry : Bool}
  {Nat.add(A.unsigned(accumulator),A.unsigned(a)) == Nat.add(A.unsigned(I.wrapping_add(accumulator,a)),A.spill(64n,carry)) : Nat}
def exact_add_with_carry(accumulator,a,carry,carried):
  Equal.trans(Nat,Nat.add(A.unsigned(accumulator),A.unsigned(a)),
    Nat.add(A.unsigned(I.wrapping_add(accumulator,a)),A.spill(64n,S.carry(64n,A.bits(accumulator),A.bits(a),False{}))),
    Nat.add(A.unsigned(I.wrapping_add(accumulator,a)),A.spill(64n,carry)),A.wrapping_add_natural(accumulator,a),
    Equal.cong(Bool,Nat,c => Nat.add(A.unsigned(I.wrapping_add(accumulator,a)),A.spill(64n,c)),S.carry(64n,A.bits(accumulator),A.bits(a),False{}),carry,
      Equal.trans(Bool,S.carry(64n,A.bits(accumulator),A.bits(a),False{}),I.unsigned_lt(I.wrapping_add(accumulator,a),accumulator),carry,
        Equal.sym(Bool,I.unsigned_lt(I.wrapping_add(accumulator,a),accumulator),S.carry(64n,A.bits(accumulator),A.bits(a),False{}),G.unsigned_add_carry_is_guard(accumulator,a)),carried)))

law safe_selected_word:
  for +odd: Bool
  for +carry: Bool
  for +a: V.Int64
  for +accumulator: V.Int64
  for carried: {I.unsigned_lt(I.wrapping_add(accumulator,a),accumulator) == carry : Bool}
  for safe: {odd && carry == False{} : Bool}
  {A.unsigned(selected_word(odd,a,accumulator)) == selected_value(odd,a,accumulator) : Nat}
def safe_selected_word(odd,carry,a,accumulator,carried,safe):
  match odd carry:
    case False{} _: {==}
    case True{} False{}:
      Equal.sym(Nat,Nat.add(A.unsigned(accumulator),A.unsigned(a)),A.unsigned(I.wrapping_add(accumulator,a)),
        Equal.trans(Nat,Nat.add(A.unsigned(accumulator),A.unsigned(a)),Nat.add(A.unsigned(I.wrapping_add(accumulator,a)),0n),A.unsigned(I.wrapping_add(accumulator,a)),exact_add_with_carry(accumulator,a,False{},carried),A.add_zero_right(A.unsigned(I.wrapping_add(accumulator,a)))))
    case True{} True{}:
      F.absurd_boolean({A.unsigned(I.wrapping_add(accumulator,a)) == Nat.add(A.unsigned(accumulator),A.unsigned(a)) : Nat},Equal.sym(Bool,True{},False{},safe))

law safe_shift_product:
  for +high: Bool
  for +zero: Bool
  for +a: V.Int64
  for +b: V.Int64
  for high_bit: {I.negative(a) == high : Bool}
  for is_zero: {I.zero(I.shr(b)) == zero : Bool}
  for safe: {high && Bool.not(zero) == False{} : Bool}
  {Nat.mul(A.unsigned(I.shr(b)),Nat.double(A.unsigned(a))) == Nat.mul(A.unsigned(I.shr(b)),A.unsigned(I.shl(a))) : Nat}
def safe_shift_product(high,zero,a,b,high_bit,is_zero,safe):
  match high zero:
    case False{} _:
      Equal.cong(Nat,Nat,n => Nat.mul(A.unsigned(I.shr(b)),n),Nat.double(A.unsigned(a)),A.unsigned(I.shl(a)),
        Equal.trans(Nat,Nat.double(A.unsigned(a)),Nat.add(A.unsigned(I.shl(a)),A.spill(64n,I.negative(a))),A.unsigned(I.shl(a)),T.actual_left_shift_natural(a),
          Equal.trans(Nat,Nat.add(A.unsigned(I.shl(a)),A.spill(64n,I.negative(a))),Nat.add(A.unsigned(I.shl(a)),0n),A.unsigned(I.shl(a)),
            Equal.cong(Bool,Nat,h => Nat.add(A.unsigned(I.shl(a)),A.spill(64n,h)),I.negative(a),False{},high_bit),A.add_zero_right(A.unsigned(I.shl(a))))))
    case True{} True{}:
      %Equal.sym(V.Int64,I.shr(b),V.Int64{0,0},G.zero_guard_is_sound(I.shr(b),is_zero)) :
        {Nat.mul(A.unsigned(_),Nat.double(A.unsigned(a))) == Nat.mul(A.unsigned(_),A.unsigned(I.shl(a))) : Nat}
      {==}
    case True{} False{}:
      F.absurd_boolean({Nat.mul(A.unsigned(I.shr(b)),Nat.double(A.unsigned(a))) == Nat.mul(A.unsigned(I.shr(b)),A.unsigned(I.shl(a))) : Nat},Equal.sym(Bool,True{},False{},safe))

law safe_step:
  for +odd: Bool
  for +carry: Bool
  for +high: Bool
  for +zero: Bool
  for +a: V.Int64
  for +b: V.Int64
  for +accumulator: V.Int64
  for parity: {I.odd(b) == odd : Bool}
  for carried: {I.unsigned_lt(I.wrapping_add(accumulator,a),accumulator) == carry : Bool}
  for high_bit: {I.negative(a) == high : Bool}
  for is_zero: {I.zero(I.shr(b)) == zero : Bool}
  for safe_add: {odd && carry == False{} : Bool}
  for safe_shift: {high && Bool.not(zero) == False{} : Bool}
  {total(a,b,accumulator) == next_total(odd,a,b,accumulator) : Nat}
def safe_step(odd,carry,high,zero,a,b,accumulator,parity,carried,high_bit,is_zero,safe_add,safe_shift):
  Equal.trans(Nat,total(a,b,accumulator),expanded(odd,a,b,accumulator),next_total(odd,a,b,accumulator),current_is_binary_expansion(a,b,accumulator,odd,parity),
    Equal.trans(Nat,expanded(odd,a,b,accumulator),Nat.add(A.unsigned(selected_word(odd,a,accumulator)),Nat.mul(A.unsigned(I.shr(b)),Nat.double(A.unsigned(a)))),next_total(odd,a,b,accumulator),
      Equal.cong(Nat,Nat,n => Nat.add(n,Nat.mul(A.unsigned(I.shr(b)),Nat.double(A.unsigned(a)))),selected_value(odd,a,accumulator),A.unsigned(selected_word(odd,a,accumulator)),
        Equal.sym(Nat,A.unsigned(selected_word(odd,a,accumulator)),selected_value(odd,a,accumulator),safe_selected_word(odd,carry,a,accumulator,carried,safe_add))),
      Equal.cong(Nat,Nat,n => Nat.add(A.unsigned(selected_word(odd,a,accumulator)),n),Nat.mul(A.unsigned(I.shr(b)),Nat.double(A.unsigned(a))),Nat.mul(A.unsigned(I.shr(b)),A.unsigned(I.shl(a))),safe_shift_product(high,zero,a,b,high_bit,is_zero,safe_shift))))

# Keep the radix symbolic through algebraic helper boundaries; no huge unary
# literal is ever evaluated by this proof or by the executable program.
law move_radix_middle:
  for +width: Nat
  for +a: Nat
  for +b: Nat
  {Nat.add(Nat.add(a,A.modulus(width)),b) == Nat.add(Nat.add(a,b),A.modulus(width)) : Nat}
def move_radix_middle(width,a,b):
  Equal.trans(Nat,Nat.add(Nat.add(a,A.modulus(width)),b),Nat.add(a,Nat.add(A.modulus(width),b)),Nat.add(Nat.add(a,b),A.modulus(width)),A.add_associative(a,A.modulus(width),b),
    Equal.trans(Nat,Nat.add(a,Nat.add(A.modulus(width),b)),Nat.add(a,Nat.add(b,A.modulus(width))),Nat.add(Nat.add(a,b),A.modulus(width)),
      Equal.cong(Nat,Nat,n => Nat.add(a,n),Nat.add(A.modulus(width),b),Nat.add(b,A.modulus(width)),A.add_commutative(A.modulus(width),b)),
      Equal.sym(Nat,Nat.add(Nat.add(a,b),A.modulus(width)),Nat.add(a,Nat.add(b,A.modulus(width))),A.add_associative(a,b,A.modulus(width)))))


# Radix evidence stays indexed by symbolic width even at the 64-bit boundary.
law carried_sum_is_beyond:
  for +width: Nat
  for +x: Nat
  for +y: Nat
  for +residue: Nat
  for +carry: Bool
  for truth: {carry == True{} : Bool}
  for exact: {Nat.add(x,y) == Nat.add(residue,A.spill(width,carry)) : Nat}
  Beyond<width,Nat.add(x,y)>
def carried_sum_is_beyond(width,x,y,residue,carry,truth,exact):
  match carry:
    case False{}: F.absurd_boolean(Beyond<width,Nat.add(x,y)>,truth)
    case True{}: Beyond{residue,exact}

law beyond_append:
  for +width: Nat
  for +value: Nat
  for +tail: Nat
  for beyond: Beyond<width,value>
  Beyond<width,Nat.add(value,tail)>
def beyond_append(width,value,tail,beyond):
  match beyond:
    case Beyond{+excess,exact}:
      Beyond{Nat.add(excess,tail),Equal.trans(Nat,Nat.add(value,tail),Nat.add(Nat.add(excess,A.modulus(width)),tail),Nat.add(Nat.add(excess,tail),A.modulus(width)),
        Equal.cong(Nat,Nat,n => Nat.add(n,tail),value,Nat.add(excess,A.modulus(width)),exact),move_radix_middle(width,excess,tail))}

law beyond_prepend:
  for +width: Nat
  for +value: Nat
  for +head: Nat
  for beyond: Beyond<width,value>
  Beyond<width,Nat.add(head,value)>
def beyond_prepend(width,value,head,beyond):
  match beyond:
    case Beyond{+excess,exact}:
      Beyond{Nat.add(head,excess),Equal.trans(Nat,Nat.add(head,value),Nat.add(head,Nat.add(excess,A.modulus(width))),Nat.add(Nat.add(head,excess),A.modulus(width)),
        Equal.cong(Nat,Nat,n => Nat.add(head,n),value,Nat.add(excess,A.modulus(width)),exact),
        Equal.sym(Nat,Nat.add(Nat.add(head,excess),A.modulus(width)),Nat.add(head,Nat.add(excess,A.modulus(width))),A.add_associative(head,excess,A.modulus(width))))}

law beyond_rewrite:
  for +width: Nat
  for +value: Nat
  for +other: Nat
  for same: {value == other : Nat}
  for beyond: Beyond<width,other>
  Beyond<width,value>
def beyond_rewrite(width,value,other,same,beyond):
  match beyond:
    case Beyond{+excess,exact}:
      Beyond{excess,Equal.trans(Nat,value,other,Nat.add(excess,A.modulus(width)),same,exact)}

law carry_overflows_total:
  for +a: V.Int64
  for +b: V.Int64
  for +accumulator: V.Int64
  for parity: {I.odd(b) == True{} : Bool}
  for carried: {I.unsigned_lt(I.wrapping_add(accumulator,a),accumulator) == True{} : Bool}
  Beyond<64n,total(a,b,accumulator)>
def carry_overflows_total(a,b,accumulator,parity,carried):
  beyond_rewrite(64n,total(a,b,accumulator),expanded(True{},a,b,accumulator),current_is_binary_expansion(a,b,accumulator,True{},parity),
    beyond_append(64n,Nat.add(A.unsigned(accumulator),A.unsigned(a)),Nat.mul(A.unsigned(I.shr(b)),Nat.double(A.unsigned(a))),
      carried_sum_is_beyond(64n,A.unsigned(accumulator),A.unsigned(a),A.unsigned(I.wrapping_add(accumulator,a)),S.carry(64n,A.bits(accumulator),A.bits(a),False{}),
        Equal.trans(Bool,S.carry(64n,A.bits(accumulator),A.bits(a),False{}),I.unsigned_lt(I.wrapping_add(accumulator,a),accumulator),True{},
          Equal.sym(Bool,I.unsigned_lt(I.wrapping_add(accumulator,a),accumulator),S.carry(64n,A.bits(accumulator),A.bits(a),False{}),G.unsigned_add_carry_is_guard(accumulator,a)),carried),A.wrapping_add_natural(accumulator,a))))

law high_shift_is_beyond:
  for +width: Nat
  for +value: Nat
  for +residue: Nat
  for +high: Bool
  for truth: {high == True{} : Bool}
  for exact: {Nat.double(value) == Nat.add(residue,A.spill(width,high)) : Nat}
  Beyond<width,Nat.double(value)>
def high_shift_is_beyond(width,value,residue,high,truth,exact):
  match high:
    case False{}: F.absurd_boolean(Beyond<width,Nat.double(value)>,truth)
    case True{}: Beyond{residue,exact}

law positive_product_is_beyond:
  for +width: Nat
  for +p: Nat
  for +value: Nat
  for beyond: Beyond<width,value>
  Beyond<width,Nat.mul(1n+p,value)>
def positive_product_is_beyond(width,p,value,beyond):
  beyond_append(width,value,Nat.mul(p,value),beyond)

def shift_overflow_with_positive_tail(+a: V.Int64,+b: V.Int64,+accumulator: V.Int64,+odd: Bool,
  parity: {I.odd(b) == odd : Bool},high_bit: {I.negative(a) == True{} : Bool},
  positive: G.Positive<I.shr(b)>) -> Beyond<64n,total(a,b,accumulator)>:
  match positive:
    case G.Positive{+p,measure}:
      beyond_rewrite(64n,total(a,b,accumulator),expanded(odd,a,b,accumulator),current_is_binary_expansion(a,b,accumulator,odd,parity),
        beyond_rewrite(64n,expanded(odd,a,b,accumulator),Nat.add(selected_value(odd,a,accumulator),Nat.mul(1n+p,Nat.double(A.unsigned(a)))),
          Equal.cong(Nat,Nat,n => Nat.add(selected_value(odd,a,accumulator),Nat.mul(n,Nat.double(A.unsigned(a)))),A.unsigned(I.shr(b)),1n+p,measure),
          beyond_prepend(64n,Nat.mul(1n+p,Nat.double(A.unsigned(a))),selected_value(odd,a,accumulator),
            positive_product_is_beyond(64n,p,Nat.double(A.unsigned(a)),high_shift_is_beyond(64n,A.unsigned(a),A.unsigned(I.shl(a)),I.negative(a),high_bit,T.actual_left_shift_natural(a))))))

law shift_overflows_total:
  for +a: V.Int64
  for +b: V.Int64
  for +accumulator: V.Int64
  for +odd: Bool
  for parity: {I.odd(b) == odd : Bool}
  for high_bit: {I.negative(a) == True{} : Bool}
  for nonzero: {I.zero(I.shr(b)) == False{} : Bool}
  Beyond<64n,total(a,b,accumulator)>
def shift_overflows_total(a,b,accumulator,odd,parity,high_bit,nonzero):
  shift_overflow_with_positive_tail(a,b,accumulator,odd,parity,high_bit,G.nonzero_has_positive_measure(I.shr(b),nonzero))

def StepEvidence(+odd: Bool,+carry: Bool,+high: Bool,+zero: Bool,+a: V.Int64,+b: V.Int64,+accumulator: V.Int64) -> Type:
  Bool.pick(Type,(odd && carry) || (high && Bool.not(zero)),
    Beyond<64n,total(a,b,accumulator)>,{total(a,b,accumulator) == next_total(odd,a,b,accumulator) : Nat})

law flags_step_evidence:
  for +odd: Bool
  for +carry: Bool
  for +high: Bool
  for +zero: Bool
  for +a: V.Int64
  for +b: V.Int64
  for +accumulator: V.Int64
  for parity: {I.odd(b) == odd : Bool}
  for carried: {I.unsigned_lt(I.wrapping_add(accumulator,a),accumulator) == carry : Bool}
  for high_bit: {I.negative(a) == high : Bool}
  for is_zero: {I.zero(I.shr(b)) == zero : Bool}
  StepEvidence(odd,carry,high,zero,a,b,accumulator)
def flags_step_evidence(odd,carry,high,zero,a,b,accumulator,parity,carried,high_bit,is_zero):
  match odd carry high zero:
    case False{} False{} False{} False{}:
      safe_step(False{},False{},False{},False{},a,b,accumulator,parity,carried,high_bit,is_zero,{==},{==})
    case False{} False{} False{} True{}:
      safe_step(False{},False{},False{},True{},a,b,accumulator,parity,carried,high_bit,is_zero,{==},{==})
    case False{} False{} True{} False{}:
      shift_overflows_total(a,b,accumulator,False{},parity,high_bit,is_zero)
    case False{} False{} True{} True{}:
      safe_step(False{},False{},True{},True{},a,b,accumulator,parity,carried,high_bit,is_zero,{==},{==})
    case False{} True{} False{} False{}:
      safe_step(False{},True{},False{},False{},a,b,accumulator,parity,carried,high_bit,is_zero,{==},{==})
    case False{} True{} False{} True{}:
      safe_step(False{},True{},False{},True{},a,b,accumulator,parity,carried,high_bit,is_zero,{==},{==})
    case False{} True{} True{} False{}:
      shift_overflows_total(a,b,accumulator,False{},parity,high_bit,is_zero)
    case False{} True{} True{} True{}:
      safe_step(False{},True{},True{},True{},a,b,accumulator,parity,carried,high_bit,is_zero,{==},{==})
    case True{} False{} False{} False{}:
      safe_step(True{},False{},False{},False{},a,b,accumulator,parity,carried,high_bit,is_zero,{==},{==})
    case True{} False{} False{} True{}:
      safe_step(True{},False{},False{},True{},a,b,accumulator,parity,carried,high_bit,is_zero,{==},{==})
    case True{} False{} True{} False{}:
      shift_overflows_total(a,b,accumulator,True{},parity,high_bit,is_zero)
    case True{} False{} True{} True{}:
      safe_step(True{},False{},True{},True{},a,b,accumulator,parity,carried,high_bit,is_zero,{==},{==})
    case True{} True{} False{} False{}:
      carry_overflows_total(a,b,accumulator,parity,carried)
    case True{} True{} False{} True{}:
      carry_overflows_total(a,b,accumulator,parity,carried)
    case True{} True{} True{} False{}:
      carry_overflows_total(a,b,accumulator,parity,carried)
    case True{} True{} True{} True{}:
      carry_overflows_total(a,b,accumulator,parity,carried)

# No proof about an implementation flag is assumed by the public step theorem.
law actual_step_evidence:
  for +a: V.Int64
  for +b: V.Int64
  for +accumulator: V.Int64
  StepEvidence(I.odd(b),I.unsigned_lt(I.wrapping_add(accumulator,a),accumulator),I.negative(a),I.zero(I.shr(b)),a,b,accumulator)
def actual_step_evidence(a,b,accumulator):
  flags_step_evidence(I.odd(b),I.unsigned_lt(I.wrapping_add(accumulator,a),accumulator),I.negative(a),I.zero(I.shr(b)),a,b,accumulator,{==},{==},{==},{==})
