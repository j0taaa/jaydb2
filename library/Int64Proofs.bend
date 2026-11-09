# Arithmetic interpretation of the actual two-word implementation.
# Unbounded Nat values are mathematical measures, never runtime conversions.
# No result, carry, overflow or algorithm equation is received as a premise.
import Base
import ../contract/Logic.bend as L
import ./Value.bend as V
import ../proof/Foundations.bend as F
import ../proof/CodecSums64.bend as C64
import ../proof/CodecAcceptanceTags.bend as Tags
import ./Int64.bend as I
import ../proof/CodecSumsBits.bend as S
import ../proof/CodecWordsWord.bend as W
import ../proof/CodecCounters.bend as N

def bit(b: Bool) -> Nat:
  match b:
    case False{}: 0n
    case True{}: 1n

def place(b: Bool, n: Nat) -> Nat:
  match b:
    case False{}: Nat.double(n)
    case True{}: 1n+Nat.double(n)

def maximum_value(n: Nat) -> Nat:
  match n:
    case 0n: 0n
    case 1n+p: 1n+Nat.double(maximum_value(p))

def modulus(n: Nat) -> Nat:
  1n+maximum_value(n)

def spill(n: Nat, c: Bool) -> Nat:
  match c:
    case False{}: 0n
    case True{}: modulus(n)

law add_zero_right:
  for +a: Nat
  {Nat.add(a, 0n) == a : Nat}
def add_zero_right(a):
  match a:
    case 0n: {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 0n), p, add_zero_right(p))

law double_sum:
  for +a: Nat
  for +b: Nat
  {Nat.double(Nat.add(a, b)) == Nat.add(Nat.double(a), Nat.double(b)) : Nat}
def double_sum(a, b):
  match a:
    case 0n: {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 2n+n,
        Nat.double(Nat.add(p, b)), Nat.add(Nat.double(p), Nat.double(b)), double_sum(p, b))

# Truth-table base plus induction on both unbounded tail measures.
law full_adder_natural:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  for +x: Nat
  for +y: Nat
  {Nat.add(place(a, x), Nat.add(place(b, y), bit(c))) ==
    place(S.bit_sum(a, b, c), Nat.add(x, Nat.add(y, bit(S.bit_carry(a, b, c))))) : Nat}
def full_adder_natural(a, b, c, x, y):
  match a b c:
    case False{} False{} False{}:
      match x y:
        case 0n 0n: {==}
        case 1n+p _:
          Equal.cong(Nat, Nat, n => 2n+n,
            Nat.add(place(False{}, p), Nat.add(place(False{}, y), bit(False{}))),
            place(False{}, Nat.add(p, Nat.add(y, bit(False{})))),
            full_adder_natural(False{}, False{}, False{}, p, y))
        case 0n 1n+q:
          Equal.cong(Nat, Nat, n => 2n+n,
            Nat.add(place(False{}, 0n), Nat.add(place(False{}, q), bit(False{}))),
            place(False{}, Nat.add(0n, Nat.add(q, bit(False{})))),
            full_adder_natural(False{}, False{}, False{}, 0n, q))
    case False{} False{} True{}:
      match x y:
        case 0n 0n: {==}
        case 1n+p _:
          Equal.cong(Nat, Nat, n => 2n+n,
            Nat.add(place(False{}, p), Nat.add(place(False{}, y), bit(True{}))),
            place(True{}, Nat.add(p, Nat.add(y, bit(False{})))),
            full_adder_natural(False{}, False{}, True{}, p, y))
        case 0n 1n+q:
          Equal.cong(Nat, Nat, n => 2n+n,
            Nat.add(place(False{}, 0n), Nat.add(place(False{}, q), bit(True{}))),
            place(True{}, Nat.add(0n, Nat.add(q, bit(False{})))),
            full_adder_natural(False{}, False{}, True{}, 0n, q))
    case False{} True{} False{}:
      match x y:
        case 0n 0n: {==}
        case 1n+p _:
          Equal.cong(Nat, Nat, n => 2n+n,
            Nat.add(place(False{}, p), Nat.add(place(True{}, y), bit(False{}))),
            place(True{}, Nat.add(p, Nat.add(y, bit(False{})))),
            full_adder_natural(False{}, True{}, False{}, p, y))
        case 0n 1n+q:
          Equal.cong(Nat, Nat, n => 2n+n,
            Nat.add(place(False{}, 0n), Nat.add(place(True{}, q), bit(False{}))),
            place(True{}, Nat.add(0n, Nat.add(q, bit(False{})))),
            full_adder_natural(False{}, True{}, False{}, 0n, q))
    case False{} True{} True{}:
      match x y:
        case 0n 0n: {==}
        case 1n+p _:
          Equal.cong(Nat, Nat, n => 2n+n,
            Nat.add(place(False{}, p), Nat.add(place(True{}, y), bit(True{}))),
            place(False{}, Nat.add(p, Nat.add(y, bit(True{})))),
            full_adder_natural(False{}, True{}, True{}, p, y))
        case 0n 1n+q:
          Equal.cong(Nat, Nat, n => 2n+n,
            Nat.add(place(False{}, 0n), Nat.add(place(True{}, q), bit(True{}))),
            place(False{}, Nat.add(0n, Nat.add(q, bit(True{})))),
            full_adder_natural(False{}, True{}, True{}, 0n, q))
    case True{} False{} False{}:
      match x y:
        case 0n 0n: {==}
        case 1n+p _:
          Equal.cong(Nat, Nat, n => 2n+n,
            Nat.add(place(True{}, p), Nat.add(place(False{}, y), bit(False{}))),
            place(True{}, Nat.add(p, Nat.add(y, bit(False{})))),
            full_adder_natural(True{}, False{}, False{}, p, y))
        case 0n 1n+q:
          Equal.cong(Nat, Nat, n => 2n+n,
            Nat.add(place(True{}, 0n), Nat.add(place(False{}, q), bit(False{}))),
            place(True{}, Nat.add(0n, Nat.add(q, bit(False{})))),
            full_adder_natural(True{}, False{}, False{}, 0n, q))
    case True{} False{} True{}:
      match x y:
        case 0n 0n: {==}
        case 1n+p _:
          Equal.cong(Nat, Nat, n => 2n+n,
            Nat.add(place(True{}, p), Nat.add(place(False{}, y), bit(True{}))),
            place(False{}, Nat.add(p, Nat.add(y, bit(True{})))),
            full_adder_natural(True{}, False{}, True{}, p, y))
        case 0n 1n+q:
          Equal.cong(Nat, Nat, n => 2n+n,
            Nat.add(place(True{}, 0n), Nat.add(place(False{}, q), bit(True{}))),
            place(False{}, Nat.add(0n, Nat.add(q, bit(True{})))),
            full_adder_natural(True{}, False{}, True{}, 0n, q))
    case True{} True{} False{}:
      match x y:
        case 0n 0n: {==}
        case 1n+p _:
          Equal.cong(Nat, Nat, n => 2n+n,
            Nat.add(place(True{}, p), Nat.add(place(True{}, y), bit(False{}))),
            place(False{}, Nat.add(p, Nat.add(y, bit(True{})))),
            full_adder_natural(True{}, True{}, False{}, p, y))
        case 0n 1n+q:
          Equal.cong(Nat, Nat, n => 2n+n,
            Nat.add(place(True{}, 0n), Nat.add(place(True{}, q), bit(False{}))),
            place(False{}, Nat.add(0n, Nat.add(q, bit(True{})))),
            full_adder_natural(True{}, True{}, False{}, 0n, q))
    case True{} True{} True{}:
      match x y:
        case 0n 0n: {==}
        case 1n+p _:
          Equal.cong(Nat, Nat, n => 2n+n,
            Nat.add(place(True{}, p), Nat.add(place(True{}, y), bit(True{}))),
            place(True{}, Nat.add(p, Nat.add(y, bit(True{})))),
            full_adder_natural(True{}, True{}, True{}, p, y))
        case 0n 1n+q:
          Equal.cong(Nat, Nat, n => 2n+n,
            Nat.add(place(True{}, 0n), Nat.add(place(True{}, q), bit(True{}))),
            place(True{}, Nat.add(0n, Nat.add(q, bit(True{})))),
            full_adder_natural(True{}, True{}, True{}, 0n, q))

law place_spill:
  for +n: Nat
  for +b: Bool
  for +r: Nat
  for +c: Bool
  {place(b, Nat.add(r, spill(n, c))) == Nat.add(place(b, r), spill(1n+n, c)) : Nat}
def place_spill(n, b, r, c):
  match b c:
    case False{} False{}:
      Equal.trans(Nat, place(False{}, Nat.add(r, 0n)), place(False{}, r), Nat.add(place(False{}, r), 0n),
        Equal.cong(Nat, Nat, x => place(False{}, x), Nat.add(r, 0n), r, add_zero_right(r)),
        Equal.sym(Nat, Nat.add(place(False{}, r), 0n), place(False{}, r), add_zero_right(place(False{}, r))))
    case True{} False{}:
      Equal.trans(Nat, place(True{}, Nat.add(r, 0n)), place(True{}, r), Nat.add(place(True{}, r), 0n),
        Equal.cong(Nat, Nat, x => place(True{}, x), Nat.add(r, 0n), r, add_zero_right(r)),
        Equal.sym(Nat, Nat.add(place(True{}, r), 0n), place(True{}, r), add_zero_right(place(True{}, r))))
    case False{} True{}: double_sum(r, modulus(n))
    case True{} True{}:
      Equal.cong(Nat, Nat, x => 1n+x,
        Nat.double(Nat.add(r, modulus(n))), Nat.add(Nat.double(r), Nat.double(modulus(n))),
        double_sum(r, modulus(n)))

# Output value + radix times the final carry equals the exact mathematical sum.
law adc_natural:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Bool
  {Nat.add(Word.to_nat(n, a), Nat.add(Word.to_nat(n, b), bit(c))) ==
    Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, c)), spill(n, S.carry(n, a, b, c))) : Nat}
def adc_natural(n, a, b, c):
  match n:
    case 0n:
      match c:
        case False{}: {==}
        case True{}: {==}
    case 1n+p:
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          Equal.trans(Nat,
            Nat.add(place(False{}, Word.to_nat(p, at)), Nat.add(place(False{}, Word.to_nat(p, bt)), bit(False{}))),
            place(False{}, Nat.add(Word.to_nat(p, at), Nat.add(Word.to_nat(p, bt), bit(False{})))),
            Nat.add(place(False{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, False{}))), spill(1n+p, S.carry(p, at, bt, False{}))),
            full_adder_natural(False{}, False{}, False{}, Word.to_nat(p, at), Word.to_nat(p, bt)),
            Equal.trans(Nat,
              place(False{}, Nat.add(Word.to_nat(p, at), Nat.add(Word.to_nat(p, bt), bit(False{})))),
              place(False{}, Nat.add(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), spill(p, S.carry(p, at, bt, False{})))),
              Nat.add(place(False{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, False{}))), spill(1n+p, S.carry(p, at, bt, False{}))),
              Equal.cong(Nat, Nat, x => place(False{}, x),
                Nat.add(Word.to_nat(p, at), Nat.add(Word.to_nat(p, bt), bit(False{}))), Nat.add(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), spill(p, S.carry(p, at, bt, False{}))), adc_natural(p, at, bt, False{})),
              place_spill(p, False{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), S.carry(p, at, bt, False{}))))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          Equal.trans(Nat,
            Nat.add(place(False{}, Word.to_nat(p, at)), Nat.add(place(False{}, Word.to_nat(p, bt)), bit(True{}))),
            place(True{}, Nat.add(Word.to_nat(p, at), Nat.add(Word.to_nat(p, bt), bit(False{})))),
            Nat.add(place(True{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, False{}))), spill(1n+p, S.carry(p, at, bt, False{}))),
            full_adder_natural(False{}, False{}, True{}, Word.to_nat(p, at), Word.to_nat(p, bt)),
            Equal.trans(Nat,
              place(True{}, Nat.add(Word.to_nat(p, at), Nat.add(Word.to_nat(p, bt), bit(False{})))),
              place(True{}, Nat.add(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), spill(p, S.carry(p, at, bt, False{})))),
              Nat.add(place(True{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, False{}))), spill(1n+p, S.carry(p, at, bt, False{}))),
              Equal.cong(Nat, Nat, x => place(True{}, x),
                Nat.add(Word.to_nat(p, at), Nat.add(Word.to_nat(p, bt), bit(False{}))), Nat.add(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), spill(p, S.carry(p, at, bt, False{}))), adc_natural(p, at, bt, False{})),
              place_spill(p, True{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), S.carry(p, at, bt, False{}))))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          Equal.trans(Nat,
            Nat.add(place(False{}, Word.to_nat(p, at)), Nat.add(place(True{}, Word.to_nat(p, bt)), bit(False{}))),
            place(True{}, Nat.add(Word.to_nat(p, at), Nat.add(Word.to_nat(p, bt), bit(False{})))),
            Nat.add(place(True{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, False{}))), spill(1n+p, S.carry(p, at, bt, False{}))),
            full_adder_natural(False{}, True{}, False{}, Word.to_nat(p, at), Word.to_nat(p, bt)),
            Equal.trans(Nat,
              place(True{}, Nat.add(Word.to_nat(p, at), Nat.add(Word.to_nat(p, bt), bit(False{})))),
              place(True{}, Nat.add(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), spill(p, S.carry(p, at, bt, False{})))),
              Nat.add(place(True{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, False{}))), spill(1n+p, S.carry(p, at, bt, False{}))),
              Equal.cong(Nat, Nat, x => place(True{}, x),
                Nat.add(Word.to_nat(p, at), Nat.add(Word.to_nat(p, bt), bit(False{}))), Nat.add(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), spill(p, S.carry(p, at, bt, False{}))), adc_natural(p, at, bt, False{})),
              place_spill(p, True{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), S.carry(p, at, bt, False{}))))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          Equal.trans(Nat,
            Nat.add(place(False{}, Word.to_nat(p, at)), Nat.add(place(True{}, Word.to_nat(p, bt)), bit(True{}))),
            place(False{}, Nat.add(Word.to_nat(p, at), Nat.add(Word.to_nat(p, bt), bit(True{})))),
            Nat.add(place(False{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, True{}))), spill(1n+p, S.carry(p, at, bt, True{}))),
            full_adder_natural(False{}, True{}, True{}, Word.to_nat(p, at), Word.to_nat(p, bt)),
            Equal.trans(Nat,
              place(False{}, Nat.add(Word.to_nat(p, at), Nat.add(Word.to_nat(p, bt), bit(True{})))),
              place(False{}, Nat.add(Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})), spill(p, S.carry(p, at, bt, True{})))),
              Nat.add(place(False{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, True{}))), spill(1n+p, S.carry(p, at, bt, True{}))),
              Equal.cong(Nat, Nat, x => place(False{}, x),
                Nat.add(Word.to_nat(p, at), Nat.add(Word.to_nat(p, bt), bit(True{}))), Nat.add(Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})), spill(p, S.carry(p, at, bt, True{}))), adc_natural(p, at, bt, True{})),
              place_spill(p, False{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})), S.carry(p, at, bt, True{}))))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          Equal.trans(Nat,
            Nat.add(place(True{}, Word.to_nat(p, at)), Nat.add(place(False{}, Word.to_nat(p, bt)), bit(False{}))),
            place(True{}, Nat.add(Word.to_nat(p, at), Nat.add(Word.to_nat(p, bt), bit(False{})))),
            Nat.add(place(True{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, False{}))), spill(1n+p, S.carry(p, at, bt, False{}))),
            full_adder_natural(True{}, False{}, False{}, Word.to_nat(p, at), Word.to_nat(p, bt)),
            Equal.trans(Nat,
              place(True{}, Nat.add(Word.to_nat(p, at), Nat.add(Word.to_nat(p, bt), bit(False{})))),
              place(True{}, Nat.add(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), spill(p, S.carry(p, at, bt, False{})))),
              Nat.add(place(True{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, False{}))), spill(1n+p, S.carry(p, at, bt, False{}))),
              Equal.cong(Nat, Nat, x => place(True{}, x),
                Nat.add(Word.to_nat(p, at), Nat.add(Word.to_nat(p, bt), bit(False{}))), Nat.add(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), spill(p, S.carry(p, at, bt, False{}))), adc_natural(p, at, bt, False{})),
              place_spill(p, True{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), S.carry(p, at, bt, False{}))))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          Equal.trans(Nat,
            Nat.add(place(True{}, Word.to_nat(p, at)), Nat.add(place(False{}, Word.to_nat(p, bt)), bit(True{}))),
            place(False{}, Nat.add(Word.to_nat(p, at), Nat.add(Word.to_nat(p, bt), bit(True{})))),
            Nat.add(place(False{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, True{}))), spill(1n+p, S.carry(p, at, bt, True{}))),
            full_adder_natural(True{}, False{}, True{}, Word.to_nat(p, at), Word.to_nat(p, bt)),
            Equal.trans(Nat,
              place(False{}, Nat.add(Word.to_nat(p, at), Nat.add(Word.to_nat(p, bt), bit(True{})))),
              place(False{}, Nat.add(Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})), spill(p, S.carry(p, at, bt, True{})))),
              Nat.add(place(False{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, True{}))), spill(1n+p, S.carry(p, at, bt, True{}))),
              Equal.cong(Nat, Nat, x => place(False{}, x),
                Nat.add(Word.to_nat(p, at), Nat.add(Word.to_nat(p, bt), bit(True{}))), Nat.add(Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})), spill(p, S.carry(p, at, bt, True{}))), adc_natural(p, at, bt, True{})),
              place_spill(p, False{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})), S.carry(p, at, bt, True{}))))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          Equal.trans(Nat,
            Nat.add(place(True{}, Word.to_nat(p, at)), Nat.add(place(True{}, Word.to_nat(p, bt)), bit(False{}))),
            place(False{}, Nat.add(Word.to_nat(p, at), Nat.add(Word.to_nat(p, bt), bit(True{})))),
            Nat.add(place(False{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, True{}))), spill(1n+p, S.carry(p, at, bt, True{}))),
            full_adder_natural(True{}, True{}, False{}, Word.to_nat(p, at), Word.to_nat(p, bt)),
            Equal.trans(Nat,
              place(False{}, Nat.add(Word.to_nat(p, at), Nat.add(Word.to_nat(p, bt), bit(True{})))),
              place(False{}, Nat.add(Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})), spill(p, S.carry(p, at, bt, True{})))),
              Nat.add(place(False{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, True{}))), spill(1n+p, S.carry(p, at, bt, True{}))),
              Equal.cong(Nat, Nat, x => place(False{}, x),
                Nat.add(Word.to_nat(p, at), Nat.add(Word.to_nat(p, bt), bit(True{}))), Nat.add(Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})), spill(p, S.carry(p, at, bt, True{}))), adc_natural(p, at, bt, True{})),
              place_spill(p, False{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})), S.carry(p, at, bt, True{}))))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          Equal.trans(Nat,
            Nat.add(place(True{}, Word.to_nat(p, at)), Nat.add(place(True{}, Word.to_nat(p, bt)), bit(True{}))),
            place(True{}, Nat.add(Word.to_nat(p, at), Nat.add(Word.to_nat(p, bt), bit(True{})))),
            Nat.add(place(True{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, True{}))), spill(1n+p, S.carry(p, at, bt, True{}))),
            full_adder_natural(True{}, True{}, True{}, Word.to_nat(p, at), Word.to_nat(p, bt)),
            Equal.trans(Nat,
              place(True{}, Nat.add(Word.to_nat(p, at), Nat.add(Word.to_nat(p, bt), bit(True{})))),
              place(True{}, Nat.add(Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})), spill(p, S.carry(p, at, bt, True{})))),
              Nat.add(place(True{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, True{}))), spill(1n+p, S.carry(p, at, bt, True{}))),
              Equal.cong(Nat, Nat, x => place(True{}, x),
                Nat.add(Word.to_nat(p, at), Nat.add(Word.to_nat(p, bt), bit(True{}))), Nat.add(Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})), spill(p, S.carry(p, at, bt, True{}))), adc_natural(p, at, bt, True{})),
              place_spill(p, True{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})), S.carry(p, at, bt, True{}))))

law adc_carry_is_increment:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.adc(n, a, b, False{}, True{}) == Word.inc(n, Word.add(n, a, b)) : Word(n)}
def adc_carry_is_increment(n, a, b):
  match n:
    case 0n: {==}
    case 1n+p:
      match a b:
        case WCon{False{}, at} WCon{False{}, bt}: {==}
        case WCon{False{}, +at} WCon{True{}, +bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.adc(p, at, bt, False{}, True{}), Word.inc(p, Word.add(p, at, bt)),
            adc_carry_is_increment(p, at, bt))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.adc(p, at, bt, False{}, True{}), Word.inc(p, Word.add(p, at, bt)),
            adc_carry_is_increment(p, at, bt))
        case WCon{True{}, at} WCon{True{}, bt}: {==}

law adc_blocks:
  for +k: Nat
  for +n: Nat
  for +al: Word(k)
  for +bl: Word(k)
  for +ah: Word(n)
  for +bh: Word(n)
  for +c: Bool
  {Word.adc(Nat.add(k, n), W.join(k, n, al, ah), W.join(k, n, bl, bh), False{}, c) ==
    W.join(k, n, Word.adc(k, al, bl, False{}, c), Word.adc(n, ah, bh, False{}, S.carry(k, al, bl, c))) : Word(Nat.add(k, n))}
def adc_blocks(k, n, al, bl, ah, bh, c):
  match k:
    case 0n: {==}
    case 1n+p:
      match al bl c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), w => WCon{False{}, w},
            Word.adc(Nat.add(p, n), W.join(p, n, at, ah), W.join(p, n, bt, bh), False{}, False{}),
            W.join(p, n, Word.adc(p, at, bt, False{}, False{}), Word.adc(n, ah, bh, False{}, S.carry(p, at, bt, False{}))),
            adc_blocks(p, n, at, bt, ah, bh, False{}))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), w => WCon{True{}, w},
            Word.adc(Nat.add(p, n), W.join(p, n, at, ah), W.join(p, n, bt, bh), False{}, False{}),
            W.join(p, n, Word.adc(p, at, bt, False{}, False{}), Word.adc(n, ah, bh, False{}, S.carry(p, at, bt, False{}))),
            adc_blocks(p, n, at, bt, ah, bh, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), w => WCon{True{}, w},
            Word.adc(Nat.add(p, n), W.join(p, n, at, ah), W.join(p, n, bt, bh), False{}, False{}),
            W.join(p, n, Word.adc(p, at, bt, False{}, False{}), Word.adc(n, ah, bh, False{}, S.carry(p, at, bt, False{}))),
            adc_blocks(p, n, at, bt, ah, bh, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), w => WCon{False{}, w},
            Word.adc(Nat.add(p, n), W.join(p, n, at, ah), W.join(p, n, bt, bh), False{}, True{}),
            W.join(p, n, Word.adc(p, at, bt, False{}, True{}), Word.adc(n, ah, bh, False{}, S.carry(p, at, bt, True{}))),
            adc_blocks(p, n, at, bt, ah, bh, True{}))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), w => WCon{True{}, w},
            Word.adc(Nat.add(p, n), W.join(p, n, at, ah), W.join(p, n, bt, bh), False{}, False{}),
            W.join(p, n, Word.adc(p, at, bt, False{}, False{}), Word.adc(n, ah, bh, False{}, S.carry(p, at, bt, False{}))),
            adc_blocks(p, n, at, bt, ah, bh, False{}))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), w => WCon{False{}, w},
            Word.adc(Nat.add(p, n), W.join(p, n, at, ah), W.join(p, n, bt, bh), False{}, True{}),
            W.join(p, n, Word.adc(p, at, bt, False{}, True{}), Word.adc(n, ah, bh, False{}, S.carry(p, at, bt, True{}))),
            adc_blocks(p, n, at, bt, ah, bh, True{}))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), w => WCon{False{}, w},
            Word.adc(Nat.add(p, n), W.join(p, n, at, ah), W.join(p, n, bt, bh), False{}, True{}),
            W.join(p, n, Word.adc(p, at, bt, False{}, True{}), Word.adc(n, ah, bh, False{}, S.carry(p, at, bt, True{}))),
            adc_blocks(p, n, at, bt, ah, bh, True{}))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), w => WCon{True{}, w},
            Word.adc(Nat.add(p, n), W.join(p, n, at, ah), W.join(p, n, bt, bh), False{}, True{}),
            W.join(p, n, Word.adc(p, at, bt, False{}, True{}), Word.adc(n, ah, bh, False{}, S.carry(p, at, bt, True{}))),
            adc_blocks(p, n, at, bt, ah, bh, True{}))

def word(x: U32) -> Word(32n):
  U32{w} = x
  w

def bits(x: V.Int64) -> Word(64n):
  V.Int64{U32{h}, U32{l}} = x
  W.join(32n, 32n, l, h)

def unsigned(x: V.Int64) -> Nat:
  Word.to_nat(64n, bits(x))

law high_carry_exact:
  for +a: Word(32n)
  for +b: Word(32n)
  for c: Bool
  {Word.add(32n, Word.add(32n, a, b), word(Bool.to_u32(c))) == Word.adc(32n, a, b, False{}, c) : Word(32n)}
def high_carry_exact(a, b, c):
  match c:
    case False{}: W.sum_zero_right(32n, Word.add(32n, a, b))
    case True{}:
      Equal.trans(Word(32n), Word.add(32n, Word.add(32n, a, b), N.one(31n)),
        Word.inc(32n, Word.add(32n, a, b)), Word.adc(32n, a, b, False{}, True{}),
        N.sum_one_increments(31n, Word.add(32n, a, b)),
        Equal.sym(Word(32n), Word.adc(32n, a, b, False{}, True{}), Word.inc(32n, Word.add(32n, a, b)),
          adc_carry_is_increment(32n, a, b)))

law bits_add_carry:
  for +ah: Word(32n)
  for +al: Word(32n)
  for +bh: Word(32n)
  for +bl: Word(32n)
  for +c: Bool
  {bits(V.Int64{U32.add(U32.add(U32{ah}, U32{bh}), Bool.to_u32(c)), U32.add(U32{al}, U32{bl})}) ==
    W.join(32n, 32n, Word.add(32n, al, bl), Word.adc(32n, ah, bh, False{}, c)) : Word(64n)}
def bits_add_carry(ah, al, bh, bl, c):
  match c:
    case False{}:
      Equal.cong(Word(32n), Word(64n), w => W.join(32n, 32n, Word.add(32n, al, bl), w),
        Word.add(32n, Word.add(32n, ah, bh), word(Bool.to_u32(False{}))),
        Word.adc(32n, ah, bh, False{}, False{}), high_carry_exact(ah, bh, False{}))
    case True{}:
      Equal.cong(Word(32n), Word(64n), w => W.join(32n, 32n, Word.add(32n, al, bl), w),
        Word.add(32n, Word.add(32n, ah, bh), word(Bool.to_u32(True{}))),
        Word.adc(32n, ah, bh, False{}, True{}), high_carry_exact(ah, bh, True{}))

law wrapping_add_is_full_word_add:
  for +a: V.Int64
  for +b: V.Int64
  {bits(I.wrapping_add(a, b)) == Word.add(64n, bits(a), bits(b)) : Word(64n)}
def wrapping_add_is_full_word_add(a, b):
  match a b:
    case V.Int64{U32{+ah}, U32{+al}} V.Int64{U32{+bh}, U32{+bl}}:
      %S.carry_equivalent_comparison(32n, al, bl, False{}) :
        {bits(V.Int64{U32.add(U32.add(U32{ah}, U32{bh}), Bool.to_u32(_)), U32.add(U32{al}, U32{bl})}) ==
          Word.add(64n, W.join(32n, 32n, al, ah), W.join(32n, 32n, bl, bh)) : Word(64n)}
      Equal.trans(Word(64n),
        bits(V.Int64{U32.add(U32.add(U32{ah}, U32{bh}), Bool.to_u32(S.carry(32n, al, bl, False{}))), U32.add(U32{al}, U32{bl})}),
        W.join(32n, 32n, Word.add(32n, al, bl), Word.adc(32n, ah, bh, False{}, S.carry(32n, al, bl, False{}))),
        Word.add(64n, W.join(32n, 32n, al, ah), W.join(32n, 32n, bl, bh)),
        bits_add_carry(ah, al, bh, bl, S.carry(32n, al, bl, False{})),
        Equal.sym(Word(64n),
          Word.add(64n, W.join(32n, 32n, al, ah), W.join(32n, 32n, bl, bh)),
          W.join(32n, 32n, Word.add(32n, al, bl), Word.adc(32n, ah, bh, False{}, S.carry(32n, al, bl, False{}))),
          adc_blocks(32n, 32n, al, bl, ah, bh, False{})))

# Unsigned interpretation of wrapping addition for EVERY pair of signed-word
# representations: exact sum = wrapped unsigned result + 2^64 * carry.
law wrapping_add_natural:
  for +a: V.Int64
  for +b: V.Int64
  {Nat.add(unsigned(a), unsigned(b)) ==
    Nat.add(unsigned(I.wrapping_add(a, b)), spill(64n, S.carry(64n, bits(a), bits(b), False{}))) : Nat}
def wrapping_add_natural(a, b):
  Equal.trans(Nat, Nat.add(unsigned(a), unsigned(b)),
    Nat.add(unsigned(a), Nat.add(unsigned(b), 0n)),
    Nat.add(unsigned(I.wrapping_add(a, b)), spill(64n, S.carry(64n, bits(a), bits(b), False{}))),
    Equal.cong(Nat, Nat, n => Nat.add(unsigned(a), n), unsigned(b), Nat.add(unsigned(b), 0n),
      Equal.sym(Nat, Nat.add(unsigned(b), 0n), unsigned(b), add_zero_right(unsigned(b)))),
    Equal.trans(Nat, Nat.add(unsigned(a), Nat.add(unsigned(b), 0n)),
      Nat.add(Word.to_nat(64n, Word.add(64n, bits(a), bits(b))), spill(64n, S.carry(64n, bits(a), bits(b), False{}))),
      Nat.add(unsigned(I.wrapping_add(a, b)), spill(64n, S.carry(64n, bits(a), bits(b), False{}))),
      adc_natural(64n, bits(a), bits(b), False{}),
      Equal.cong(Word(64n), Nat, w => Nat.add(Word.to_nat(64n, w), spill(64n, S.carry(64n, bits(a), bits(b), False{}))),
        Word.add(64n, bits(a), bits(b)), bits(I.wrapping_add(a, b)),
        Equal.sym(Word(64n), bits(I.wrapping_add(a, b)), Word.add(64n, bits(a), bits(b)), wrapping_add_is_full_word_add(a, b)))))

# Highest bit and the usual two's-complement integer interpretation.
def nat_zero(n: Nat) -> Bool:
  match n:
    case 0n: True{}
    case 1n+p: False{}

def top(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n: False{}
    case 1n+ +p:
      match w:
        case WCon{b, t}: Bool.pick(Bool, nat_zero(p), b, top(p, t))

def sign_threshold(n: Nat) -> Word(1n+n):
  match n:
    case 0n: WCon{True{}, WNil{}}
    case 1n+p: WCon{False{}, sign_threshold(p)}

law compare_zero_low_bit:
  for b: Bool
  for c: Cmp
  {Cmp.is_ge(Word.cmp.fin(b, False{}, c)) == Cmp.is_ge(c) : Bool}
def compare_zero_low_bit(b, c):
  match b c:
    case False{} LT{}: {==}
    case False{} EQ{}: {==}
    case False{} GT{}: {==}
    case True{} LT{}: {==}
    case True{} EQ{}: {==}
    case True{} GT{}: {==}

law sign_threshold_is_top:
  for +n: Nat
  for +w: Word(1n+n)
  {Cmp.is_ge(Word.cmp(1n+n, w, sign_threshold(n))) == top(1n+n, w) : Bool}
def sign_threshold_is_top(n, w):
  match n:
    case 0n:
      match w:
        case WCon{False{}, WNil{}}: {==}
        case WCon{True{}, WNil{}}: {==}
    case 1n+p:
      match w:
        case WCon{b, +t}:
          Equal.trans(Bool,
            Cmp.is_ge(Word.cmp.fin(b, False{}, Word.cmp(1n+p, t, sign_threshold(p)))),
            Cmp.is_ge(Word.cmp(1n+p, t, sign_threshold(p))), top(1n+p, t),
            compare_zero_low_bit(b, Word.cmp(1n+p, t, sign_threshold(p))), sign_threshold_is_top(p, t))

law sum_successor_is_positive:
  for k: Nat
  for n: Nat
  {nat_zero(Nat.add(k, 1n+n)) == False{} : Bool}
def sum_successor_is_positive(k, n):
  match k:
    case 0n: {==}
    case 1n+p: {==}

law top_join:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(1n+n)
  {top(Nat.add(k, 1n+n), W.join(k, 1n+n, lo, hi)) == top(1n+n, hi) : Bool}
def top_join(k, n, lo, hi):
  match k:
    case 0n: {==}
    case 1n+p:
      match lo:
        case WCon{b, t}:
          %Equal.sym(Bool, nat_zero(Nat.add(p, 1n+n)), False{}, sum_successor_is_positive(p, n)) :
            {Bool.pick(Bool, _, b, top(Nat.add(p, 1n+n), W.join(p, 1n+n, t, hi))) == top(1n+n, hi) : Bool}
          top_join(p, n, t, hi)

law negative_is_sign_bit:
  for +x: V.Int64
  {I.negative(x) == top(64n, bits(x)) : Bool}
def negative_is_sign_bit(x):
  match x:
    case V.Int64{U32{+h}, U32{+l}}:
      Equal.trans(Bool, Cmp.is_ge(Word.cmp(32n, h, sign_threshold(31n))), top(32n, h),
        top(64n, W.join(32n, 32n, l, h)), sign_threshold_is_top(31n, h),
        Equal.sym(Bool, top(64n, W.join(32n, 32n, l, h)), top(32n, h), top_join(32n, 31n, l, h)))

# A signed addition fits exactly when the final carry balances the sign bits.
# The relation on the right is an equality of unbounded natural counts.
law signed_carry_balance:
  for +n: Nat
  for +a: Word(1n+n)
  for +b: Word(1n+n)
  for +c: Bool
  for fits: {(Bool.not(Bool.xor(top(1n+n, a), top(1n+n, b))) &&
    Bool.xor(top(1n+n, a), top(1n+n, Word.adc(1n+n, a, b, False{}, c)))) == False{} : Bool}
  {Nat.add(bit(top(1n+n, a)), bit(top(1n+n, b))) ==
    Nat.add(bit(top(1n+n, Word.adc(1n+n, a, b, False{}, c))), bit(S.carry(1n+n, a, b, c))) : Nat}
def signed_carry_balance(n, a, b, c, fits):
  match n:
    case 0n:
      match a b c:
        case WCon{False{}, WNil{}} WCon{False{}, WNil{}} False{}:
          {==}
        case WCon{False{}, WNil{}} WCon{False{}, WNil{}} True{}:
          F.absurd_boolean({Nat.add(bit(False{}), bit(False{})) == Nat.add(bit(True{}), bit(False{})) : Nat}, Equal.sym(Bool, True{}, False{}, fits))
        case WCon{False{}, WNil{}} WCon{True{}, WNil{}} False{}:
          {==}
        case WCon{False{}, WNil{}} WCon{True{}, WNil{}} True{}:
          {==}
        case WCon{True{}, WNil{}} WCon{False{}, WNil{}} False{}:
          {==}
        case WCon{True{}, WNil{}} WCon{False{}, WNil{}} True{}:
          {==}
        case WCon{True{}, WNil{}} WCon{True{}, WNil{}} False{}:
          F.absurd_boolean({Nat.add(bit(True{}), bit(True{})) == Nat.add(bit(False{}), bit(True{})) : Nat}, Equal.sym(Bool, True{}, False{}, fits))
        case WCon{True{}, WNil{}} WCon{True{}, WNil{}} True{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{False{}, at} WCon{False{}, bt} False{}:
          signed_carry_balance(p, at, bt, False{}, fits)
        case WCon{False{}, at} WCon{False{}, bt} True{}:
          signed_carry_balance(p, at, bt, False{}, fits)
        case WCon{False{}, at} WCon{True{}, bt} False{}:
          signed_carry_balance(p, at, bt, False{}, fits)
        case WCon{False{}, at} WCon{True{}, bt} True{}:
          signed_carry_balance(p, at, bt, True{}, fits)
        case WCon{True{}, at} WCon{False{}, bt} False{}:
          signed_carry_balance(p, at, bt, False{}, fits)
        case WCon{True{}, at} WCon{False{}, bt} True{}:
          signed_carry_balance(p, at, bt, True{}, fits)
        case WCon{True{}, at} WCon{True{}, bt} False{}:
          signed_carry_balance(p, at, bt, True{}, fits)
        case WCon{True{}, at} WCon{True{}, bt} True{}:
          signed_carry_balance(p, at, bt, True{}, fits)

# An integer is the difference of two unbounded naturals. Integer equality and
# addition use cross-addition; they do not inspect any implementation overflow.
type Integer is Data:
  Integer{positive: Nat, negative: Nat}

def integer(+x: V.Int64) -> Integer:
  Integer{unsigned(x), spill(64n, top(64n, bits(x)))}

def IntegerSum(a: Integer, b: Integer, r: Integer) -> Type:
  Integer{ap, an} = a
  Integer{bp, bn} = b
  Integer{rp, rn} = r
  {Nat.add(Nat.add(ap, bp), rn) == Nat.add(rp, Nat.add(an, bn)) : Nat}

law add_associative:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}
def add_associative(a, b, c):
  match a:
    case 0n: {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n,
        Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), add_associative(p, b, c))

law scale_carry_balance:
  for +n: Nat
  for +a: Bool
  for +b: Bool
  for +r: Bool
  for +c: Bool
  for balance: {Nat.add(bit(a), bit(b)) == Nat.add(bit(r), bit(c)) : Nat}
  {Nat.add(spill(n, c), spill(n, r)) == Nat.add(spill(n, a), spill(n, b)) : Nat}
def scale_carry_balance(n, a, b, r, c, balance):
  match a b r c:
    case False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{}:
      F.absurd_boolean({Nat.add(spill(n, True{}), spill(n, False{})) == Nat.add(spill(n, False{}), spill(n, False{})) : Nat}, Equal.cong(Nat, Bool, v => Bool.not(Nat.is_eq(v, 0n)), 0n, 1n, balance))
    case False{} False{} True{} False{}:
      F.absurd_boolean({Nat.add(spill(n, False{}), spill(n, True{})) == Nat.add(spill(n, False{}), spill(n, False{})) : Nat}, Equal.cong(Nat, Bool, v => Bool.not(Nat.is_eq(v, 0n)), 0n, 1n, balance))
    case False{} False{} True{} True{}:
      F.absurd_boolean({Nat.add(spill(n, True{}), spill(n, True{})) == Nat.add(spill(n, False{}), spill(n, False{})) : Nat}, Equal.cong(Nat, Bool, v => Bool.not(Nat.is_eq(v, 0n)), 0n, 2n, balance))
    case False{} True{} False{} False{}:
      F.absurd_boolean({Nat.add(spill(n, False{}), spill(n, False{})) == Nat.add(spill(n, False{}), spill(n, True{})) : Nat}, Equal.cong(Nat, Bool, v => Bool.not(Nat.is_eq(v, 1n)), 1n, 0n, balance))
    case False{} True{} False{} True{}:
      add_zero_right(modulus(n))
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{}:
      F.absurd_boolean({Nat.add(spill(n, True{}), spill(n, True{})) == Nat.add(spill(n, False{}), spill(n, True{})) : Nat}, Equal.cong(Nat, Bool, v => Bool.not(Nat.is_eq(v, 1n)), 1n, 2n, balance))
    case True{} False{} False{} False{}:
      F.absurd_boolean({Nat.add(spill(n, False{}), spill(n, False{})) == Nat.add(spill(n, True{}), spill(n, False{})) : Nat}, Equal.cong(Nat, Bool, v => Bool.not(Nat.is_eq(v, 1n)), 1n, 0n, balance))
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{}:
      Equal.sym(Nat, Nat.add(modulus(n), 0n), modulus(n), add_zero_right(modulus(n)))
    case True{} False{} True{} True{}:
      F.absurd_boolean({Nat.add(spill(n, True{}), spill(n, True{})) == Nat.add(spill(n, True{}), spill(n, False{})) : Nat}, Equal.cong(Nat, Bool, v => Bool.not(Nat.is_eq(v, 1n)), 1n, 2n, balance))
    case True{} True{} False{} False{}:
      F.absurd_boolean({Nat.add(spill(n, False{}), spill(n, False{})) == Nat.add(spill(n, True{}), spill(n, True{})) : Nat}, Equal.cong(Nat, Bool, v => Bool.not(Nat.is_eq(v, 2n)), 2n, 0n, balance))
    case True{} True{} False{} True{}:
      F.absurd_boolean({Nat.add(spill(n, True{}), spill(n, False{})) == Nat.add(spill(n, True{}), spill(n, True{})) : Nat}, Equal.cong(Nat, Bool, v => Bool.not(Nat.is_eq(v, 2n)), 2n, 1n, balance))
    case True{} True{} True{} False{}:
      F.absurd_boolean({Nat.add(spill(n, False{}), spill(n, True{})) == Nat.add(spill(n, True{}), spill(n, True{})) : Nat}, Equal.cong(Nat, Bool, v => Bool.not(Nat.is_eq(v, 2n)), 2n, 1n, balance))
    case True{} True{} True{} True{}:
      {==}

law add_overflow_is_word_sign_overflow:
  for +a: V.Int64
  for +b: V.Int64
  {I.add_overflow(a, b) ==
    (Bool.not(Bool.xor(top(64n, bits(a)), top(64n, bits(b)))) &&
      Bool.xor(top(64n, bits(a)), top(64n, Word.add(64n, bits(a), bits(b))))) : Bool}
def add_overflow_is_word_sign_overflow(a, b):
  %Equal.sym(Bool, I.negative(a), top(64n, bits(a)), negative_is_sign_bit(a)) :
    {(Bool.not(Bool.xor(_, I.negative(b))) && Bool.xor(_, I.negative(I.wrapping_add(a, b)))) ==
      (Bool.not(Bool.xor(top(64n, bits(a)), top(64n, bits(b)))) &&
        Bool.xor(top(64n, bits(a)), top(64n, Word.add(64n, bits(a), bits(b))))) : Bool}
  %Equal.sym(Bool, I.negative(b), top(64n, bits(b)), negative_is_sign_bit(b)) :
    {(Bool.not(Bool.xor(top(64n, bits(a)), _)) && Bool.xor(top(64n, bits(a)), I.negative(I.wrapping_add(a, b)))) ==
      (Bool.not(Bool.xor(top(64n, bits(a)), top(64n, bits(b)))) &&
        Bool.xor(top(64n, bits(a)), top(64n, Word.add(64n, bits(a), bits(b))))) : Bool}
  %Equal.sym(Bool, I.negative(I.wrapping_add(a, b)), top(64n, bits(I.wrapping_add(a, b))), negative_is_sign_bit(I.wrapping_add(a, b))) :
    {(Bool.not(Bool.xor(top(64n, bits(a)), top(64n, bits(b)))) && Bool.xor(top(64n, bits(a)), _)) ==
      (Bool.not(Bool.xor(top(64n, bits(a)), top(64n, bits(b)))) &&
        Bool.xor(top(64n, bits(a)), top(64n, Word.add(64n, bits(a), bits(b))))) : Bool}
  Equal.cong(Word(64n), Bool,
    w => Bool.not(Bool.xor(top(64n, bits(a)), top(64n, bits(b)))) && Bool.xor(top(64n, bits(a)), top(64n, w)),
    bits(I.wrapping_add(a, b)), Word.add(64n, bits(a), bits(b)), wrapping_add_is_full_word_add(a, b))

law fitting_add_is_integer_addition:
  for +a: V.Int64
  for +b: V.Int64
  for fits: {I.add_overflow(a, b) == False{} : Bool}
  IntegerSum(integer(a), integer(b), integer(I.wrapping_add(a, b)))
def fitting_add_is_integer_addition(a, b, fits):
  word_fits = Equal.trans(Bool,
    Bool.not(Bool.xor(top(64n, bits(a)), top(64n, bits(b)))) && Bool.xor(top(64n, bits(a)), top(64n, Word.add(64n, bits(a), bits(b)))),
    I.add_overflow(a, b), False{}, Equal.sym(Bool, I.add_overflow(a, b),
      Bool.not(Bool.xor(top(64n, bits(a)), top(64n, bits(b)))) && Bool.xor(top(64n, bits(a)), top(64n, Word.add(64n, bits(a), bits(b)))),
      add_overflow_is_word_sign_overflow(a, b)), fits)
  balance = signed_carry_balance(63n, bits(a), bits(b), False{}, word_fits)
  scaled = scale_carry_balance(64n, top(64n, bits(a)), top(64n, bits(b)),
    top(64n, Word.add(64n, bits(a), bits(b))), S.carry(64n, bits(a), bits(b), False{}), balance)
  exact = Equal.trans(Nat,
    Nat.add(Nat.add(unsigned(a), unsigned(b)), spill(64n, top(64n, Word.add(64n, bits(a), bits(b))))),
    Nat.add(Nat.add(unsigned(I.wrapping_add(a, b)), spill(64n, S.carry(64n, bits(a), bits(b), False{}))), spill(64n, top(64n, Word.add(64n, bits(a), bits(b))))),
    Nat.add(unsigned(I.wrapping_add(a, b)), Nat.add(spill(64n, top(64n, bits(a))), spill(64n, top(64n, bits(b))))),
    Equal.cong(Nat, Nat, x => Nat.add(x, spill(64n, top(64n, Word.add(64n, bits(a), bits(b))))),
      Nat.add(unsigned(a), unsigned(b)), Nat.add(unsigned(I.wrapping_add(a, b)), spill(64n, S.carry(64n, bits(a), bits(b), False{}))), wrapping_add_natural(a, b)),
    Equal.trans(Nat,
      Nat.add(Nat.add(unsigned(I.wrapping_add(a, b)), spill(64n, S.carry(64n, bits(a), bits(b), False{}))), spill(64n, top(64n, Word.add(64n, bits(a), bits(b))))),
      Nat.add(unsigned(I.wrapping_add(a, b)), Nat.add(spill(64n, S.carry(64n, bits(a), bits(b), False{})), spill(64n, top(64n, Word.add(64n, bits(a), bits(b)))))),
      Nat.add(unsigned(I.wrapping_add(a, b)), Nat.add(spill(64n, top(64n, bits(a))), spill(64n, top(64n, bits(b))))),
      add_associative(unsigned(I.wrapping_add(a, b)), spill(64n, S.carry(64n, bits(a), bits(b), False{})), spill(64n, top(64n, Word.add(64n, bits(a), bits(b))))),
      Equal.cong(Nat, Nat, x => Nat.add(unsigned(I.wrapping_add(a, b)), x),
        Nat.add(spill(64n, S.carry(64n, bits(a), bits(b), False{})), spill(64n, top(64n, Word.add(64n, bits(a), bits(b))))),
        Nat.add(spill(64n, top(64n, bits(a))), spill(64n, top(64n, bits(b)))), scaled)))
  %Equal.sym(Word(64n), bits(I.wrapping_add(a, b)), Word.add(64n, bits(a), bits(b)), wrapping_add_is_full_word_add(a, b)) :
    {Nat.add(Nat.add(unsigned(a), unsigned(b)), spill(64n, top(64n, _))) ==
      Nat.add(unsigned(I.wrapping_add(a, b)), Nat.add(spill(64n, top(64n, bits(a))), spill(64n, top(64n, bits(b))))) : Nat}
  exact

def predecessor(n: Nat) -> Nat:
  match n:
    case 0n: 0n
    case 1n+p: p

law add_left_cancel:
  for +p: Nat
  for +a: Nat
  for +b: Nat
  for same: {Nat.add(p, a) == Nat.add(p, b) : Nat}
  {a == b : Nat}
def add_left_cancel(p, a, b, same):
  match p:
    case 0n: same
    case 1n+k:
      add_left_cancel(k, a, b,
        Equal.cong(Nat, Nat, predecessor, 1n+Nat.add(k, a), 1n+Nat.add(k, b), same))

law modulus_is_positive:
  for +n: Nat
  {nat_zero(modulus(n)) == False{} : Bool}
def modulus_is_positive(n):
  {==}

law doubled_sum_zero:
  for +n: Nat
  {nat_zero(Nat.add(n, n)) == nat_zero(n) : Bool}
def doubled_sum_zero(n):
  match n:
    case 0n: {==}
    case 1n+p: {==}

type Multiple is Data:
  ZeroTimes{}
  Once{}
  Twice{}

def radix_times(+n: Nat, k: Multiple) -> Nat:
  match k:
    case ZeroTimes{}: 0n
    case Once{}: modulus(n)
    case Twice{}: Nat.add(modulus(n), modulus(n))

def coefficient(k: Multiple) -> Nat:
  match k:
    case ZeroTimes{}: 0n
    case Once{}: 1n
    case Twice{}: 2n

def count_bits(a: Bool, b: Bool) -> Multiple:
  match a b:
    case False{} False{}: ZeroTimes{}
    case False{} True{}: Once{}
    case True{} False{}: Once{}
    case True{} True{}: Twice{}

law count_bits_natural:
  for +a: Bool
  for +b: Bool
  {coefficient(count_bits(a, b)) == Nat.add(bit(a), bit(b)) : Nat}
def count_bits_natural(a, b):
  match a b:
    case False{} False{}: {==}
    case False{} True{}: {==}
    case True{} False{}: {==}
    case True{} True{}: {==}

law spill_pair:
  for +n: Nat
  for +a: Bool
  for +b: Bool
  {Nat.add(spill(n, a), spill(n, b)) == radix_times(n, count_bits(a, b)) : Nat}
def spill_pair(n, a, b):
  match a b:
    case False{} False{}: {==}
    case False{} True{}: {==}
    case True{} False{}: add_zero_right(modulus(n))
    case True{} True{}: {==}

# Distinct 0, 1, and 2 multiples of the positive mathematical radix remain distinct.
law small_multiple_injective:
  for +n: Nat
  for +a: Multiple
  for +b: Multiple
  for positive: {nat_zero(modulus(n)) == False{} : Bool}
  for same: {radix_times(n, a) == radix_times(n, b) : Nat}
  {coefficient(a) == coefficient(b) : Nat}
def small_multiple_injective(n, a, b, positive, same):
  match a b:
    case ZeroTimes{} ZeroTimes{}: {==}
    case Once{} Once{}: {==}
    case Twice{} Twice{}: {==}
    case Once{} ZeroTimes{}:
      F.absurd_boolean({1n == 0n : Nat},
        Equal.trans(Bool, False{}, nat_zero(modulus(n)), True{}, Equal.sym(Bool, nat_zero(modulus(n)), False{}, positive),
          Equal.cong(Nat, Bool, nat_zero, modulus(n), 0n, same)))
    case ZeroTimes{} Once{}:
      F.absurd_boolean({0n == 1n : Nat},
        Equal.trans(Bool, False{}, nat_zero(modulus(n)), True{}, Equal.sym(Bool, nat_zero(modulus(n)), False{}, positive),
          Equal.cong(Nat, Bool, nat_zero, modulus(n), 0n, Equal.sym(Nat, 0n, modulus(n), same))))
    case Twice{} ZeroTimes{}:
      F.absurd_boolean({2n == 0n : Nat},
        Equal.trans(Bool, False{}, nat_zero(modulus(n)), True{}, Equal.sym(Bool, nat_zero(modulus(n)), False{}, positive),
          Equal.trans(Bool, nat_zero(modulus(n)), nat_zero(Nat.add(modulus(n), modulus(n))), True{},
            Equal.sym(Bool, nat_zero(Nat.add(modulus(n), modulus(n))), nat_zero(modulus(n)), doubled_sum_zero(modulus(n))),
            Equal.cong(Nat, Bool, nat_zero, Nat.add(modulus(n), modulus(n)), 0n, same))))
    case ZeroTimes{} Twice{}:
      F.absurd_boolean({0n == 2n : Nat},
        Equal.trans(Bool, False{}, nat_zero(modulus(n)), True{}, Equal.sym(Bool, nat_zero(modulus(n)), False{}, positive),
          Equal.trans(Bool, nat_zero(modulus(n)), nat_zero(Nat.add(modulus(n), modulus(n))), True{},
            Equal.sym(Bool, nat_zero(Nat.add(modulus(n), modulus(n))), nat_zero(modulus(n)), doubled_sum_zero(modulus(n))),
            Equal.cong(Nat, Bool, nat_zero, Nat.add(modulus(n), modulus(n)), 0n, Equal.sym(Nat, 0n, Nat.add(modulus(n), modulus(n)), same)))))
    case Twice{} Once{}:
      F.absurd_boolean({2n == 1n : Nat},
        Equal.trans(Bool, False{}, nat_zero(modulus(n)), True{}, Equal.sym(Bool, nat_zero(modulus(n)), False{}, positive),
          Equal.cong(Nat, Bool, nat_zero, modulus(n), 0n,
            add_left_cancel(modulus(n), modulus(n), 0n, Equal.trans(Nat, Nat.add(modulus(n), modulus(n)), modulus(n), Nat.add(modulus(n), 0n), same,
              Equal.sym(Nat, Nat.add(modulus(n), 0n), modulus(n), add_zero_right(modulus(n))))))))
    case Once{} Twice{}:
      F.absurd_boolean({1n == 2n : Nat},
        Equal.trans(Bool, False{}, nat_zero(modulus(n)), True{}, Equal.sym(Bool, nat_zero(modulus(n)), False{}, positive),
          Equal.cong(Nat, Bool, nat_zero, modulus(n), 0n,
            Equal.sym(Nat, 0n, modulus(n), add_left_cancel(modulus(n), 0n, modulus(n),
              Equal.trans(Nat, Nat.add(modulus(n), 0n), modulus(n), Nat.add(modulus(n), modulus(n)), add_zero_right(modulus(n)), same))))))

law bit_sum_commutative:
  for +a: Bool
  for +b: Bool
  {Nat.add(bit(a), bit(b)) == Nat.add(bit(b), bit(a)) : Nat}
def bit_sum_commutative(a, b):
  match a b:
    case False{} False{}: {==}
    case False{} True{}: {==}
    case True{} False{}: {==}
    case True{} True{}: {==}

law scaled_balance_reflects_sign_count:
  for +n: Nat
  for +a: Bool
  for +b: Bool
  for +r: Bool
  for +c: Bool
  for balance: {Nat.add(spill(n, c), spill(n, r)) == Nat.add(spill(n, a), spill(n, b)) : Nat}
  {Nat.add(bit(a), bit(b)) == Nat.add(bit(r), bit(c)) : Nat}
def scaled_balance_reflects_sign_count(n, a, b, r, c, balance):
  scaled = Equal.trans(Nat, radix_times(n, count_bits(c, r)),
    Nat.add(spill(n, c), spill(n, r)), radix_times(n, count_bits(a, b)),
    Equal.sym(Nat, Nat.add(spill(n, c), spill(n, r)), radix_times(n, count_bits(c, r)), spill_pair(n, c, r)),
    Equal.trans(Nat, Nat.add(spill(n, c), spill(n, r)), Nat.add(spill(n, a), spill(n, b)),
      radix_times(n, count_bits(a, b)), balance, spill_pair(n, a, b)))
  counts = small_multiple_injective(n, count_bits(c, r), count_bits(a, b), modulus_is_positive(n), scaled)
  Equal.trans(Nat, Nat.add(bit(a), bit(b)), coefficient(count_bits(a, b)), Nat.add(bit(r), bit(c)),
    Equal.sym(Nat, coefficient(count_bits(a, b)), Nat.add(bit(a), bit(b)), count_bits_natural(a, b)),
    Equal.trans(Nat, coefficient(count_bits(a, b)), coefficient(count_bits(c, r)), Nat.add(bit(r), bit(c)),
      Equal.sym(Nat, coefficient(count_bits(c, r)), coefficient(count_bits(a, b)), counts),
      Equal.trans(Nat, coefficient(count_bits(c, r)), Nat.add(bit(c), bit(r)), Nat.add(bit(r), bit(c)),
        count_bits_natural(c, r), bit_sum_commutative(c, r))))

law sign_balance_implies_fitting:
  for +n: Nat
  for +a: Word(1n+n)
  for +b: Word(1n+n)
  for +c: Bool
  for balance: {Nat.add(bit(top(1n+n, a)), bit(top(1n+n, b))) ==
    Nat.add(bit(top(1n+n, Word.adc(1n+n, a, b, False{}, c))), bit(S.carry(1n+n, a, b, c))) : Nat}
  {(Bool.not(Bool.xor(top(1n+n, a), top(1n+n, b))) &&
    Bool.xor(top(1n+n, a), top(1n+n, Word.adc(1n+n, a, b, False{}, c)))) == False{} : Bool}
def sign_balance_implies_fitting(n, a, b, c, balance):
  match n:
    case 0n:
      match a b c:
        case WCon{False{}, WNil{}} WCon{False{}, WNil{}} False{}:
          {==}
        case WCon{False{}, WNil{}} WCon{False{}, WNil{}} True{}:
          F.absurd_boolean({True{} == False{} : Bool}, Equal.cong(Nat, Bool, v => Bool.not(Nat.is_eq(v, 0n)), 0n, 1n, balance))
        case WCon{False{}, WNil{}} WCon{True{}, WNil{}} False{}:
          {==}
        case WCon{False{}, WNil{}} WCon{True{}, WNil{}} True{}:
          {==}
        case WCon{True{}, WNil{}} WCon{False{}, WNil{}} False{}:
          {==}
        case WCon{True{}, WNil{}} WCon{False{}, WNil{}} True{}:
          {==}
        case WCon{True{}, WNil{}} WCon{True{}, WNil{}} False{}:
          F.absurd_boolean({True{} == False{} : Bool}, Equal.cong(Nat, Bool, v => Bool.not(Nat.is_eq(v, 2n)), 2n, 1n, balance))
        case WCon{True{}, WNil{}} WCon{True{}, WNil{}} True{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{False{}, at} WCon{False{}, bt} False{}:
          sign_balance_implies_fitting(p, at, bt, False{}, balance)
        case WCon{False{}, at} WCon{False{}, bt} True{}:
          sign_balance_implies_fitting(p, at, bt, False{}, balance)
        case WCon{False{}, at} WCon{True{}, bt} False{}:
          sign_balance_implies_fitting(p, at, bt, False{}, balance)
        case WCon{False{}, at} WCon{True{}, bt} True{}:
          sign_balance_implies_fitting(p, at, bt, True{}, balance)
        case WCon{True{}, at} WCon{False{}, bt} False{}:
          sign_balance_implies_fitting(p, at, bt, False{}, balance)
        case WCon{True{}, at} WCon{False{}, bt} True{}:
          sign_balance_implies_fitting(p, at, bt, True{}, balance)
        case WCon{True{}, at} WCon{True{}, bt} False{}:
          sign_balance_implies_fitting(p, at, bt, True{}, balance)
        case WCon{True{}, at} WCon{True{}, bt} True{}:
          sign_balance_implies_fitting(p, at, bt, True{}, balance)

# Converse: a wrapped result denotes the exact signed mathematical sum only
# when the implementation's checked-add test accepts it.
law integer_addition_implies_fitting:
  for +a: V.Int64
  for +b: V.Int64
  for exact: IntegerSum(integer(a), integer(b), integer(I.wrapping_add(a, b)))
  {I.add_overflow(a, b) == False{} : Bool}
def integer_addition_implies_fitting(a, b, exact):
  rewritten = Equal.trans(Nat,
    Nat.add(Nat.add(unsigned(I.wrapping_add(a, b)), spill(64n, S.carry(64n, bits(a), bits(b), False{}))), spill(64n, top(64n, bits(I.wrapping_add(a, b))))),
    Nat.add(Nat.add(unsigned(a), unsigned(b)), spill(64n, top(64n, bits(I.wrapping_add(a, b))))),
    Nat.add(unsigned(I.wrapping_add(a, b)), Nat.add(spill(64n, top(64n, bits(a))), spill(64n, top(64n, bits(b))))),
    Equal.cong(Nat, Nat, x => Nat.add(x, spill(64n, top(64n, bits(I.wrapping_add(a, b))))),
      Nat.add(unsigned(I.wrapping_add(a, b)), spill(64n, S.carry(64n, bits(a), bits(b), False{}))),
      Nat.add(unsigned(a), unsigned(b)),
      Equal.sym(Nat, Nat.add(unsigned(a), unsigned(b)),
        Nat.add(unsigned(I.wrapping_add(a, b)), spill(64n, S.carry(64n, bits(a), bits(b), False{}))), wrapping_add_natural(a, b))), exact)
  associated = Equal.trans(Nat,
    Nat.add(unsigned(I.wrapping_add(a, b)), Nat.add(spill(64n, S.carry(64n, bits(a), bits(b), False{})), spill(64n, top(64n, bits(I.wrapping_add(a, b)))))),
    Nat.add(Nat.add(unsigned(I.wrapping_add(a, b)), spill(64n, S.carry(64n, bits(a), bits(b), False{}))), spill(64n, top(64n, bits(I.wrapping_add(a, b))))),
    Nat.add(unsigned(I.wrapping_add(a, b)), Nat.add(spill(64n, top(64n, bits(a))), spill(64n, top(64n, bits(b))))),
    Equal.sym(Nat,
      Nat.add(Nat.add(unsigned(I.wrapping_add(a, b)), spill(64n, S.carry(64n, bits(a), bits(b), False{}))), spill(64n, top(64n, bits(I.wrapping_add(a, b))))),
      Nat.add(unsigned(I.wrapping_add(a, b)), Nat.add(spill(64n, S.carry(64n, bits(a), bits(b), False{})), spill(64n, top(64n, bits(I.wrapping_add(a, b)))))),
      add_associative(unsigned(I.wrapping_add(a, b)), spill(64n, S.carry(64n, bits(a), bits(b), False{})), spill(64n, top(64n, bits(I.wrapping_add(a, b)))))), rewritten)
  scaled = add_left_cancel(unsigned(I.wrapping_add(a, b)),
    Nat.add(spill(64n, S.carry(64n, bits(a), bits(b), False{})), spill(64n, top(64n, bits(I.wrapping_add(a, b))))),
    Nat.add(spill(64n, top(64n, bits(a))), spill(64n, top(64n, bits(b)))), associated)
  count = scaled_balance_reflects_sign_count(64n, top(64n, bits(a)), top(64n, bits(b)), top(64n, bits(I.wrapping_add(a, b))), S.carry(64n, bits(a), bits(b), False{}), scaled)
  full_count = Equal.trans(Nat,
    Nat.add(bit(top(64n, bits(a))), bit(top(64n, bits(b)))),
    Nat.add(bit(top(64n, bits(I.wrapping_add(a, b)))), bit(S.carry(64n, bits(a), bits(b), False{}))),
    Nat.add(bit(top(64n, Word.add(64n, bits(a), bits(b)))), bit(S.carry(64n, bits(a), bits(b), False{}))), count,
    Equal.cong(Word(64n), Nat, w => Nat.add(bit(top(64n, w)), bit(S.carry(64n, bits(a), bits(b), False{}))),
      bits(I.wrapping_add(a, b)), Word.add(64n, bits(a), bits(b)), wrapping_add_is_full_word_add(a, b)))
  Equal.trans(Bool, I.add_overflow(a, b),
    Bool.not(Bool.xor(top(64n, bits(a)), top(64n, bits(b)))) && Bool.xor(top(64n, bits(a)), top(64n, Word.add(64n, bits(a), bits(b)))), False{},
    add_overflow_is_word_sign_overflow(a, b), sign_balance_implies_fitting(63n, bits(a), bits(b), False{}, full_count))

law add_right_successor:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}
def add_right_successor(a, b):
  match a:
    case 0n: {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 1n+b), 1n+Nat.add(p, b), add_right_successor(p, b))

law add_commutative:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}
def add_commutative(a, b):
  match a:
    case 0n: Equal.sym(Nat, Nat.add(b, 0n), b, add_zero_right(b))
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p),
        Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, b), Nat.add(b, p), add_commutative(p, b)),
        Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), add_right_successor(b, p)))

law add_right_cancel:
  for +p: Nat
  for +a: Nat
  for +b: Nat
  for same: {Nat.add(a, p) == Nat.add(b, p) : Nat}
  {a == b : Nat}
def add_right_cancel(p, a, b, same):
  add_left_cancel(p, a, b,
    Equal.trans(Nat, Nat.add(p, a), Nat.add(a, p), Nat.add(p, b), add_commutative(p, a),
      Equal.trans(Nat, Nat.add(a, p), Nat.add(b, p), Nat.add(p, b), same, add_commutative(b, p))))

law complement_value:
  for +n: Nat
  for +w: Word(n)
  {Nat.add(Word.to_nat(n, w), Word.to_nat(n, Word.not(n, w))) == maximum_value(n) : Nat}
def complement_value(n, w):
  match n:
    case 0n: {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          Equal.trans(Nat,
            Nat.add(Nat.double(Word.to_nat(p, t)), 1n+Nat.double(Word.to_nat(p, Word.not(p, t)))),
            1n+Nat.add(Nat.double(Word.to_nat(p, t)), Nat.double(Word.to_nat(p, Word.not(p, t)))),
            1n+Nat.double(maximum_value(p)),
            add_right_successor(Nat.double(Word.to_nat(p, t)), Nat.double(Word.to_nat(p, Word.not(p, t)))),
            Equal.trans(Nat,
              1n+Nat.add(Nat.double(Word.to_nat(p, t)), Nat.double(Word.to_nat(p, Word.not(p, t)))),
              1n+Nat.double(Nat.add(Word.to_nat(p, t), Word.to_nat(p, Word.not(p, t)))), 1n+Nat.double(maximum_value(p)),
              Equal.cong(Nat, Nat, v => 1n+v,
                Nat.add(Nat.double(Word.to_nat(p, t)), Nat.double(Word.to_nat(p, Word.not(p, t)))),
                Nat.double(Nat.add(Word.to_nat(p, t), Word.to_nat(p, Word.not(p, t)))),
                Equal.sym(Nat, Nat.double(Nat.add(Word.to_nat(p, t), Word.to_nat(p, Word.not(p, t)))),
                  Nat.add(Nat.double(Word.to_nat(p, t)), Nat.double(Word.to_nat(p, Word.not(p, t)))), double_sum(Word.to_nat(p, t), Word.to_nat(p, Word.not(p, t))))),
              Equal.cong(Nat, Nat, v => 1n+Nat.double(v),
                Nat.add(Word.to_nat(p, t), Word.to_nat(p, Word.not(p, t))), maximum_value(p), complement_value(p, t))))
        case WCon{True{}, +t}:
          Equal.trans(Nat,
            1n+Nat.add(Nat.double(Word.to_nat(p, t)), Nat.double(Word.to_nat(p, Word.not(p, t)))),
            1n+Nat.double(Nat.add(Word.to_nat(p, t), Word.to_nat(p, Word.not(p, t)))), 1n+Nat.double(maximum_value(p)),
            Equal.cong(Nat, Nat, v => 1n+v,
              Nat.add(Nat.double(Word.to_nat(p, t)), Nat.double(Word.to_nat(p, Word.not(p, t)))),
              Nat.double(Nat.add(Word.to_nat(p, t), Word.to_nat(p, Word.not(p, t)))),
              Equal.sym(Nat, Nat.double(Nat.add(Word.to_nat(p, t), Word.to_nat(p, Word.not(p, t)))),
                Nat.add(Nat.double(Word.to_nat(p, t)), Nat.double(Word.to_nat(p, Word.not(p, t)))), double_sum(Word.to_nat(p, t), Word.to_nat(p, Word.not(p, t))))),
            Equal.cong(Nat, Nat, v => 1n+Nat.double(v),
              Nat.add(Word.to_nat(p, t), Word.to_nat(p, Word.not(p, t))), maximum_value(p), complement_value(p, t)))

law strict_self_plus_gap:
  for +a: Nat
  for +b: Nat
  {Nat.is_lt(a, 1n+Nat.add(a, b)) == True{} : Bool}
def strict_self_plus_gap(a, b):
  match a:
    case 0n: {==}
    case 1n+p: strict_self_plus_gap(p, b)

# Constructive strict order: the ceiling is one plus the value and a gap.
# Keeping the proof as an indexed proposition avoids materializing 2^64 as a
# unary runtime comparison operand in the official frontend.
type Bound<-width: Nat, -value: Nat> is Type:
  Bound{gap: Nat, exact: {modulus(width) == 1n+Nat.add(value, gap) : Nat}}

law word_value_is_bounded:
  for +n: Nat
  for +w: Word(n)
  Bound<n, Word.to_nat(n, w)>
def word_value_is_bounded(n, w):
  Bound{Word.to_nat(n, Word.not(n, w)),
    Equal.cong(Nat, Nat, v => 1n+v, maximum_value(n), Nat.add(Word.to_nat(n, w), Word.to_nat(n, Word.not(n, w))),
      Equal.sym(Nat, Nat.add(Word.to_nat(n, w), Word.to_nat(n, Word.not(n, w))), maximum_value(n), complement_value(n, w)))}

law strict_irreflexive:
  for +n: Nat
  {Nat.is_lt(n, n) == False{} : Bool}
def strict_irreflexive(n):
  match n:
    case 0n: {==}
    case 1n+p: strict_irreflexive(p)

law strict_successor_right:
  for +x: Nat
  for +y: Nat
  for less: {Nat.is_lt(x, y) == True{} : Bool}
  {Nat.is_lt(x, 1n+y) == True{} : Bool}
def strict_successor_right(x, y, less):
  match x y:
    case 0n _: {==}
    case 1n+p 0n: F.absurd_boolean({Nat.is_lt(1n+p, 1n) == True{} : Bool}, less)
    case 1n+p 1n+q: strict_successor_right(p, q, less)

law strict_add_right:
  for +x: Nat
  for +y: Nat
  for +m: Nat
  for less: {Nat.is_lt(x, m) == True{} : Bool}
  {Nat.is_lt(x, Nat.add(y, m)) == True{} : Bool}
def strict_add_right(x, y, m, less):
  match y:
    case 0n: less
    case 1n+p: strict_successor_right(x, Nat.add(p, m), strict_add_right(x, p, m, less))

# A value below a radix cannot equal a value with at least one whole radix.
def contradict_radix_gap(width: Nat, +x: Nat, +y: Nat,
  less: Bound<width, x>, same: {x == Nat.add(y, modulus(width)) : Nat}) -> {False{} == True{} : Bool}:
  match less:
    case Bound{+gap, ceiling}:
      larger = Equal.trans(Nat, x, Nat.add(y, modulus(width)), Nat.add(y, 1n+Nat.add(x, gap)), same,
        Equal.cong(Nat, Nat, n => Nat.add(y, n), modulus(width), 1n+Nat.add(x, gap), ceiling))
      Equal.trans(Bool, False{}, Nat.is_lt(x, x), True{},
        Equal.sym(Bool, Nat.is_lt(x, x), False{}, strict_irreflexive(x)),
        Equal.trans(Bool, Nat.is_lt(x, x), Nat.is_lt(x, Nat.add(y, 1n+Nat.add(x, gap))), True{},
          Equal.cong(Nat, Bool, n => Nat.is_lt(x, n), x, Nat.add(y, 1n+Nat.add(x, gap)), larger),
          strict_add_right(x, y, 1n+Nat.add(x, gap), strict_self_plus_gap(x, gap))))

# Uniqueness of residues for the 0..2 radix multiples arising in two's complement.
law bounded_residue_unique:
  for +width: Nat
  for +x: Nat
  for +y: Nat
  for +a: Multiple
  for +b: Multiple
  for lx: Bound<width, x>
  for ly: Bound<width, y>
  for same: {Nat.add(x, radix_times(width, a)) == Nat.add(y, radix_times(width, b)) : Nat}
  L.E<{x == y : Nat}, {coefficient(a) == coefficient(b) : Nat}>
def bounded_residue_unique(width, x, y, a, b, lx, ly, same):
  match a b:
    case ZeroTimes{} ZeroTimes{}:
      L.Both{(Equal.trans(Nat, x, Nat.add(x, 0n), y,
        Equal.sym(Nat, Nat.add(x, 0n), x, add_zero_right(x)),
        Equal.trans(Nat, Nat.add(x, 0n), Nat.add(y, 0n), y, same, add_zero_right(y)))), {==}}
    case Once{} Once{}: L.Both{add_right_cancel(modulus(width), x, y, same), {==}}
    case Twice{} Twice{}: L.Both{add_right_cancel(Nat.add(modulus(width), modulus(width)), x, y, same), {==}}
    case ZeroTimes{} Once{}:
      F.absurd_boolean(L.E<{x == y : Nat}, {coefficient(a) == coefficient(b) : Nat}>, contradict_radix_gap(width, x, y, lx,
        Equal.trans(Nat, x, Nat.add(x, 0n), Nat.add(y, modulus(width)), Equal.sym(Nat, Nat.add(x, 0n), x, add_zero_right(x)), same)))
    case Once{} ZeroTimes{}:
      F.absurd_boolean(L.E<{x == y : Nat}, {coefficient(a) == coefficient(b) : Nat}>, contradict_radix_gap(width, y, x, ly,
        Equal.sym(Nat, Nat.add(x, modulus(width)), y,
          Equal.trans(Nat, Nat.add(x, modulus(width)), Nat.add(y, 0n), y, same, add_zero_right(y)))))
    case ZeroTimes{} Twice{}:
      F.absurd_boolean(L.E<{x == y : Nat}, {coefficient(a) == coefficient(b) : Nat}>, contradict_radix_gap(width, x, Nat.add(y, modulus(width)), lx,
        Equal.trans(Nat, x, Nat.add(x, 0n), Nat.add(Nat.add(y, modulus(width)), modulus(width)), Equal.sym(Nat, Nat.add(x, 0n), x, add_zero_right(x)),
          Equal.trans(Nat, Nat.add(x, 0n), Nat.add(y, Nat.add(modulus(width), modulus(width))), Nat.add(Nat.add(y, modulus(width)), modulus(width)), same,
            Equal.sym(Nat, Nat.add(Nat.add(y, modulus(width)), modulus(width)), Nat.add(y, Nat.add(modulus(width), modulus(width))), add_associative(y, modulus(width), modulus(width)))))))
    case Twice{} ZeroTimes{}:
      F.absurd_boolean(L.E<{x == y : Nat}, {coefficient(a) == coefficient(b) : Nat}>, contradict_radix_gap(width, y, Nat.add(x, modulus(width)), ly,
        Equal.trans(Nat, y, Nat.add(y, 0n), Nat.add(Nat.add(x, modulus(width)), modulus(width)), Equal.sym(Nat, Nat.add(y, 0n), y, add_zero_right(y)),
          Equal.trans(Nat, Nat.add(y, 0n), Nat.add(x, Nat.add(modulus(width), modulus(width))), Nat.add(Nat.add(x, modulus(width)), modulus(width)),
            Equal.sym(Nat, Nat.add(x, Nat.add(modulus(width), modulus(width))), Nat.add(y, 0n), same),
            Equal.sym(Nat, Nat.add(Nat.add(x, modulus(width)), modulus(width)), Nat.add(x, Nat.add(modulus(width), modulus(width))), add_associative(x, modulus(width), modulus(width)))))))
    case Once{} Twice{}:
      F.absurd_boolean(L.E<{x == y : Nat}, {coefficient(a) == coefficient(b) : Nat}>, contradict_radix_gap(width, x, y, lx,
        add_right_cancel(modulus(width), x, Nat.add(y, modulus(width)),
          Equal.trans(Nat, Nat.add(x, modulus(width)), Nat.add(y, Nat.add(modulus(width), modulus(width))), Nat.add(Nat.add(y, modulus(width)), modulus(width)), same,
            Equal.sym(Nat, Nat.add(Nat.add(y, modulus(width)), modulus(width)), Nat.add(y, Nat.add(modulus(width), modulus(width))), add_associative(y, modulus(width), modulus(width)))))))
    case Twice{} Once{}:
      F.absurd_boolean(L.E<{x == y : Nat}, {coefficient(a) == coefficient(b) : Nat}>, contradict_radix_gap(width, y, x, ly,
        add_right_cancel(modulus(width), y, Nat.add(x, modulus(width)),
          Equal.trans(Nat, Nat.add(y, modulus(width)), Nat.add(x, Nat.add(modulus(width), modulus(width))), Nat.add(Nat.add(x, modulus(width)), modulus(width)),
            Equal.sym(Nat, Nat.add(x, Nat.add(modulus(width), modulus(width))), Nat.add(y, modulus(width)), same),
            Equal.sym(Nat, Nat.add(Nat.add(x, modulus(width)), modulus(width)), Nat.add(x, Nat.add(modulus(width), modulus(width))), add_associative(x, modulus(width), modulus(width)))))))

def of_bits(+w: Word(64n)) -> V.Int64:
  V.Int64{U32{C64.high(32n, 32n, w)}, U32{C64.low(32n, 32n, w)}}

law of_bits_exact:
  for +x: V.Int64
  {of_bits(bits(x)) == x : V.Int64}
def of_bits_exact(x):
  match x:
    case V.Int64{U32{+h}, U32{+l}}:
      %Equal.sym(Word(32n), C64.high(32n, 32n, W.join(32n, 32n, l, h)), h, C64.high_join(32n, 32n, l, h)) :
        {V.Int64{U32{_}, U32{C64.low(32n, 32n, W.join(32n, 32n, l, h))}} == V.Int64{U32{h}, U32{l}} : V.Int64}
      Equal.cong(Word(32n), V.Int64, t => V.Int64{U32{h}, U32{t}},
        C64.low(32n, 32n, W.join(32n, 32n, l, h)), l, C64.low_join(32n, 32n, l, h))

law bits_injective:
  for +a: V.Int64
  for +b: V.Int64
  for same: {bits(a) == bits(b) : Word(64n)}
  {a == b : V.Int64}
def bits_injective(a, b, same):
  Equal.trans(V.Int64, a, of_bits(bits(a)), b,
    Equal.sym(V.Int64, of_bits(bits(a)), a, of_bits_exact(a)),
    Equal.trans(V.Int64, of_bits(bits(a)), of_bits(bits(b)), b,
      Equal.cong(Word(64n), V.Int64, w => of_bits(w), bits(a), bits(b), same), of_bits_exact(b)))

# Every representable signed sum must have the actual wrapped bit pattern.
# This uses unsigned value bounds and residue uniqueness, not a sign heuristic.
def ResidueData(+a: V.Int64, +b: V.Int64, +r: V.Int64) -> Type:
  L.E<{unsigned(I.wrapping_add(a, b)) == unsigned(r) : Nat},
    {coefficient(count_bits(S.carry(64n, bits(a), bits(b), False{}), top(64n, bits(r)))) ==
      coefficient(count_bits(top(64n, bits(a)), top(64n, bits(b)))) : Nat}>

law integer_sum_residues:
  for +a: V.Int64
  for +b: V.Int64
  for +r: V.Int64
  for exact: IntegerSum(integer(a), integer(b), integer(r))
  ResidueData(a, b, r)
def integer_sum_residues(a, b, r, exact):
  rewritten = Equal.trans(Nat,
    Nat.add(Nat.add(unsigned(I.wrapping_add(a, b)), spill(64n, S.carry(64n, bits(a), bits(b), False{}))), spill(64n, top(64n, bits(r)))),
    Nat.add(Nat.add(unsigned(a), unsigned(b)), spill(64n, top(64n, bits(r)))),
    Nat.add(unsigned(r), Nat.add(spill(64n, top(64n, bits(a))), spill(64n, top(64n, bits(b))))),
    Equal.cong(Nat, Nat, x => Nat.add(x, spill(64n, top(64n, bits(r)))),
      Nat.add(unsigned(I.wrapping_add(a, b)), spill(64n, S.carry(64n, bits(a), bits(b), False{}))),
      Nat.add(unsigned(a), unsigned(b)),
      Equal.sym(Nat, Nat.add(unsigned(a), unsigned(b)),
        Nat.add(unsigned(I.wrapping_add(a, b)), spill(64n, S.carry(64n, bits(a), bits(b), False{}))), wrapping_add_natural(a, b))), exact)
  associated = Equal.trans(Nat,
    Nat.add(unsigned(I.wrapping_add(a, b)), Nat.add(spill(64n, S.carry(64n, bits(a), bits(b), False{})), spill(64n, top(64n, bits(r))))),
    Nat.add(Nat.add(unsigned(I.wrapping_add(a, b)), spill(64n, S.carry(64n, bits(a), bits(b), False{}))), spill(64n, top(64n, bits(r)))),
    Nat.add(unsigned(r), Nat.add(spill(64n, top(64n, bits(a))), spill(64n, top(64n, bits(b))))),
    Equal.sym(Nat,
      Nat.add(Nat.add(unsigned(I.wrapping_add(a, b)), spill(64n, S.carry(64n, bits(a), bits(b), False{}))), spill(64n, top(64n, bits(r)))),
      Nat.add(unsigned(I.wrapping_add(a, b)), Nat.add(spill(64n, S.carry(64n, bits(a), bits(b), False{})), spill(64n, top(64n, bits(r))))),
      add_associative(unsigned(I.wrapping_add(a, b)), spill(64n, S.carry(64n, bits(a), bits(b), False{})), spill(64n, top(64n, bits(r))))), rewritten)
  multiple = Equal.trans(Nat,
    Nat.add(unsigned(I.wrapping_add(a, b)), radix_times(64n, count_bits(S.carry(64n, bits(a), bits(b), False{}), top(64n, bits(r))))),
    Nat.add(unsigned(I.wrapping_add(a, b)), Nat.add(spill(64n, S.carry(64n, bits(a), bits(b), False{})), spill(64n, top(64n, bits(r))))),
    Nat.add(unsigned(r), radix_times(64n, count_bits(top(64n, bits(a)), top(64n, bits(b))))),
    Equal.cong(Nat, Nat, n => Nat.add(unsigned(I.wrapping_add(a, b)), n),
      radix_times(64n, count_bits(S.carry(64n, bits(a), bits(b), False{}), top(64n, bits(r)))),
      Nat.add(spill(64n, S.carry(64n, bits(a), bits(b), False{})), spill(64n, top(64n, bits(r)))),
      Equal.sym(Nat, Nat.add(spill(64n, S.carry(64n, bits(a), bits(b), False{})), spill(64n, top(64n, bits(r)))),
        radix_times(64n, count_bits(S.carry(64n, bits(a), bits(b), False{}), top(64n, bits(r)))),
        spill_pair(64n, S.carry(64n, bits(a), bits(b), False{}), top(64n, bits(r))))),
    Equal.trans(Nat,
      Nat.add(unsigned(I.wrapping_add(a, b)), Nat.add(spill(64n, S.carry(64n, bits(a), bits(b), False{})), spill(64n, top(64n, bits(r))))),
      Nat.add(unsigned(r), Nat.add(spill(64n, top(64n, bits(a))), spill(64n, top(64n, bits(b))))),
      Nat.add(unsigned(r), radix_times(64n, count_bits(top(64n, bits(a)), top(64n, bits(b))))), associated,
      Equal.cong(Nat, Nat, n => Nat.add(unsigned(r), n),
        Nat.add(spill(64n, top(64n, bits(a))), spill(64n, top(64n, bits(b)))),
        radix_times(64n, count_bits(top(64n, bits(a)), top(64n, bits(b)))), spill_pair(64n, top(64n, bits(a)), top(64n, bits(b))))))
  bounded_residue_unique(64n, unsigned(I.wrapping_add(a, b)), unsigned(r),
    count_bits(S.carry(64n, bits(a), bits(b), False{}), top(64n, bits(r))), count_bits(top(64n, bits(a)), top(64n, bits(b))),
    word_value_is_bounded(64n, bits(I.wrapping_add(a, b))), word_value_is_bounded(64n, bits(r)), multiple)

def candidate_from_residue(+a: V.Int64, +b: V.Int64, +r: V.Int64,
  data: ResidueData(a, b, r)) -> {r == I.wrapping_add(a, b) : V.Int64}:
  match data:
    case L.Both{residue, coefficients}:
      Equal.sym(V.Int64, I.wrapping_add(a, b), r,
        bits_injective(I.wrapping_add(a, b), r, Tags.word_to_nat_injective(64n, bits(I.wrapping_add(a, b)), bits(r), residue)))


law integer_sum_candidate_is_wrapped:
  for +a: V.Int64
  for +b: V.Int64
  for +r: V.Int64
  for exact: IntegerSum(integer(a), integer(b), integer(r))
  {r == I.wrapping_add(a, b) : V.Int64}
def integer_sum_candidate_is_wrapped(a, b, r, exact):
  candidate_from_residue(a, b, r, integer_sum_residues(a, b, r, exact))


def fitting_from_residue(+a: V.Int64, +b: V.Int64, +r: V.Int64,
  data: ResidueData(a, b, r)) -> {I.add_overflow(a, b) == False{} : Bool}:
  match data:
    case L.Both{residue, coefficients}:
      result_bits = Equal.trans(Word(64n), bits(r), bits(I.wrapping_add(a, b)), Word.add(64n, bits(a), bits(b)),
        Equal.sym(Word(64n), bits(I.wrapping_add(a, b)), bits(r),
          Tags.word_to_nat_injective(64n, bits(I.wrapping_add(a, b)), bits(r), residue)), wrapping_add_is_full_word_add(a, b))
      count = Equal.trans(Nat, Nat.add(bit(top(64n, bits(a))), bit(top(64n, bits(b)))),
        coefficient(count_bits(top(64n, bits(a)), top(64n, bits(b)))),
        Nat.add(bit(top(64n, bits(r))), bit(S.carry(64n, bits(a), bits(b), False{}))),
        Equal.sym(Nat, coefficient(count_bits(top(64n, bits(a)), top(64n, bits(b)))),
          Nat.add(bit(top(64n, bits(a))), bit(top(64n, bits(b)))), count_bits_natural(top(64n, bits(a)), top(64n, bits(b)))),
        Equal.trans(Nat, coefficient(count_bits(top(64n, bits(a)), top(64n, bits(b)))),
          coefficient(count_bits(S.carry(64n, bits(a), bits(b), False{}), top(64n, bits(r)))),
          Nat.add(bit(top(64n, bits(r))), bit(S.carry(64n, bits(a), bits(b), False{}))),
          Equal.sym(Nat, coefficient(count_bits(S.carry(64n, bits(a), bits(b), False{}), top(64n, bits(r)))),
            coefficient(count_bits(top(64n, bits(a)), top(64n, bits(b)))), coefficients),
          Equal.trans(Nat, coefficient(count_bits(S.carry(64n, bits(a), bits(b), False{}), top(64n, bits(r)))),
            Nat.add(bit(S.carry(64n, bits(a), bits(b), False{})), bit(top(64n, bits(r)))),
            Nat.add(bit(top(64n, bits(r))), bit(S.carry(64n, bits(a), bits(b), False{}))),
            count_bits_natural(S.carry(64n, bits(a), bits(b), False{}), top(64n, bits(r))),
            bit_sum_commutative(S.carry(64n, bits(a), bits(b), False{}), top(64n, bits(r))))))
      full_count = Equal.trans(Nat, Nat.add(bit(top(64n, bits(a))), bit(top(64n, bits(b)))),
        Nat.add(bit(top(64n, bits(r))), bit(S.carry(64n, bits(a), bits(b), False{}))),
        Nat.add(bit(top(64n, Word.add(64n, bits(a), bits(b)))), bit(S.carry(64n, bits(a), bits(b), False{}))), count,
        Equal.cong(Word(64n), Nat, w => Nat.add(bit(top(64n, w)), bit(S.carry(64n, bits(a), bits(b), False{}))),
          bits(r), Word.add(64n, bits(a), bits(b)), result_bits))
      Equal.trans(Bool, I.add_overflow(a, b),
        Bool.not(Bool.xor(top(64n, bits(a)), top(64n, bits(b)))) && Bool.xor(top(64n, bits(a)), top(64n, Word.add(64n, bits(a), bits(b)))), False{},
        add_overflow_is_word_sign_overflow(a, b), sign_balance_implies_fitting(63n, bits(a), bits(b), False{}, full_count))


law representable_integer_sum_implies_fitting:
  for +a: V.Int64
  for +b: V.Int64
  for +r: V.Int64
  for exact: IntegerSum(integer(a), integer(b), integer(r))
  {I.add_overflow(a, b) == False{} : Bool}
def representable_integer_sum_implies_fitting(a, b, r, exact):
  fitting_from_residue(a, b, r, integer_sum_residues(a, b, r, exact))


# TOTAL, independent mathematical specification: a successful result is exactly
# integer addition; rejection means NO signed64 word represents that sum.
def AdditionCorrect(+a: V.Int64, +b: V.Int64, result: Maybe<&2, V.Int64>) -> Type:
  match result:
    case Some{r}: IntegerSum(integer(a), integer(b), integer(r))
    case None{}: @r: V.Int64 -> IntegerSum(integer(a), integer(b), integer(r)) -> Empty

def addition_case(overflow: Bool, +a: V.Int64, +b: V.Int64,
  exact: {I.add_overflow(a, b) == overflow : Bool}) -> AdditionCorrect(a, b, I.checked(overflow, I.wrapping_add(a, b))):
  match overflow:
    case False{}: fitting_add_is_integer_addition(a, b, exact)
    case True{}:
      r => candidate => F.false_negative_true(
        Equal.trans(Bool, False{}, I.add_overflow(a, b), True{},
          Equal.sym(Bool, I.add_overflow(a, b), False{}, representable_integer_sum_implies_fitting(a, b, r, candidate)), exact))

law checked_add_is_integer_addition:
  for +a: V.Int64
  for +b: V.Int64
  AdditionCorrect(a, b, I.add(a, b))
def checked_add_is_integer_addition(a, b):
  addition_case(I.add_overflow(a, b), a, b, {==})
