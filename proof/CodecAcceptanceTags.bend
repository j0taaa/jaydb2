# Injectivity of actual Word/U32 to Nat conversion, without axioms.
# Supports tag extraction; assumes no codec property.
import Base

def impossible(-A: Type, e: Empty) -> A:
  match e:

def half(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n:
      0n
    case 2n+p:
      1n+half(p)

def parity(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n:
      True{}
    case 2n+p:
      parity(p)

law half_double:
  for +n: Nat
  {half(Nat.double(n)) == n : Nat}
def half_double(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, r => 1n+r, half(Nat.double(p)), p, half_double(p))

law half_successor_double:
  for +n: Nat
  {half(1n+Nat.double(n)) == n : Nat}
def half_successor_double(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, r => 1n+r, half(1n+Nat.double(p)), p,
        half_successor_double(p))

law parity_double:
  for n: Nat
  {parity(Nat.double(n)) == False{} : Bool}
def parity_double(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      parity_double(p)

law parity_successor_double:
  for n: Nat
  {parity(1n+Nat.double(n)) == True{} : Bool}
def parity_successor_double(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      parity_successor_double(p)

law double_injective:
  for +a: Nat
  for +b: Nat
  for e: {Nat.double(a) == Nat.double(b) : Nat}
  {a == b : Nat}
def double_injective(a, b, e):
  Equal.trans(Nat, a, half(Nat.double(a)), b,
    Equal.sym(Nat, half(Nat.double(a)), a, half_double(a)),
    Equal.trans(Nat, half(Nat.double(a)), half(Nat.double(b)), b,
      Equal.cong(Nat, Nat, r => half(r), Nat.double(a), Nat.double(b), e),
      half_double(b)))

law successor_double_injective:
  for +a: Nat
  for +b: Nat
  for e: {1n+Nat.double(a) == 1n+Nat.double(b) : Nat}
  {a == b : Nat}
def successor_double_injective(a, b, e):
  Equal.trans(Nat, a, half(1n+Nat.double(a)), b,
    Equal.sym(Nat, half(1n+Nat.double(a)), a, half_successor_double(a)),
    Equal.trans(Nat, half(1n+Nat.double(a)), half(1n+Nat.double(b)), b,
      Equal.cong(Nat, Nat, r => half(r), 1n+Nat.double(a), 1n+Nat.double(b), e),
      half_successor_double(b)))

def double_negative_successor_double(+a: Nat, +b: Nat,
  e: {Nat.double(a) == 1n+Nat.double(b) : Nat}) -> Empty:
  false = Equal.trans(Bool, False{}, parity(Nat.double(a)), True{},
    Equal.sym(Bool, parity(Nat.double(a)), False{}, parity_double(a)),
    Equal.trans(Bool, parity(Nat.double(a)), parity(1n+Nat.double(b)), True{},
      Equal.cong(Nat, Bool, r => parity(r), Nat.double(a), 1n+Nat.double(b), e),
      parity_successor_double(b)))
  %false : Bool.pick(Type, _, Empty, Unit)
  Unit{}

# Induction on width, recovering the low bit by parity and the tail
# by cancelling double. Applies to every width, including zero.
law word_to_nat_injective:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for e: {Word.to_nat(n, a) == Word.to_nat(n, b) : Nat}
  {a == b : Word(n)}
def word_to_nat_injective(n, a, b, e):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r}, at, bt,
            word_to_nat_injective(p, at, bt,
              double_injective(Word.to_nat(p, at), Word.to_nat(p, bt), e)))
        case WCon{False{}, at} WCon{True{}, bt}:
          impossible({WCon{False{}, at} == WCon{True{}, bt} : Word(1n+p)},
            double_negative_successor_double(Word.to_nat(p, at), Word.to_nat(p, bt), e))
        case WCon{True{}, at} WCon{False{}, bt}:
          impossible({WCon{True{}, at} == WCon{False{}, bt} : Word(1n+p)},
            double_negative_successor_double(Word.to_nat(p, bt), Word.to_nat(p, at),
              Equal.sym(Nat, 1n+Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt)), e)))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{True{}, r}, at, bt,
            word_to_nat_injective(p, at, bt,
              successor_double_injective(Word.to_nat(p, at), Word.to_nat(p, bt), e)))

law u32_to_nat_injective:
  for +a: U32
  for +b: U32
  for e: {U32.to_nat(a) == U32.to_nat(b) : Nat}
  {a == b : U32}
def u32_to_nat_injective(a, b, e):
  match a b:
    case U32{+aw} U32{+bw}:
      Equal.cong(Word(32n), U32, r => U32{r}, aw, bw,
        word_to_nat_injective(32n, aw, bw, e))
