# Every Word has an exact natural measure, without a representability premise.
import Base
import ../contract/Bytes.bend as B
import ./CodecSumsBits.bend as S
import ./CodecSums64.bend as P

# Doubling the measure appends a zero low bit, including the None case.
law natural_double:
  for +n: Nat
  for +v: Nat
  {S.natural(1n+n, Nat.double(v)) == S.attach(n, False{}, S.natural(n, v)) : Maybe<&2, Word(1n+n)>}
def natural_double(n, v):
  match v:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Maybe<&2, Word(1n+n)>,
        S.increment(1n+n, S.increment(1n+n, S.natural(1n+n, Nat.double(p)))),
        S.increment(1n+n, S.increment(1n+n, S.attach(n, False{}, S.natural(n, p)))),
        S.attach(n, False{}, S.increment(n, S.natural(n, p))),
        Equal.cong(Maybe<&2, Word(1n+n)>, Maybe<&2, Word(1n+n)>,
          m => S.increment(1n+n, S.increment(1n+n, m)),
          S.natural(1n+n, Nat.double(p)), S.attach(n, False{}, S.natural(n, p)), natural_double(n, p)),
        Equal.trans(Maybe<&2, Word(1n+n)>,
          S.increment(1n+n, S.increment(1n+n, S.attach(n, False{}, S.natural(n, p)))),
          S.increment(1n+n, S.attach(n, True{}, S.natural(n, p))),
          S.attach(n, False{}, S.increment(n, S.natural(n, p))),
          Equal.cong(Maybe<&2, Word(1n+n)>, Maybe<&2, Word(1n+n)>, m => S.increment(1n+n, m),
            S.increment(1n+n, S.attach(n, False{}, S.natural(n, p))),
            S.attach(n, True{}, S.natural(n, p)), S.increment_attach_zero(n, S.natural(n, p))),
          S.increment_attach_one(n, S.natural(n, p))))

# Width induction: the witness is Word.to_nat, computed from the bits.
law natural_represents_word:
  for +n: Nat
  for +w: Word(n)
  {S.natural(n, Word.to_nat(n, w)) == Some{w} : Maybe<&2, Word(n)>}
def natural_represents_word(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          Equal.trans(Maybe<&2, Word(1n+p)>,
            S.natural(1n+p, Nat.double(Word.to_nat(p, t))),
            S.attach(p, False{}, S.natural(p, Word.to_nat(p, t))),
            Some{WCon{False{}, t}},
            natural_double(p, Word.to_nat(p, t)),
            Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => S.attach(p, False{}, m),
              S.natural(p, Word.to_nat(p, t)), Some{t}, natural_represents_word(p, t)))
        case WCon{True{}, +t}:
          Equal.trans(Maybe<&2, Word(1n+p)>,
            S.increment(1n+p, S.natural(1n+p, Nat.double(Word.to_nat(p, t)))),
            S.increment(1n+p, S.attach(p, False{}, S.natural(p, Word.to_nat(p, t)))),
            Some{WCon{True{}, t}},
            Equal.cong(Maybe<&2, Word(1n+p)>, Maybe<&2, Word(1n+p)>, m => S.increment(1n+p, m),
              S.natural(1n+p, Nat.double(Word.to_nat(p, t))),
              S.attach(p, False{}, S.natural(p, Word.to_nat(p, t))), natural_double(p, Word.to_nat(p, t))),
            Equal.trans(Maybe<&2, Word(1n+p)>,
              S.increment(1n+p, S.attach(p, False{}, S.natural(p, Word.to_nat(p, t)))),
              S.attach(p, True{}, S.natural(p, Word.to_nat(p, t))),
              Some{WCon{True{}, t}},
              S.increment_attach_zero(p, S.natural(p, Word.to_nat(p, t))),
              Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => S.attach(p, True{}, m),
                S.natural(p, Word.to_nat(p, t)), Some{t}, natural_represents_word(p, t))))

# The faithful CodecSums64 bridge transports the measure to actual nat64.
law nat64_measures_number:
  for +q: B.Number64
  {B.nat64(Word.to_nat(64n, P.bits(q))) == Some{q} : Maybe<&2, B.Number64>}
def nat64_measures_number(q):
  P.represent_injective(B.nat64(Word.to_nat(64n, P.bits(q))), Some{q},
    Equal.trans(Maybe<&2, Word(64n)>,
      P.represent(B.nat64(Word.to_nat(64n, P.bits(q)))),
      S.natural(64n, Word.to_nat(64n, P.bits(q))), Some{P.bits(q)},
      P.nat64_represents_natural_binary(Word.to_nat(64n, P.bits(q))),
      natural_represents_word(64n, P.bits(q))))

type NumberMeasured<-q: B.Number64> is Type:
  NumberMeasured{natural: Nat, measured: {B.nat64(natural) == Some{q} : Maybe<&2, B.Number64>}}

def measure_number(+q: B.Number64) -> NumberMeasured<q>:
  NumberMeasured{Word.to_nat(64n, P.bits(q)), nat64_measures_number(q)}
