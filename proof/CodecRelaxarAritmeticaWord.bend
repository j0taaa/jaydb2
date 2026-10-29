# Todo Word possui uma medida natural exata, sem premissa de representabilidade.
import Base
import ../contrato/Bytes.bend as B
import ./CodecSomasBits.bend as S
import ./CodecSomas64.bend as P

# Dobrar a medida acrescenta um bit baixo zero, inclusive no caso None.
law natural_dobro:
  for +n: Nat
  for +v: Nat
  {S.natural(1n+n, Nat.double(v)) == S.anexar(n, False{}, S.natural(n, v)) : Maybe<&2, Word(1n+n)>}
def natural_dobro(n, v):
  match v:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Maybe<&2, Word(1n+n)>,
        S.incrementar(1n+n, S.incrementar(1n+n, S.natural(1n+n, Nat.double(p)))),
        S.incrementar(1n+n, S.incrementar(1n+n, S.anexar(n, False{}, S.natural(n, p)))),
        S.anexar(n, False{}, S.incrementar(n, S.natural(n, p))),
        Equal.cong(Maybe<&2, Word(1n+n)>, Maybe<&2, Word(1n+n)>,
          m => S.incrementar(1n+n, S.incrementar(1n+n, m)),
          S.natural(1n+n, Nat.double(p)), S.anexar(n, False{}, S.natural(n, p)), natural_dobro(n, p)),
        Equal.trans(Maybe<&2, Word(1n+n)>,
          S.incrementar(1n+n, S.incrementar(1n+n, S.anexar(n, False{}, S.natural(n, p)))),
          S.incrementar(1n+n, S.anexar(n, True{}, S.natural(n, p))),
          S.anexar(n, False{}, S.incrementar(n, S.natural(n, p))),
          Equal.cong(Maybe<&2, Word(1n+n)>, Maybe<&2, Word(1n+n)>, m => S.incrementar(1n+n, m),
            S.incrementar(1n+n, S.anexar(n, False{}, S.natural(n, p))),
            S.anexar(n, True{}, S.natural(n, p)), S.incrementar_anexar_zero(n, S.natural(n, p))),
          S.incrementar_anexar_um(n, S.natural(n, p))))

# Inducao na largura: a testemunha e Word.to_nat, calculada pelos bits.
law natural_representa_palavra:
  for +n: Nat
  for +w: Word(n)
  {S.natural(n, Word.to_nat(n, w)) == Some{w} : Maybe<&2, Word(n)>}
def natural_representa_palavra(n, w):
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
            S.anexar(p, False{}, S.natural(p, Word.to_nat(p, t))),
            Some{WCon{False{}, t}},
            natural_dobro(p, Word.to_nat(p, t)),
            Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => S.anexar(p, False{}, m),
              S.natural(p, Word.to_nat(p, t)), Some{t}, natural_representa_palavra(p, t)))
        case WCon{True{}, +t}:
          Equal.trans(Maybe<&2, Word(1n+p)>,
            S.incrementar(1n+p, S.natural(1n+p, Nat.double(Word.to_nat(p, t)))),
            S.incrementar(1n+p, S.anexar(p, False{}, S.natural(p, Word.to_nat(p, t)))),
            Some{WCon{True{}, t}},
            Equal.cong(Maybe<&2, Word(1n+p)>, Maybe<&2, Word(1n+p)>, m => S.incrementar(1n+p, m),
              S.natural(1n+p, Nat.double(Word.to_nat(p, t))),
              S.anexar(p, False{}, S.natural(p, Word.to_nat(p, t))), natural_dobro(p, Word.to_nat(p, t))),
            Equal.trans(Maybe<&2, Word(1n+p)>,
              S.incrementar(1n+p, S.anexar(p, False{}, S.natural(p, Word.to_nat(p, t)))),
              S.anexar(p, True{}, S.natural(p, Word.to_nat(p, t))),
              Some{WCon{True{}, t}},
              S.incrementar_anexar_zero(p, S.natural(p, Word.to_nat(p, t))),
              Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => S.anexar(p, True{}, m),
                S.natural(p, Word.to_nat(p, t)), Some{t}, natural_representa_palavra(p, t))))

# A ponte fiel de CodecSomas64 transporta a medida para o nat64 real.
law nat64_mede_numero:
  for +q: B.Numero64
  {B.nat64(Word.to_nat(64n, P.bits(q))) == Some{q} : Maybe<&2, B.Numero64>}
def nat64_mede_numero(q):
  P.representar_injetiva(B.nat64(Word.to_nat(64n, P.bits(q))), Some{q},
    Equal.trans(Maybe<&2, Word(64n)>,
      P.representar(B.nat64(Word.to_nat(64n, P.bits(q)))),
      S.natural(64n, Word.to_nat(64n, P.bits(q))), Some{P.bits(q)},
      P.nat64_representa_natural_binario(Word.to_nat(64n, P.bits(q))),
      natural_representa_palavra(64n, P.bits(q))))

type NumeroMedido<-q: B.Numero64> is Type:
  NumeroMedido{natural: Nat, medido: {B.nat64(natural) == Some{q} : Maybe<&2, B.Numero64>}}

def medir_numero(+q: B.Numero64) -> NumeroMedido<q>:
  NumeroMedido{Word.to_nat(64n, P.bits(q)), nat64_mede_numero(q)}
