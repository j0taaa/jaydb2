# Relaxamento de limites naturais exatos; None continua sendo overflow.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecSomas.bend as S
import ./CodecSomasOrdem.bend as O
import ./CodecMinimosPilha.bend as M
import ./CodecAceitacaoPilha.bend as J

law zero_nao_maior:
  for n: Nat
  {Nat.is_le(0n, n) == True{} : Bool}
def zero_nao_maior(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

law somar_prefixo_preserva_ordem:
  for +k: Nat
  for +n: Nat
  for +m: Nat
  for le: {Nat.is_le(n, m) == True{} : Bool}
  {Nat.is_le(Nat.add(k, n), Nat.add(k, m)) == True{} : Bool}
def somar_prefixo_preserva_ordem(k, n, m, le):
  match k:
    case 0n:
      le
    case 1n+p:
      somar_prefixo_preserva_ordem(p, n, m, le)

law ordem_transitiva:
  for +n: Nat
  for +m: Nat
  for +t: Nat
  for nm: {Nat.is_le(n, m) == True{} : Bool}
  for mt: {Nat.is_le(m, t) == True{} : Bool}
  {Nat.is_le(n, t) == True{} : Bool}
def ordem_transitiva(n, m, t, nm, mt):
  match n m t:
    case 0n _ _:
      zero_nao_maior(t)
    case 1n+p 0n _:
      F.absurdo_booleano({Nat.is_le(1n+p, t) == True{} : Bool}, nm)
    case 1n+p 1n+q 0n:
      F.absurdo_booleano({False{} == True{} : Bool}, mt)
    case 1n+p 1n+q 1n+r:
      ordem_transitiva(p, q, r, nm, mt)

# As duas conversoes sao exatas, mas podem produzir None. Nao se exige
# representabilidade de nenhum minimo para construir esta relacao.
type OrdemNatural<-a: Maybe<&2, B.Numero64>, -b: Maybe<&2, B.Numero64>> is Type:
  OrdemNatural{menor: Nat, maior: Nat,
    exato_menor: {a == B.nat64(menor) : Maybe<&2, B.Numero64>},
    exato_maior: {b == B.nat64(maior) : Maybe<&2, B.Numero64>},
    ordem: {Nat.is_le(menor, maior) == True{} : Bool}}

def somar_exatos(+a: Maybe<&2, B.Numero64>, +b: Maybe<&2, B.Numero64>, +n: Nat, +m: Nat,
  ea: {a == B.nat64(n) : Maybe<&2, B.Numero64>},
  eb: {b == B.nat64(m) : Maybe<&2, B.Numero64>}) ->
  {C.somar_opcionais(a, b) == B.nat64(Nat.add(n, m)) : Maybe<&2, B.Numero64>}:
  %Equal.sym(Maybe<&2, B.Numero64>, a, B.nat64(n), ea) :
    {C.somar_opcionais(_, b) == B.nat64(Nat.add(n, m)) : Maybe<&2, B.Numero64>}
  %Equal.sym(Maybe<&2, B.Numero64>, b, B.nat64(m), eb) :
    {C.somar_opcionais(B.nat64(n), _) == B.nat64(Nat.add(n, m)) : Maybe<&2, B.Numero64>}
  S.somar_opcionais_nat64_exato(n, m)

def somar_a_ordem(+prefixo: Maybe<&2, B.Numero64>, +k: Nat,
  +a: Maybe<&2, B.Numero64>, +b: Maybe<&2, B.Numero64>,
  +exato: {prefixo == B.nat64(k) : Maybe<&2, B.Numero64>},
  h: OrdemNatural<a, b>) -> OrdemNatural<C.somar_opcionais(prefixo, a), C.somar_opcionais(prefixo, b)>:
  match h:
    case OrdemNatural{+n, +m, ea, eb, le}:
      OrdemNatural{Nat.add(k, n), Nat.add(k, m),
        somar_exatos(prefixo, a, k, n, exato, ea),
        somar_exatos(prefixo, b, k, m, exato, eb),
        somar_prefixo_preserva_ordem(k, n, m, le)}

def pendencia_exata(+q: B.Numero64, +k: Nat, +a: Maybe<&2, B.Numero64>, +n: Nat, +r: Nat,
  medido: {B.nat64(n) == Some{q} : Maybe<&2, B.Numero64>},
  exato: {a == B.nat64(r) : Maybe<&2, B.Numero64>}) ->
  {C.somar_pendencia(q, k, a) == B.nat64(Nat.add(Nat.mul(k, n), r)) : Maybe<&2, B.Numero64>}:
  %Equal.sym(Maybe<&2, B.Numero64>, a, B.nat64(r), exato) :
    {C.somar_pendencia(q, k, _) == B.nat64(Nat.add(Nat.mul(k, n), r)) : Maybe<&2, B.Numero64>}
  M.somar_pendencia_nat64_exato(n, q, k, r, medido)

def pendencia_a_ordem(+q: B.Numero64, +k: Nat,
  +a: Maybe<&2, B.Numero64>, +b: Maybe<&2, B.Numero64>, +n: Nat,
  +medido: {B.nat64(n) == Some{q} : Maybe<&2, B.Numero64>},
  h: OrdemNatural<a, b>) -> OrdemNatural<C.somar_pendencia(q, k, a), C.somar_pendencia(q, k, b)>:
  match h:
    case OrdemNatural{+r, +s, ea, eb, le}:
      OrdemNatural{Nat.add(Nat.mul(k, n), r), Nat.add(Nat.mul(k, n), s),
        pendencia_exata(q, k, a, n, r, medido, ea),
        pendencia_exata(q, k, b, n, s, medido, eb),
        somar_prefixo_preserva_ordem(Nat.mul(k, n), r, s, le)}

def ordem_na_raiz(-fora: C.Pilha, minimo: M.MinimoExato<fora>) ->
  OrdemNatural<C.minimo_pilha(C.Raiz{}), C.minimo_pilha(fora)>:
  match minimo:
    case M.MinimoExato{+n, exato}:
      OrdemNatural{0n, n, {==}, exato, zero_nao_maior(n)}

# A prova estrutural usa somente medidas dos contadores, sem exigir que
# nenhum minimo composto seja representavel.
law minimos_ligados_naturais:
  for +p: C.Pilha
  for +fora: C.Pilha
  for medidas_p: M.MedidasPilha(p)
  for medidas_fora: M.MedidasPilha(fora)
  OrdemNatural<C.minimo_pilha(p), C.minimo_pilha(J.ligar_pilha(p, fora))>
def minimos_ligados_naturais(p, fora, medidas_p, medidas_fora):
  match p:
    case C.Raiz{}:
      ordem_na_raiz(fora, M.todos_os_minimos_de_pilha_medida_sao_exatos(fora, medidas_fora))
    case C.Lista{u, +q, xs, +pai}:
      match medidas_p:
        case L.Ambos{M.ContadorMedido{+n, medido}, acima}:
          pendencia_a_ordem(q, 1n, C.minimo_pilha(pai), C.minimo_pilha(J.ligar_pilha(pai, fora)), n, medido,
            minimos_ligados_naturais(pai, fora, acima, medidas_fora))
    case C.Campo{u, +q, nome, xs, +pai}:
      match medidas_p:
        case L.Ambos{M.ContadorMedido{+n, medido}, acima}:
          pendencia_a_ordem(q, 11n, C.minimo_pilha(pai), C.minimo_pilha(J.ligar_pilha(pai, fora)), n, medido,
            minimos_ligados_naturais(pai, fora, acima, medidas_fora))
    case C.Nome{u, +q, anterior, xs, +pai}:
      match medidas_p:
        case L.Ambos{M.ContadorMedido{+n, medido}, acima}:
          somar_a_ordem(Some{B.Numero64{0, 1}}, 1n,
            C.somar_pendencia(q, 11n, C.minimo_pilha(pai)),
            C.somar_pendencia(q, 11n, C.minimo_pilha(J.ligar_pilha(pai, fora))), {==},
            pendencia_a_ordem(q, 11n, C.minimo_pilha(pai), C.minimo_pilha(J.ligar_pilha(pai, fora)), n, medido,
              minimos_ligados_naturais(pai, fora, acima, medidas_fora)))

def e_cabe(c: C.Conferencia) -> Bool:
  match c:
    case C.Cabe{}:
      True{}
    case C.Curto{}:
      False{}
    case C.Grande{}:
      False{}

def conferir_exige_representacao(+a: Maybe<&2, B.Numero64>, +corpo: B.Numero64, +teto: B.Numero64,
  cabe: {C.conferir(a, corpo, teto) == C.Cabe{} : C.Conferencia}) -> O.NumeroRepresentado<a>:
  match a:
    case None{}:
      F.absurdo_booleano(O.NumeroRepresentado<None{}>,
        Equal.cong(C.Conferencia, Bool, c => e_cabe(c), C.Grande{}, C.Cabe{}, cabe))
    case Some{q}:
      O.Representado{q, {==}}

def conferir_casos_exige_limites(+t: Bool, +c: Bool,
  cabe: {C.conferir_casos(t, c) == C.Cabe{} : C.Conferencia}) ->
  L.E<{t == True{} : Bool}, {c == True{} : Bool}>:
  match t c:
    case True{} True{}:
      L.Ambos{{==}, {==}}
    case True{} False{}:
      F.absurdo_booleano(L.E<{True{} == True{} : Bool}, {False{} == True{} : Bool}>,
        Equal.cong(C.Conferencia, Bool, x => e_cabe(x), C.Curto{}, C.Cabe{}, cabe))
    case False{} _:
      F.absurdo_booleano(L.E<{False{} == True{} : Bool}, {c == True{} : Bool}>,
        Equal.cong(C.Conferencia, Bool, x => e_cabe(x), C.Grande{}, C.Cabe{}, cabe))

def limite_natural_do_guard(+m: Nat, +c: Nat, +total: B.Numero64, +corpo: B.Numero64,
  medido: {B.nat64(m) == Some{total} : Maybe<&2, B.Numero64>},
  mc: {B.nat64(c) == Some{corpo} : Maybe<&2, B.Numero64>},
  limite: {C.menor_igual64(total, corpo) == True{} : Bool}) -> {Nat.is_le(m, c) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(m, c), C.menor_igual64(total, corpo), True{},
    Equal.sym(Bool, C.menor_igual64(total, corpo), Nat.is_le(m, c),
      O.menor_igual64_reflete_ordem_nat(m, c, total, corpo, medido, mc)), limite)

def conferir_natural_menor_representado(+n: Nat, +m: Nat, +c: Nat, +t: Nat,
  +corpo: B.Numero64, +teto: B.Numero64,
  +mc: {B.nat64(c) == Some{corpo} : Maybe<&2, B.Numero64>},
  +mt: {B.nat64(t) == Some{teto} : Maybe<&2, B.Numero64>},
  +le: {Nat.is_le(n, m) == True{} : Bool},
  representado: O.NumeroRepresentado<B.nat64(m)>,
  cabe: {C.conferir(B.nat64(m), corpo, teto) == C.Cabe{} : C.Conferencia}) ->
  {C.conferir(B.nat64(n), corpo, teto) == C.Cabe{} : C.Conferencia}:
  match representado:
    case O.Representado{+total, +medido}:
      limites = conferir_casos_exige_limites(C.menor_igual64(total, teto), C.menor_igual64(total, corpo),
        (%medido : {C.conferir(_, corpo, teto) == C.Cabe{} : C.Conferencia}
          cabe))
      F.com_par({C.conferir(B.nat64(n), corpo, teto) == C.Cabe{} : C.Conferencia},
        {C.menor_igual64(total, teto) == True{} : Bool}, {C.menor_igual64(total, corpo) == True{} : Bool},
        limites, lt => lc =>
          O.conferir_natural_limitado(n, c, t, corpo, teto, mc, mt,
            ordem_transitiva(n, m, c, le, limite_natural_do_guard(m, c, total, corpo, medido, mc, lc)),
            ordem_transitiva(n, m, t, le, limite_natural_do_guard(m, t, total, teto, medido, mt, lt))))

law conferir_natural_menor:
  for +n: Nat
  for +m: Nat
  for +c: Nat
  for +t: Nat
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +mc: {B.nat64(c) == Some{corpo} : Maybe<&2, B.Numero64>}
  for +mt: {B.nat64(t) == Some{teto} : Maybe<&2, B.Numero64>}
  for +le: {Nat.is_le(n, m) == True{} : Bool}
  for +cabe: {C.conferir(B.nat64(m), corpo, teto) == C.Cabe{} : C.Conferencia}
  {C.conferir(B.nat64(n), corpo, teto) == C.Cabe{} : C.Conferencia}
def conferir_natural_menor(n, m, c, t, corpo, teto, mc, mt, le, cabe):
  conferir_natural_menor_representado(n, m, c, t, corpo, teto, mc, mt, le,
    conferir_exige_representacao(B.nat64(m), corpo, teto, cabe), cabe)
