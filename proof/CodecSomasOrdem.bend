# Ordem matematica dos contadores representaveis, nos dois sentidos.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecContadores.bend as N
import ./CodecUnicode.bend as U
import ./CodecMinimos.bend as M
import ./CodecSomas.bend as A

def inverter_cmp(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

law inverter_fin:
  for a: Bool
  for b: Bool
  for c: Cmp
  {inverter_cmp(Word.cmp.fin(a, b, c)) == Word.cmp.fin(b, a, inverter_cmp(c)) : Cmp}
def inverter_fin(a, b, c):
  match a b c:
    case False{} False{} LT{}:
      {==}
    case False{} False{} EQ{}:
      {==}
    case False{} False{} GT{}:
      {==}
    case False{} True{} LT{}:
      {==}
    case False{} True{} EQ{}:
      {==}
    case False{} True{} GT{}:
      {==}
    case True{} False{} LT{}:
      {==}
    case True{} False{} EQ{}:
      {==}
    case True{} False{} GT{}:
      {==}
    case True{} True{} LT{}:
      {==}
    case True{} True{} EQ{}:
      {==}
    case True{} True{} GT{}:
      {==}

law comparar_palavras_invertidas:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {inverter_cmp(Word.cmp(n, a, b)) == Word.cmp(n, b, a) : Cmp}
def comparar_palavras_invertidas(n, a, b):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{x, +at} WCon{y, +bt}:
          Equal.trans(Cmp,
            inverter_cmp(Word.cmp.fin(x, y, Word.cmp(p, at, bt))),
            Word.cmp.fin(y, x, inverter_cmp(Word.cmp(p, at, bt))),
            Word.cmp.fin(y, x, Word.cmp(p, bt, at)),
            inverter_fin(x, y, Word.cmp(p, at, bt)),
            Equal.cong(Cmp, Cmp, c => Word.cmp.fin(y, x, c),
              inverter_cmp(Word.cmp(p, at, bt)), Word.cmp(p, bt, at), comparar_palavras_invertidas(p, at, bt)))

law le_cmp_invertida:
  for c: Cmp
  {Cmp.is_le(inverter_cmp(c)) == Bool.not(Cmp.is_lt(c)) : Bool}
def le_cmp_invertida(c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

law lt_cmp_invertida:
  for c: Cmp
  {Cmp.is_lt(inverter_cmp(c)) == Bool.not(Cmp.is_le(c)) : Bool}
def lt_cmp_invertida(c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

law le_palavras_invertidas:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Cmp.is_le(Word.cmp(n, a, b)) == Bool.not(Cmp.is_lt(Word.cmp(n, b, a))) : Bool}
def le_palavras_invertidas(n, a, b):
  %comparar_palavras_invertidas(n, b, a) :
    {Cmp.is_le(_) == Bool.not(Cmp.is_lt(Word.cmp(n, b, a))) : Bool}
  le_cmp_invertida(Word.cmp(n, b, a))

law lt_palavras_invertidas:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Cmp.is_lt(Word.cmp(n, a, b)) == Bool.not(Cmp.is_le(Word.cmp(n, b, a))) : Bool}
def lt_palavras_invertidas(n, a, b):
  %comparar_palavras_invertidas(n, b, a) :
    {Cmp.is_lt(_) == Bool.not(Cmp.is_le(Word.cmp(n, b, a))) : Bool}
  lt_cmp_invertida(Word.cmp(n, b, a))

law limite_sucessor_esquerdo:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for cabe: {U.sem_transporte(n, a) == True{} : Bool}
  {Cmp.is_le(Word.cmp(n, Word.inc(n, a), b)) == Cmp.is_lt(Word.cmp(n, a, b)) : Bool}
def limite_sucessor_esquerdo(n, a, b, cabe):
  Equal.trans(Bool,
    Cmp.is_le(Word.cmp(n, Word.inc(n, a), b)),
    Bool.not(Cmp.is_lt(Word.cmp(n, b, Word.inc(n, a)))),
    Cmp.is_lt(Word.cmp(n, a, b)),
    le_palavras_invertidas(n, Word.inc(n, a), b),
    Equal.trans(Bool,
      Bool.not(Cmp.is_lt(Word.cmp(n, b, Word.inc(n, a)))),
      Bool.not(Cmp.is_le(Word.cmp(n, b, a))), Cmp.is_lt(Word.cmp(n, a, b)),
      Equal.cong(Bool, Bool, c => Bool.not(c),
        Cmp.is_lt(Word.cmp(n, b, Word.inc(n, a))), Cmp.is_le(Word.cmp(n, b, a)),
        Equal.sym(Bool, Cmp.is_le(Word.cmp(n, b, a)), Cmp.is_lt(Word.cmp(n, b, Word.inc(n, a))), U.word_limite_sucessor(n, b, a, cabe))),
      Equal.sym(Bool, Cmp.is_lt(Word.cmp(n, a, b)), Bool.not(Cmp.is_le(Word.cmp(n, b, a))), lt_palavras_invertidas(n, a, b))))

law le_fin_00:
  for c: Cmp
  {Cmp.is_le(Word.cmp.fin(False{}, False{}, c)) == Cmp.is_le(c) : Bool}
def le_fin_00(c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

law le_fin_01:
  for c: Cmp
  {Cmp.is_le(Word.cmp.fin(False{}, True{}, c)) == Cmp.is_le(c) : Bool}
def le_fin_01(c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

law le_fin_10:
  for c: Cmp
  {Cmp.is_le(Word.cmp.fin(True{}, False{}, c)) == Cmp.is_lt(c) : Bool}
def le_fin_10(c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

law le_fin_11:
  for c: Cmp
  {Cmp.is_le(Word.cmp.fin(True{}, True{}, c)) == Cmp.is_le(c) : Bool}
def le_fin_11(c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

law incrementar_preserva_comparacao:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +ca: {U.sem_transporte(n, a) == True{} : Bool}
  for +cb: {U.sem_transporte(n, b) == True{} : Bool}
  {Cmp.is_le(Word.cmp(n, Word.inc(n, a), Word.inc(n, b))) == Cmp.is_le(Word.cmp(n, a, b)) : Bool}
def incrementar_preserva_comparacao(n, a, b, ca, cb):
  match n:
    case 0n:
      F.absurdo_booleano({Cmp.is_le(Word.cmp(0n, Word.inc(0n, a), Word.inc(0n, b))) == Cmp.is_le(Word.cmp(0n, a, b)) : Bool}, ca)
    case 1n+p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          Equal.trans(Bool,
            Cmp.is_le(Word.cmp.fin(True{}, True{}, Word.cmp(p, at, bt))),
            Cmp.is_le(Word.cmp(p, at, bt)),
            Cmp.is_le(Word.cmp.fin(False{}, False{}, Word.cmp(p, at, bt))),
            le_fin_11(Word.cmp(p, at, bt)),
            Equal.sym(Bool, Cmp.is_le(Word.cmp.fin(False{}, False{}, Word.cmp(p, at, bt))), Cmp.is_le(Word.cmp(p, at, bt)), le_fin_00(Word.cmp(p, at, bt))))
        case WCon{False{}, +at} WCon{True{}, +bt}:
          Equal.trans(Bool,
            Cmp.is_le(Word.cmp.fin(True{}, False{}, Word.cmp(p, at, Word.inc(p, bt)))),
            Cmp.is_lt(Word.cmp(p, at, Word.inc(p, bt))),
            Cmp.is_le(Word.cmp.fin(False{}, True{}, Word.cmp(p, at, bt))),
            le_fin_10(Word.cmp(p, at, Word.inc(p, bt))),
            Equal.trans(Bool,
              Cmp.is_lt(Word.cmp(p, at, Word.inc(p, bt))), Cmp.is_le(Word.cmp(p, at, bt)),
              Cmp.is_le(Word.cmp.fin(False{}, True{}, Word.cmp(p, at, bt))),
              Equal.sym(Bool, Cmp.is_le(Word.cmp(p, at, bt)), Cmp.is_lt(Word.cmp(p, at, Word.inc(p, bt))), U.word_limite_sucessor(p, at, bt, cb)),
              Equal.sym(Bool, Cmp.is_le(Word.cmp.fin(False{}, True{}, Word.cmp(p, at, bt))), Cmp.is_le(Word.cmp(p, at, bt)), le_fin_01(Word.cmp(p, at, bt)))))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          Equal.trans(Bool,
            Cmp.is_le(Word.cmp.fin(False{}, True{}, Word.cmp(p, Word.inc(p, at), bt))),
            Cmp.is_le(Word.cmp(p, Word.inc(p, at), bt)),
            Cmp.is_le(Word.cmp.fin(True{}, False{}, Word.cmp(p, at, bt))),
            le_fin_01(Word.cmp(p, Word.inc(p, at), bt)),
            Equal.trans(Bool,
              Cmp.is_le(Word.cmp(p, Word.inc(p, at), bt)), Cmp.is_lt(Word.cmp(p, at, bt)),
              Cmp.is_le(Word.cmp.fin(True{}, False{}, Word.cmp(p, at, bt))),
              limite_sucessor_esquerdo(p, at, bt, ca),
              Equal.sym(Bool, Cmp.is_le(Word.cmp.fin(True{}, False{}, Word.cmp(p, at, bt))), Cmp.is_lt(Word.cmp(p, at, bt)), le_fin_10(Word.cmp(p, at, bt)))))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          Equal.trans(Bool,
            Cmp.is_le(Word.cmp.fin(False{}, False{}, Word.cmp(p, Word.inc(p, at), Word.inc(p, bt)))),
            Cmp.is_le(Word.cmp(p, Word.inc(p, at), Word.inc(p, bt))),
            Cmp.is_le(Word.cmp.fin(True{}, True{}, Word.cmp(p, at, bt))),
            le_fin_00(Word.cmp(p, Word.inc(p, at), Word.inc(p, bt))),
            Equal.trans(Bool,
              Cmp.is_le(Word.cmp(p, Word.inc(p, at), Word.inc(p, bt))), Cmp.is_le(Word.cmp(p, at, bt)),
              Cmp.is_le(Word.cmp.fin(True{}, True{}, Word.cmp(p, at, bt))),
              incrementar_preserva_comparacao(p, at, bt, ca, cb),
              Equal.sym(Bool, Cmp.is_le(Word.cmp.fin(True{}, True{}, Word.cmp(p, at, bt))), Cmp.is_le(Word.cmp(p, at, bt)), le_fin_11(Word.cmp(p, at, bt)))))

law comparar_predecessores_positivos:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +pa: {N.zeros(n, a) == False{} : Bool}
  for +pb: {N.zeros(n, b) == False{} : Bool}
  {Cmp.is_le(Word.cmp(n, a, b)) == Cmp.is_le(Word.cmp(n, N.predecessor(n, a), N.predecessor(n, b))) : Bool}
def comparar_predecessores_positivos(n, a, b, pa, pb):
  %N.incremento_do_predecessor(n, a) :
    {Cmp.is_le(Word.cmp(n, _, b)) == Cmp.is_le(Word.cmp(n, N.predecessor(n, a), N.predecessor(n, b))) : Bool}
  %N.incremento_do_predecessor(n, b) :
    {Cmp.is_le(Word.cmp(n, Word.inc(n, N.predecessor(n, a)), _)) == Cmp.is_le(Word.cmp(n, N.predecessor(n, a), N.predecessor(n, b))) : Bool}
  incrementar_preserva_comparacao(n, N.predecessor(n, a), N.predecessor(n, b),
    M.predecessor_positivo_pode_ser_incrementado(n, a, pa), M.predecessor_positivo_pode_ser_incrementado(n, b, pb))

law diminuir_preserva_comparacao_dos_bits:
  for +a: B.Numero64
  for +b: B.Numero64
  for +pa: {C.zero64(a) == False{} : Bool}
  for +pb: {C.zero64(b) == False{} : Bool}
  {Cmp.is_le(Word.cmp(64n, M.bits64(a), M.bits64(b))) ==
    Cmp.is_le(Word.cmp(64n, M.bits64(C.diminuir64(a)), M.bits64(C.diminuir64(b)))) : Bool}
def diminuir_preserva_comparacao_dos_bits(a, b, pa, pb):
  %Equal.sym(Word(64n), M.bits64(C.diminuir64(a)), N.predecessor(64n, M.bits64(a)), M.diminuir64_representa_predecessor_positivo(a, pa)) :
    {Cmp.is_le(Word.cmp(64n, M.bits64(a), M.bits64(b))) ==
      Cmp.is_le(Word.cmp(64n, _, M.bits64(C.diminuir64(b)))) : Bool}
  %Equal.sym(Word(64n), M.bits64(C.diminuir64(b)), N.predecessor(64n, M.bits64(b)), M.diminuir64_representa_predecessor_positivo(b, pb)) :
    {Cmp.is_le(Word.cmp(64n, M.bits64(a), M.bits64(b))) ==
      Cmp.is_le(Word.cmp(64n, N.predecessor(64n, M.bits64(a)), _)) : Bool}
  comparar_predecessores_positivos(64n, M.bits64(a), M.bits64(b),
    Equal.trans(Bool, N.zeros(64n, M.bits64(a)), C.zero64(a), False{}, Equal.sym(Bool, C.zero64(a), N.zeros(64n, M.bits64(a)), M.zero64_equivale_bits_zero(a)), pa),
    Equal.trans(Bool, N.zeros(64n, M.bits64(b)), C.zero64(b), False{}, Equal.sym(Bool, C.zero64(b), N.zeros(64n, M.bits64(b)), M.zero64_equivale_bits_zero(b)), pb))

# Equivalencia, e nao somente a implicacao ja disponivel em CodecMinimos.
law diminuir_preserva_e_reflete_ordem_positiva:
  for +a: B.Numero64
  for +b: B.Numero64
  for +pa: {C.zero64(a) == False{} : Bool}
  for +pb: {C.zero64(b) == False{} : Bool}
  {C.menor_igual64(a, b) == C.menor_igual64(C.diminuir64(a), C.diminuir64(b)) : Bool}
def diminuir_preserva_e_reflete_ordem_positiva(a, b, pa, pb):
  Equal.trans(Bool,
    C.menor_igual64(a, b), Cmp.is_le(Word.cmp(64n, M.bits64(a), M.bits64(b))),
    C.menor_igual64(C.diminuir64(a), C.diminuir64(b)),
    M.menor_igual64_equivale_ordem_dos_bits(a, b),
    Equal.trans(Bool,
      Cmp.is_le(Word.cmp(64n, M.bits64(a), M.bits64(b))),
      Cmp.is_le(Word.cmp(64n, M.bits64(C.diminuir64(a)), M.bits64(C.diminuir64(b)))),
      C.menor_igual64(C.diminuir64(a), C.diminuir64(b)),
      diminuir_preserva_comparacao_dos_bits(a, b, pa, pb),
      Equal.sym(Bool, C.menor_igual64(C.diminuir64(a), C.diminuir64(b)),
        Cmp.is_le(Word.cmp(64n, M.bits64(C.diminuir64(a)), M.bits64(C.diminuir64(b)))), M.menor_igual64_equivale_ordem_dos_bits(C.diminuir64(a), C.diminuir64(b)))))

law positivo_nao_menor_igual_zero:
  for +a: B.Numero64
  for +positivo: {C.zero64(a) == False{} : Bool}
  {C.menor_igual64(a, B.Numero64{0, 0}) == False{} : Bool}
def positivo_nao_menor_igual_zero(a, positivo):
  N.falso_se_verdadeiro_impossivel(C.menor_igual64(a, B.Numero64{0, 0}), le =>
    F.falso_nao_verdadeiro(Equal.trans(Bool, False{}, C.zero64(a), True{},
      Equal.sym(Bool, C.zero64(a), False{}, positivo), M.menor_igual_a_zero64_e_zero(a, le))))

# Apenas as duas medicoes reais sao premissas. Todos os casos de ordem
# (menor, igual e maior) sao determinados pela comparacao matematica.
law menor_igual64_reflete_ordem_nat:
  for +n: Nat
  for +m: Nat
  for +x: B.Numero64
  for +y: B.Numero64
  for +nx: {B.nat64(n) == Some{x} : Maybe<&2, B.Numero64>}
  for +my: {B.nat64(m) == Some{y} : Maybe<&2, B.Numero64>}
  {C.menor_igual64(x, y) == Nat.is_le(n, m) : Bool}
def menor_igual64_reflete_ordem_nat(n, m, x, y, nx, my):
  match n m:
    case 0n 0n:
      %F.algum_injetivo(B.Numero64, B.Numero64{0, 0}, x, nx) :
        {C.menor_igual64(_, y) == True{} : Bool}
      M.zero64_nao_maior(y)
    case 0n 1n+q:
      %F.algum_injetivo(B.Numero64, B.Numero64{0, 0}, x, nx) :
        {C.menor_igual64(_, y) == True{} : Bool}
      M.zero64_nao_maior(y)
    case 1n+p 0n:
      %F.algum_injetivo(B.Numero64, B.Numero64{0, 0}, y, my) :
        {C.menor_igual64(x, _) == False{} : Bool}
      positivo_nao_menor_igual_zero(x, N.nat64_sucessor_nunca_zero(p, x, nx))
    case 1n+p 1n+q:
      Equal.trans(Bool,
        C.menor_igual64(x, y), C.menor_igual64(C.diminuir64(x), C.diminuir64(y)), Nat.is_le(p, q),
        diminuir_preserva_e_reflete_ordem_positiva(x, y, N.nat64_sucessor_nunca_zero(p, x, nx), N.nat64_sucessor_nunca_zero(q, y, my)),
        menor_igual64_reflete_ordem_nat(p, q, C.diminuir64(x), C.diminuir64(y),
          N.medida_decrementada(p, x, N.nat64_sucessor_tem_antecessor_exato(p, x, nx)),
          N.medida_decrementada(q, y, N.nat64_sucessor_tem_antecessor_exato(q, y, my))))

law menor_igual64_preserva_ordem_nat:
  for +n: Nat
  for +m: Nat
  for +x: B.Numero64
  for +y: B.Numero64
  for +nx: {B.nat64(n) == Some{x} : Maybe<&2, B.Numero64>}
  for +my: {B.nat64(m) == Some{y} : Maybe<&2, B.Numero64>}
  for le: {Nat.is_le(n, m) == True{} : Bool}
  {C.menor_igual64(x, y) == True{} : Bool}
def menor_igual64_preserva_ordem_nat(n, m, x, y, nx, my, le):
  Equal.trans(Bool, C.menor_igual64(x, y), Nat.is_le(n, m), True{}, menor_igual64_reflete_ordem_nat(n, m, x, y, nx, my), le)

law conferir_nat64_exato:
  for +n: Nat
  for +c: Nat
  for +t: Nat
  for +minimo: B.Numero64
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +mn: {B.nat64(n) == Some{minimo} : Maybe<&2, B.Numero64>}
  for +mc: {B.nat64(c) == Some{corpo} : Maybe<&2, B.Numero64>}
  for +mt: {B.nat64(t) == Some{teto} : Maybe<&2, B.Numero64>}
  {C.conferir(Some{minimo}, corpo, teto) == C.conferir_casos(Nat.is_le(n, t), Nat.is_le(n, c)) : C.Conferencia}
def conferir_nat64_exato(n, c, t, minimo, corpo, teto, mn, mc, mt):
  %Equal.sym(Bool, C.menor_igual64(minimo, teto), Nat.is_le(n, t), menor_igual64_reflete_ordem_nat(n, t, minimo, teto, mn, mt)) :
    {C.conferir_casos(_, C.menor_igual64(minimo, corpo)) == C.conferir_casos(Nat.is_le(n, t), Nat.is_le(n, c)) : C.Conferencia}
  Equal.cong(Bool, C.Conferencia, b => C.conferir_casos(Nat.is_le(n, t), b),
    C.menor_igual64(minimo, corpo), Nat.is_le(n, c), menor_igual64_reflete_ordem_nat(n, c, minimo, corpo, mn, mc))

law conferir_nat64_limitado:
  for +n: Nat
  for +c: Nat
  for +t: Nat
  for +minimo: B.Numero64
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +mn: {B.nat64(n) == Some{minimo} : Maybe<&2, B.Numero64>}
  for +mc: {B.nat64(c) == Some{corpo} : Maybe<&2, B.Numero64>}
  for +mt: {B.nat64(t) == Some{teto} : Maybe<&2, B.Numero64>}
  for nc: {Nat.is_le(n, c) == True{} : Bool}
  for nt: {Nat.is_le(n, t) == True{} : Bool}
  {C.conferir(Some{minimo}, corpo, teto) == C.Cabe{} : C.Conferencia}
def conferir_nat64_limitado(n, c, t, minimo, corpo, teto, mn, mc, mt, nc, nt):
  Equal.trans(C.Conferencia, C.conferir(Some{minimo}, corpo, teto), C.conferir_casos(Nat.is_le(n, t), Nat.is_le(n, c)), C.Cabe{},
    conferir_nat64_exato(n, c, t, minimo, corpo, teto, mn, mc, mt),
    (%Equal.sym(Bool, Nat.is_le(n, t), True{}, nt) : {C.conferir_casos(_, Nat.is_le(n, c)) == C.Cabe{} : C.Conferencia}
      %Equal.sym(Bool, Nat.is_le(n, c), True{}, nc) : {C.conferir_casos(True{}, _) == C.Cabe{} : C.Conferencia}
      {==}))

law nat_subtrair_zero:
  for +n: Nat
  {Nat.sub(n, 0n) == n : Nat}
def nat_subtrair_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

law nat_decompor_limite:
  for +n: Nat
  for +m: Nat
  for le: {Nat.is_le(n, m) == True{} : Bool}
  {Nat.add(n, Nat.sub(m, n)) == m : Nat}
def nat_decompor_limite(n, m, le):
  match n m:
    case 0n _:
      nat_subtrair_zero(m)
    case 1n+p 0n:
      F.absurdo_booleano({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, le)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, r => 1n+r, Nat.add(p, Nat.sub(q, p)), q, nat_decompor_limite(p, q, le))

type NumeroRepresentado<-m: Maybe<&2, B.Numero64>> is Type:
  Representado{numero: B.Numero64, exato: {m == Some{numero} : Maybe<&2, B.Numero64>}}

def soma_aceita_exige_primeira_parcela(a: Maybe<&2, B.Numero64>, b: Maybe<&2, B.Numero64>, -total: B.Numero64,
  exato: {C.somar_opcionais(a, b) == Some{total} : Maybe<&2, B.Numero64>}) -> NumeroRepresentado<a>:
  match a:
    case None{}:
      L.ex_falso(NumeroRepresentado<None{}>, F.nenhum_nao_algum(B.Numero64, total, exato))
    case Some{x}:
      Representado{x, {==}}

# A representabilidade do menor e DERIVADA da soma total, nao assumida.
law nat64_representabilidade_fechada_para_baixo:
  for +n: Nat
  for +m: Nat
  for +y: B.Numero64
  for medido: {B.nat64(m) == Some{y} : Maybe<&2, B.Numero64>}
  for le: {Nat.is_le(n, m) == True{} : Bool}
  NumeroRepresentado<B.nat64(n)>
def nat64_representabilidade_fechada_para_baixo(n, m, y, medido, le):
  soma_aceita_exige_primeira_parcela(B.nat64(n), B.nat64(Nat.sub(m, n)), y,
    Equal.trans(Maybe<&2, B.Numero64>,
      C.somar_opcionais(B.nat64(n), B.nat64(Nat.sub(m, n))),
      B.nat64(Nat.add(n, Nat.sub(m, n))), Some{y},
      A.somar_opcionais_nat64_exato(n, Nat.sub(m, n)),
      Equal.trans(Maybe<&2, B.Numero64>, B.nat64(Nat.add(n, Nat.sub(m, n))), B.nat64(m), Some{y},
        Equal.cong(Nat, Maybe<&2, B.Numero64>, r => B.nat64(r), Nat.add(n, Nat.sub(m, n)), m, nat_decompor_limite(n, m, le)), medido)))

def conferir_natural_representado(+n: Nat, +c: Nat, +t: Nat, +corpo: B.Numero64, +teto: B.Numero64,
  mc: {B.nat64(c) == Some{corpo} : Maybe<&2, B.Numero64>},
  mt: {B.nat64(t) == Some{teto} : Maybe<&2, B.Numero64>},
  nc: {Nat.is_le(n, c) == True{} : Bool},
  nt: {Nat.is_le(n, t) == True{} : Bool},
  representado: NumeroRepresentado<B.nat64(n)>) -> {C.conferir(B.nat64(n), corpo, teto) == C.Cabe{} : C.Conferencia}:
  match representado:
    case Representado{+minimo, +mn}:
      %Equal.sym(Maybe<&2, B.Numero64>, B.nat64(n), Some{minimo}, mn) :
        {C.conferir(_, corpo, teto) == C.Cabe{} : C.Conferencia}
      conferir_nat64_limitado(n, c, t, minimo, corpo, teto, mn, mc, mt, nc, nt)

# Esta forma dispensa ate a testemunha de representabilidade do minimo.
law conferir_natural_limitado:
  for +n: Nat
  for +c: Nat
  for +t: Nat
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +mc: {B.nat64(c) == Some{corpo} : Maybe<&2, B.Numero64>}
  for +mt: {B.nat64(t) == Some{teto} : Maybe<&2, B.Numero64>}
  for +nc: {Nat.is_le(n, c) == True{} : Bool}
  for nt: {Nat.is_le(n, t) == True{} : Bool}
  {C.conferir(B.nat64(n), corpo, teto) == C.Cabe{} : C.Conferencia}
def conferir_natural_limitado(n, c, t, corpo, teto, mc, mt, nc, nt):
  conferir_natural_representado(n, c, t, corpo, teto, mc, mt, nc, nt, nat64_representabilidade_fechada_para_baixo(n, c, corpo, mc, nc))
