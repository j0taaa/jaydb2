# Aritmetica exata do contador do corpo: decremento inverte a conversao
# sem overflow de contrato/Bytes. Nao materializa 2^32/2^64 como Nat.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./Ordens.bend as O
import ./CodecPercurso.bend as R

def predecessor(n: Nat, w: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{True{}, t}:
          WCon{False{}, t}
        case WCon{False{}, t}:
          WCon{True{}, predecessor(p, t)}

law predecessor_do_incremento:
  for +n: Nat
  for +w: Word(n)
  {predecessor(n, Word.inc(n, w)) == w : Word(n)}
def predecessor_do_incremento(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          {==}
        case WCon{True{}, +t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{True{}, r}, predecessor(p, Word.inc(p, t)), t, predecessor_do_incremento(p, t))

law adc_zero_identidade:
  for +n: Nat
  for w: Word(n)
  {Word.adc(n, w, Word.zero(n), False{}, False{}) == w : Word(n)}
def adc_zero_identidade(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r}, Word.adc(p, t, Word.zero(p), False{}, False{}), t, adc_zero_identidade(p, t))
        case WCon{True{}, +t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{True{}, r}, Word.adc(p, t, Word.zero(p), False{}, False{}), t, adc_zero_identidade(p, t))

law adc_zero_incrementa:
  for +n: Nat
  for +w: Word(n)
  {Word.adc(n, w, Word.zero(n), False{}, True{}) == Word.inc(n, w) : Word(n)}
def adc_zero_incrementa(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{True{}, r}, Word.adc(p, t, Word.zero(p), False{}, False{}), t, adc_zero_identidade(p, t))
        case WCon{True{}, +t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r}, Word.adc(p, t, Word.zero(p), False{}, True{}), Word.inc(p, t), adc_zero_incrementa(p, t))

law sbb_zero_identidade:
  for +n: Nat
  for w: Word(n)
  {Word.adc(n, w, Word.zero(n), True{}, True{}) == w : Word(n)}
def sbb_zero_identidade(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r}, Word.adc(p, t, Word.zero(p), True{}, True{}), t, sbb_zero_identidade(p, t))
        case WCon{True{}, +t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{True{}, r}, Word.adc(p, t, Word.zero(p), True{}, True{}), t, sbb_zero_identidade(p, t))

law sbb_zero_decrementa:
  for +n: Nat
  for +w: Word(n)
  {Word.adc(n, w, Word.zero(n), True{}, False{}) == predecessor(n, w) : Word(n)}
def sbb_zero_decrementa(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{True{}, r}, Word.adc(p, t, Word.zero(p), True{}, False{}), predecessor(p, t), sbb_zero_decrementa(p, t))
        case WCon{True{}, +t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r}, Word.adc(p, t, Word.zero(p), True{}, True{}), t, sbb_zero_identidade(p, t))

def um(n: Nat) -> Word(1n+n):
  WCon{True{}, Word.zero(n)}

law somar_um_incrementa:
  for +n: Nat
  for +w: Word(1n+n)
  {Word.add(1n+n, w, um(n)) == Word.inc(1n+n, w) : Word(1n+n)}
def somar_um_incrementa(n, w):
  match w:
    case WCon{False{}, +t}:
      Equal.cong(Word(n), Word(1n+n), r => WCon{True{}, r}, Word.adc(n, t, Word.zero(n), False{}, False{}), t, adc_zero_identidade(n, t))
    case WCon{True{}, +t}:
      Equal.cong(Word(n), Word(1n+n), r => WCon{False{}, r}, Word.adc(n, t, Word.zero(n), False{}, True{}), Word.inc(n, t), adc_zero_incrementa(n, t))

law subtrair_um_decrementa:
  for +n: Nat
  for +w: Word(1n+n)
  {Word.sub(1n+n, w, um(n)) == predecessor(1n+n, w) : Word(1n+n)}
def subtrair_um_decrementa(n, w):
  match w:
    case WCon{False{}, +t}:
      Equal.cong(Word(n), Word(1n+n), r => WCon{True{}, r}, Word.adc(n, t, Word.zero(n), True{}, False{}), predecessor(n, t), sbb_zero_decrementa(n, t))
    case WCon{True{}, +t}:
      Equal.cong(Word(n), Word(1n+n), r => WCon{False{}, r}, Word.adc(n, t, Word.zero(n), True{}, True{}), t, sbb_zero_identidade(n, t))

law somar_subtrair_um_cancela:
  for +x: U32
  {((x + 1 : U32) - 1 : U32) == x : U32}
def somar_subtrair_um_cancela(x):
  match x:
    case U32{+w}:
      %Equal.sym(Word(32n), Word.add(32n, w, um(31n)), Word.inc(32n, w), somar_um_incrementa(31n, w)) :
        {U32{Word.sub(32n, _, um(31n))} == U32{w} : U32}
      %Equal.sym(Word(32n), Word.sub(32n, Word.inc(32n, w), um(31n)), predecessor(32n, Word.inc(32n, w)), subtrair_um_decrementa(31n, Word.inc(32n, w))) :
        {U32{_} == U32{w} : U32}
      Equal.cong(Word(32n), U32, r => U32{r}, predecessor(32n, Word.inc(32n, w)), w, predecessor_do_incremento(32n, w))

def zeros(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          zeros(p, t)
        case WCon{True{}, t}:
          False{}

def uns(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          False{}
        case WCon{True{}, t}:
          uns(p, t)

def maximo(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{True{}, maximo(p)}

law cmp_zero_bit:
  for b: Bool
  for c: Cmp
  {Cmp.is_eq(Word.cmp.fin(b, False{}, c)) == Bool.not(b) && Cmp.is_eq(c) : Bool}
def cmp_zero_bit(b, c):
  match b c:
    case False{} LT{}:
      {==}
    case False{} EQ{}:
      {==}
    case False{} GT{}:
      {==}
    case True{} LT{}:
      {==}
    case True{} EQ{}:
      {==}
    case True{} GT{}:
      {==}

law cmp_maximo_bit:
  for b: Bool
  for c: Cmp
  {Cmp.is_eq(Word.cmp.fin(b, True{}, c)) == b && Cmp.is_eq(c) : Bool}
def cmp_maximo_bit(b, c):
  match b c:
    case False{} LT{}:
      {==}
    case False{} EQ{}:
      {==}
    case False{} GT{}:
      {==}
    case True{} LT{}:
      {==}
    case True{} EQ{}:
      {==}
    case True{} GT{}:
      {==}

law comparacao_zero_reconhece_bits:
  for +n: Nat
  for +w: Word(n)
  {Cmp.is_eq(Word.cmp(n, w, Word.zero(n))) == zeros(n, w) : Bool}
def comparacao_zero_reconhece_bits(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(p, t, Word.zero(p)))), Cmp.is_eq(Word.cmp(p, t, Word.zero(p))), zeros(p, t),
            cmp_zero_bit(False{}, Word.cmp(p, t, Word.zero(p))), comparacao_zero_reconhece_bits(p, t))
        case WCon{True{}, t}:
          cmp_zero_bit(True{}, Word.cmp(p, t, Word.zero(p)))

law comparacao_maximo_reconhece_bits:
  for +n: Nat
  for +w: Word(n)
  {Cmp.is_eq(Word.cmp(n, w, maximo(n))) == uns(n, w) : Bool}
def comparacao_maximo_reconhece_bits(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          cmp_maximo_bit(False{}, Word.cmp(p, t, maximo(p)))
        case WCon{True{}, +t}:
          Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(True{}, True{}, Word.cmp(p, t, maximo(p)))), Cmp.is_eq(Word.cmp(p, t, maximo(p))), uns(p, t),
            cmp_maximo_bit(True{}, Word.cmp(p, t, maximo(p))), comparacao_maximo_reconhece_bits(p, t))

law incremento_zero_exatamente_no_maximo:
  for +n: Nat
  for +w: Word(n)
  {zeros(n, Word.inc(n, w)) == uns(n, w) : Bool}
def incremento_zero_exatamente_no_maximo(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          {==}
        case WCon{True{}, t}:
          incremento_zero_exatamente_no_maximo(p, t)

law soma_um_zero_exatamente_no_maximo:
  for +x: U32
  {U32.is_eq((x + 1 : U32), 0) == U32.is_eq(x, 4294967295) : Bool}
def soma_um_zero_exatamente_no_maximo(x):
  match x:
    case U32{+w}:
      %Equal.sym(Word(32n), Word.add(32n, w, um(31n)), Word.inc(32n, w), somar_um_incrementa(31n, w)) :
        {Cmp.is_eq(Word.cmp(32n, _, Word.zero(32n))) == Cmp.is_eq(Word.cmp(32n, w, maximo(32n))) : Bool}
      Equal.trans(Bool, Cmp.is_eq(Word.cmp(32n, Word.inc(32n, w), Word.zero(32n))), zeros(32n, Word.inc(32n, w)), Cmp.is_eq(Word.cmp(32n, w, maximo(32n))),
        comparacao_zero_reconhece_bits(32n, Word.inc(32n, w)),
        Equal.trans(Bool, zeros(32n, Word.inc(32n, w)), uns(32n, w), Cmp.is_eq(Word.cmp(32n, w, maximo(32n))), incremento_zero_exatamente_no_maximo(32n, w),
          Equal.sym(Bool, Cmp.is_eq(Word.cmp(32n, w, maximo(32n))), uns(32n, w), comparacao_maximo_reconhece_bits(32n, w))))

law igualdade_u32:
  for +x: U32
  for +y: U32
  for e: {U32.is_eq(x, y) == True{} : Bool}
  {x == y : U32}
def igualdade_u32(x, y, e):
  O.u32_igual(x, y, O.cmp_eq(U32.cmp(x, y), e))

law diminuir_sem_transporte_inverte_incremento:
  for +a: U32
  for +b: U32
  for nao_maximo: {U32.is_eq(b, 4294967295) == False{} : Bool}
  {C.diminuir64(B.Numero64{a, (b + 1 : U32)}) == B.Numero64{a, b} : B.Numero64}
def diminuir_sem_transporte_inverte_incremento(a, b, nao_maximo):
  %Equal.sym(Bool, U32.is_eq((b + 1 : U32), 0), False{},
    Equal.trans(Bool, U32.is_eq((b + 1 : U32), 0), U32.is_eq(b, 4294967295), False{}, soma_um_zero_exatamente_no_maximo(b), nao_maximo)) :
    {C.diminuir64_casos(_, U32.is_eq(a, 0), a, (b + 1 : U32)) == B.Numero64{a, b} : B.Numero64}
  Equal.cong(U32, B.Numero64, r => B.Numero64{a, r}, ((b + 1 : U32) - 1 : U32), b, somar_subtrair_um_cancela(b))

law diminuir_com_transporte_inverte_incremento:
  for +a: U32
  for +b: U32
  for maximo_b: {U32.is_eq(b, 4294967295) == True{} : Bool}
  for nao_maximo_a: {U32.is_eq(a, 4294967295) == False{} : Bool}
  {C.diminuir64(B.Numero64{(a + 1 : U32), 0}) == B.Numero64{a, b} : B.Numero64}
def diminuir_com_transporte_inverte_incremento(a, b, maximo_b, nao_maximo_a):
  %Equal.sym(Bool, U32.is_eq((a + 1 : U32), 0), False{},
    Equal.trans(Bool, U32.is_eq((a + 1 : U32), 0), U32.is_eq(a, 4294967295), False{}, soma_um_zero_exatamente_no_maximo(a), nao_maximo_a)) :
    {C.diminuir64_casos(True{}, _, (a + 1 : U32), 0) == B.Numero64{a, b} : B.Numero64}
  %Equal.sym(U32, b, 4294967295, igualdade_u32(b, 4294967295, maximo_b)) :
    {B.Numero64{((a + 1 : U32) - 1 : U32), 4294967295} == B.Numero64{a, _} : B.Numero64}
  Equal.cong(U32, B.Numero64, r => B.Numero64{r, 4294967295}, ((a + 1 : U32) - 1 : U32), a, somar_subtrair_um_cancela(a))

law incrementar64_casos_tem_antecessor_exato:
  for transporte: Bool
  for esgotado: Bool
  for +a: U32
  for +b: U32
  for -y: B.Numero64
  for eb: {U32.is_eq(b, 4294967295) == transporte : Bool}
  for ea: {U32.is_eq(a, 4294967295) == esgotado : Bool}
  for incremento: {B.incrementar64_casos(a, b, transporte, esgotado) == Some{y} : Maybe<&2, B.Numero64>}
  {C.diminuir64(y) == B.Numero64{a, b} : B.Numero64}
def incrementar64_casos_tem_antecessor_exato(transporte, esgotado, a, b, y, eb, ea, incremento):
  match transporte esgotado:
    case False{} _:
      %F.algum_injetivo(B.Numero64, B.Numero64{a, (b + 1 : U32)}, y, incremento) :
        {C.diminuir64(_) == B.Numero64{a, b} : B.Numero64}
      diminuir_sem_transporte_inverte_incremento(a, b, eb)
    case True{} False{}:
      %F.algum_injetivo(B.Numero64, B.Numero64{(a + 1 : U32), 0}, y, incremento) :
        {C.diminuir64(_) == B.Numero64{a, b} : B.Numero64}
      diminuir_com_transporte_inverte_incremento(a, b, eb, ea)
    case True{} True{}:
      L.ex_falso({C.diminuir64(y) == B.Numero64{a, b} : B.Numero64}, F.nenhum_nao_algum(B.Numero64, y, incremento))

law incrementar64_tem_antecessor_exato:
  for +x: B.Numero64
  for -y: B.Numero64
  for incremento: {B.incrementar64(Some{x}) == Some{y} : Maybe<&2, B.Numero64>}
  {C.diminuir64(y) == x : B.Numero64}
def incrementar64_tem_antecessor_exato(x, y, incremento):
  match x:
    case B.Numero64{+a, +b}:
      incrementar64_casos_tem_antecessor_exato(U32.is_eq(b, 4294967295), U32.is_eq(a, 4294967295), a, b, y, {==}, {==}, incremento)

# A existencia do antecessor e extraida do resultado, nao presumida.
type Antecessor<-anterior: Maybe<&2, B.Numero64>, -atual: B.Numero64> is Type:
  Antecessor{numero: B.Numero64,
    medido: {anterior == Some{numero} : Maybe<&2, B.Numero64>},
    decremento: {C.diminuir64(atual) == numero : B.Numero64}}

law inverter_incremento_aceito:
  for anterior: Maybe<&2, B.Numero64>
  for -atual: B.Numero64
  for incremento: {B.incrementar64(anterior) == Some{atual} : Maybe<&2, B.Numero64>}
  Antecessor<anterior, atual>
def inverter_incremento_aceito(anterior, atual, incremento):
  match anterior:
    case None{}:
      L.ex_falso(Antecessor<None{}, atual>, F.nenhum_nao_algum(B.Numero64, atual, incremento))
    case Some{+x}:
      Antecessor{x, {==}, incrementar64_tem_antecessor_exato(x, atual, incremento)}

law nat64_sucessor_tem_antecessor_exato:
  for +n: Nat
  for -atual: B.Numero64
  for medido: {B.nat64(1n+n) == Some{atual} : Maybe<&2, B.Numero64>}
  Antecessor<B.nat64(n), atual>
def nat64_sucessor_tem_antecessor_exato(n, atual, medido):
  inverter_incremento_aceito(B.nat64(n), atual, medido)

# Qualquer octeto consumido preserva a medida EXATA do corpo restante.
def medida_decrementada(-n: Nat, -atual: B.Numero64, provas: Antecessor<B.nat64(n), atual>) ->
  {B.nat64(n) == Some{C.diminuir64(atual)} : Maybe<&2, B.Numero64>}:
  match provas:
    case Antecessor{numero, medido, decremento}:
      %Equal.sym(B.Numero64, C.diminuir64(atual), numero, decremento) :
        {B.nat64(n) == Some{_} : Maybe<&2, B.Numero64>}
      medido

law comprimento_da_cauda_e_decremento_do_corpo:
  for +b: U32
  for +bs: List<&2, U32>
  for -corpo: B.Numero64
  for medido: {B.nat64(B.comprimento(Con{b, bs})) == Some{corpo} : Maybe<&2, B.Numero64>}
  {B.nat64(B.comprimento(bs)) == Some{C.diminuir64(corpo)} : Maybe<&2, B.Numero64>}
def comprimento_da_cauda_e_decremento_do_corpo(b, bs, corpo, medido):
  medida_decrementada(B.comprimento(bs), corpo, nat64_sucessor_tem_antecessor_exato(B.comprimento(bs), corpo, medido))

law e_falso_direita:
  for b: Bool
  {b && False{} == False{} : Bool}
def e_falso_direita(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law incremento_sem_transporte_nao_zero:
  for +a: U32
  for +b: U32
  for nao_maximo: {U32.is_eq(b, 4294967295) == False{} : Bool}
  {C.zero64(B.Numero64{a, (b + 1 : U32)}) == False{} : Bool}
def incremento_sem_transporte_nao_zero(a, b, nao_maximo):
  %Equal.sym(Bool, U32.is_eq((b + 1 : U32), 0), False{},
    Equal.trans(Bool, U32.is_eq((b + 1 : U32), 0), U32.is_eq(b, 4294967295), False{}, soma_um_zero_exatamente_no_maximo(b), nao_maximo)) :
    {U32.is_eq(a, 0) && _ == False{} : Bool}
  e_falso_direita(U32.is_eq(a, 0))

law incremento_com_transporte_nao_zero:
  for +a: U32
  for nao_maximo: {U32.is_eq(a, 4294967295) == False{} : Bool}
  {C.zero64(B.Numero64{(a + 1 : U32), 0}) == False{} : Bool}
def incremento_com_transporte_nao_zero(a, nao_maximo):
  %Equal.sym(Bool, U32.is_eq((a + 1 : U32), 0), False{},
    Equal.trans(Bool, U32.is_eq((a + 1 : U32), 0), U32.is_eq(a, 4294967295), False{}, soma_um_zero_exatamente_no_maximo(a), nao_maximo)) :
    {_ && True{} == False{} : Bool}
  {==}

law incrementar64_casos_nunca_envolve_para_zero:
  for transporte: Bool
  for esgotado: Bool
  for +a: U32
  for +b: U32
  for -y: B.Numero64
  for eb: {U32.is_eq(b, 4294967295) == transporte : Bool}
  for ea: {U32.is_eq(a, 4294967295) == esgotado : Bool}
  for incremento: {B.incrementar64_casos(a, b, transporte, esgotado) == Some{y} : Maybe<&2, B.Numero64>}
  {C.zero64(y) == False{} : Bool}
def incrementar64_casos_nunca_envolve_para_zero(transporte, esgotado, a, b, y, eb, ea, incremento):
  match transporte esgotado:
    case False{} _:
      %F.algum_injetivo(B.Numero64, B.Numero64{a, (b + 1 : U32)}, y, incremento) : {C.zero64(_) == False{} : Bool}
      incremento_sem_transporte_nao_zero(a, b, eb)
    case True{} False{}:
      %F.algum_injetivo(B.Numero64, B.Numero64{(a + 1 : U32), 0}, y, incremento) : {C.zero64(_) == False{} : Bool}
      incremento_com_transporte_nao_zero(a, ea)
    case True{} True{}:
      L.ex_falso({C.zero64(y) == False{} : Bool}, F.nenhum_nao_algum(B.Numero64, y, incremento))

law incremento_aceito_nunca_envolve_para_zero:
  for anterior: Maybe<&2, B.Numero64>
  for -y: B.Numero64
  for incremento: {B.incrementar64(anterior) == Some{y} : Maybe<&2, B.Numero64>}
  {C.zero64(y) == False{} : Bool}
def incremento_aceito_nunca_envolve_para_zero(anterior, y, incremento):
  match anterior:
    case None{}:
      L.ex_falso({C.zero64(y) == False{} : Bool}, F.nenhum_nao_algum(B.Numero64, y, incremento))
    case Some{B.Numero64{+a, +b}}:
      incrementar64_casos_nunca_envolve_para_zero(U32.is_eq(b, 4294967295), U32.is_eq(a, 4294967295), a, b, y, {==}, {==}, incremento)

law nat64_sucessor_nunca_zero:
  for n: Nat
  for -atual: B.Numero64
  for medido: {B.nat64(1n+n) == Some{atual} : Maybe<&2, B.Numero64>}
  {C.zero64(atual) == False{} : Bool}
def nat64_sucessor_nunca_zero(n, atual, medido):
  incremento_aceito_nunca_envolve_para_zero(B.nat64(n), atual, medido)

def zero_e_nao_zero(-x: B.Numero64,
  zero: {x == B.Numero64{0, 0} : B.Numero64},
  nao_zero: {C.zero64(x) == False{} : Bool}) -> Empty:
  F.falso_nao_verdadeiro(Equal.sym(Bool, True{}, False{},
    (%zero : {C.zero64(_) == False{} : Bool}
      nao_zero)))

law nat64_e_injetivo_nos_resultados_representaveis:
  for +a: Nat
  for +b: Nat
  for -numero: B.Numero64
  for ma: {B.nat64(a) == Some{numero} : Maybe<&2, B.Numero64>}
  for mb: {B.nat64(b) == Some{numero} : Maybe<&2, B.Numero64>}
  {a == b : Nat}
def nat64_e_injetivo_nos_resultados_representaveis(a, b, numero, ma, mb):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+p:
      L.ex_falso({0n == 1n+p : Nat}, zero_e_nao_zero(numero,
        Equal.sym(B.Numero64, B.Numero64{0, 0}, numero, F.algum_injetivo(B.Numero64, B.Numero64{0, 0}, numero, ma)), nat64_sucessor_nunca_zero(p, numero, mb)))
    case 1n+p 0n:
      L.ex_falso({1n+p == 0n : Nat}, zero_e_nao_zero(numero,
        Equal.sym(B.Numero64, B.Numero64{0, 0}, numero, F.algum_injetivo(B.Numero64, B.Numero64{0, 0}, numero, mb)), nat64_sucessor_nunca_zero(p, numero, ma)))
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q,
        nat64_e_injetivo_nos_resultados_representaveis(p, q, C.diminuir64(numero),
          medida_decrementada(p, numero, nat64_sucessor_tem_antecessor_exato(p, numero, ma)),
          medida_decrementada(q, numero, nat64_sucessor_tem_antecessor_exato(q, numero, mb))))

law zero64_reflete_contagem_natural:
  for n: Nat
  for -numero: B.Numero64
  for medido: {B.nat64(n) == Some{numero} : Maybe<&2, B.Numero64>}
  {C.zero64(numero) == Nat.is_eq(n, 0n) : Bool}
def zero64_reflete_contagem_natural(n, numero, medido):
  match n:
    case 0n:
      %F.algum_injetivo(B.Numero64, B.Numero64{0, 0}, numero, medido) : {C.zero64(_) == True{} : Bool}
      {==}
    case 1n+p:
      nat64_sucessor_nunca_zero(p, numero, medido)

law um64_so_reconhece_um:
  for +numero: B.Numero64
  for +e: {C.um64(numero) == True{} : Bool}
  {numero == B.Numero64{0, 1} : B.Numero64}
def um64_so_reconhece_um(numero, e):
  match numero:
    case B.Numero64{+a, +b}:
      %Equal.sym(U32, a, 0, igualdade_u32(a, 0, F.e_booleano_esquerda(U32.is_eq(a, 0), U32.is_eq(b, 1), e))) :
        {B.Numero64{_, b} == B.Numero64{0, 1} : B.Numero64}
      Equal.cong(U32, B.Numero64, x => B.Numero64{0, x}, b, 1,
        igualdade_u32(b, 1, F.e_booleano_direita(U32.is_eq(a, 0), U32.is_eq(b, 1), e)))

law falso_se_verdadeiro_impossivel:
  for +b: Bool
  for impossivel: {b == True{} : Bool} -> Empty
  {b == False{} : Bool}
def falso_se_verdadeiro_impossivel(b, impossivel):
  match b:
    case False{}:
      {==}
    case True{}:
      L.ex_falso({True{} == False{} : Bool}, impossivel({==}))

law um64_reflete_contagem_natural:
  for +n: Nat
  for +numero: B.Numero64
  for medido: {B.nat64(n) == Some{numero} : Maybe<&2, B.Numero64>}
  {C.um64(numero) == Nat.is_eq(n, 1n) : Bool}
def um64_reflete_contagem_natural(n, numero, medido):
  match n:
    case 0n:
      %F.algum_injetivo(B.Numero64, B.Numero64{0, 0}, numero, medido) : {C.um64(_) == False{} : Bool}
      {==}
    case 1n:
      %F.algum_injetivo(B.Numero64, B.Numero64{0, 1}, numero, medido) : {C.um64(_) == True{} : Bool}
      {==}
    case 2n+p:
      falso_se_verdadeiro_impossivel(C.um64(numero), e =>
        F.falso_nao_verdadeiro(Equal.cong(Nat, Bool, k => Nat.is_eq(k, 1n), 2n+p, 1n,
          nat64_e_injetivo_nos_resultados_representaveis(2n+p, 1n, B.Numero64{0, 1},
            (%um64_so_reconhece_um(numero, e) : {B.nat64(2n+p) == Some{_} : Maybe<&2, B.Numero64>}
              medido), {==}))))


def corpo_quadro(q: R.Quadro) -> B.Numero64:
  R.Quadro{corpo, teto, m} = q
  corpo

law contador_do_corpo_mede_exatamente_o_sufixo:
  for xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +m: C.Maquina
  for medido: {B.nat64(B.comprimento(B.concatenar(xs, ys))) == Some{corpo} : Maybe<&2, B.Numero64>}
  {B.nat64(B.comprimento(ys)) == Some{corpo_quadro(R.executar(xs, R.Quadro{corpo, teto, m}))} : Maybe<&2, B.Numero64>}
def contador_do_corpo_mede_exatamente_o_sufixo(xs, ys, corpo, teto, m, medido):
  match xs:
    case Nil{}:
      medido
    case Con{+b, +t}:
      +resto = C.diminuir64(corpo)
      +livre = C.diminuir64(teto)
      contador_do_corpo_mede_exatamente_o_sufixo(t, ys, resto, livre, C.passo(m, b, resto, livre),
        medida_decrementada(B.comprimento(B.concatenar(t, ys)), corpo,
          nat64_sucessor_tem_antecessor_exato(B.comprimento(B.concatenar(t, ys)), corpo, medido)))

law consumo_integral_esgota_exatamente_o_corpo:
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +m: C.Maquina
  for medido: {B.nat64(B.comprimento(bs)) == Some{corpo} : Maybe<&2, B.Numero64>}
  {corpo_quadro(R.executar(bs, R.Quadro{corpo, teto, m})) == B.Numero64{0, 0} : B.Numero64}
def consumo_integral_esgota_exatamente_o_corpo(bs, corpo, teto, m, medido):
  match bs:
    case Nil{}:
      Equal.sym(B.Numero64, B.Numero64{0, 0}, corpo, F.algum_injetivo(B.Numero64, B.Numero64{0, 0}, corpo, medido))
    case Con{+b, +t}:
      +resto = C.diminuir64(corpo)
      +livre = C.diminuir64(teto)
      consumo_integral_esgota_exatamente_o_corpo(t, resto, livre, C.passo(m, b, resto, livre), comprimento_da_cauda_e_decremento_do_corpo(b, t, corpo, medido))

law incremento_do_predecessor:
  for +n: Nat
  for +w: Word(n)
  {Word.inc(n, predecessor(n, w)) == w : Word(n)}
def incremento_do_predecessor(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{True{}, t}:
          {==}
        case WCon{False{}, +t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r}, Word.inc(p, predecessor(p, t)), t, incremento_do_predecessor(p, t))

law subtrair_somar_um_cancela:
  for +x: U32
  {((x - 1 : U32) + 1 : U32) == x : U32}
def subtrair_somar_um_cancela(x):
  match x:
    case U32{+w}:
      %Equal.sym(Word(32n), Word.sub(32n, w, um(31n)), predecessor(32n, w), subtrair_um_decrementa(31n, w)) :
        {U32{Word.add(32n, _, um(31n))} == U32{w} : U32}
      %Equal.sym(Word(32n), Word.add(32n, predecessor(32n, w), um(31n)), Word.inc(32n, predecessor(32n, w)), somar_um_incrementa(31n, predecessor(32n, w))) :
        {U32{_} == U32{w} : U32}
      Equal.cong(Word(32n), U32, r => U32{r}, Word.inc(32n, predecessor(32n, w)), w, incremento_do_predecessor(32n, w))

law predecessor_maximo_exatamente_no_zero:
  for +n: Nat
  for +w: Word(n)
  {uns(n, predecessor(n, w)) == zeros(n, w) : Bool}
def predecessor_maximo_exatamente_no_zero(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{True{}, t}:
          {==}
        case WCon{False{}, t}:
          predecessor_maximo_exatamente_no_zero(p, t)

law subtracao_um_maximo_exatamente_no_zero:
  for +x: U32
  {U32.is_eq((x - 1 : U32), 4294967295) == U32.is_eq(x, 0) : Bool}
def subtracao_um_maximo_exatamente_no_zero(x):
  match x:
    case U32{+w}:
      %Equal.sym(Word(32n), Word.sub(32n, w, um(31n)), predecessor(32n, w), subtrair_um_decrementa(31n, w)) :
        {Cmp.is_eq(Word.cmp(32n, _, maximo(32n))) == Cmp.is_eq(Word.cmp(32n, w, Word.zero(32n))) : Bool}
      Equal.trans(Bool, Cmp.is_eq(Word.cmp(32n, predecessor(32n, w), maximo(32n))), uns(32n, predecessor(32n, w)), Cmp.is_eq(Word.cmp(32n, w, Word.zero(32n))),
        comparacao_maximo_reconhece_bits(32n, predecessor(32n, w)),
        Equal.trans(Bool, uns(32n, predecessor(32n, w)), zeros(32n, w), Cmp.is_eq(Word.cmp(32n, w, Word.zero(32n))), predecessor_maximo_exatamente_no_zero(32n, w),
          Equal.sym(Bool, Cmp.is_eq(Word.cmp(32n, w, Word.zero(32n))), zeros(32n, w), comparacao_zero_reconhece_bits(32n, w))))

law aumentar_apos_diminuir_sem_transporte:
  for +a: U32
  for +b: U32
  for nao_zero: {U32.is_eq(b, 0) == False{} : Bool}
  {B.incrementar64(Some{B.Numero64{a, (b - 1 : U32)}}) == Some{B.Numero64{a, b}} : Maybe<&2, B.Numero64>}
def aumentar_apos_diminuir_sem_transporte(a, b, nao_zero):
  %Equal.sym(Bool, U32.is_eq((b - 1 : U32), 4294967295), False{},
    Equal.trans(Bool, U32.is_eq((b - 1 : U32), 4294967295), U32.is_eq(b, 0), False{}, subtracao_um_maximo_exatamente_no_zero(b), nao_zero)) :
    {B.incrementar64_casos(a, (b - 1 : U32), _, U32.is_eq(a, 4294967295)) == Some{B.Numero64{a, b}} : Maybe<&2, B.Numero64>}
  Equal.cong(U32, Maybe<&2, B.Numero64>, r => Some{B.Numero64{a, r}}, ((b - 1 : U32) + 1 : U32), b, subtrair_somar_um_cancela(b))

law aumentar_apos_diminuir_com_transporte:
  for +a: U32
  for nao_zero: {U32.is_eq(a, 0) == False{} : Bool}
  {B.incrementar64(Some{B.Numero64{(a - 1 : U32), 4294967295}}) == Some{B.Numero64{a, 0}} : Maybe<&2, B.Numero64>}
def aumentar_apos_diminuir_com_transporte(a, nao_zero):
  %Equal.sym(Bool, U32.is_eq((a - 1 : U32), 4294967295), False{},
    Equal.trans(Bool, U32.is_eq((a - 1 : U32), 4294967295), U32.is_eq(a, 0), False{}, subtracao_um_maximo_exatamente_no_zero(a), nao_zero)) :
    {B.incrementar64_casos((a - 1 : U32), 4294967295, True{}, _) == Some{B.Numero64{a, 0}} : Maybe<&2, B.Numero64>}
  Equal.cong(U32, Maybe<&2, B.Numero64>, r => Some{B.Numero64{r, 0}}, ((a - 1 : U32) + 1 : U32), a, subtrair_somar_um_cancela(a))

law zero64_so_reconhece_zero:
  for +n: B.Numero64
  for +zero: {C.zero64(n) == True{} : Bool}
  {n == B.Numero64{0, 0} : B.Numero64}
def zero64_so_reconhece_zero(n, zero):
  match n:
    case B.Numero64{+a, +b}:
      %Equal.sym(U32, a, 0, igualdade_u32(a, 0, F.e_booleano_esquerda(U32.is_eq(a, 0), U32.is_eq(b, 0), zero))) :
        {B.Numero64{_, b} == B.Numero64{0, 0} : B.Numero64}
      Equal.cong(U32, B.Numero64, r => B.Numero64{0, r}, b, 0,
        igualdade_u32(b, 0, F.e_booleano_direita(U32.is_eq(a, 0), U32.is_eq(b, 0), zero)))

# Este helper transporta os testes booleanos reais para os tres ramos
# de diminuir64, sem tomar overflow como uma igualdade modular silenciosa.
def inverter_diminuir_casos(baixo_zero: Bool, alto_zero: Bool, +a: U32, +b: U32,
  eb: {U32.is_eq(b, 0) == baixo_zero : Bool},
  ea: {U32.is_eq(a, 0) == alto_zero : Bool},
  nao_zero: {alto_zero && baixo_zero == False{} : Bool}) ->
  {B.incrementar64(Some{C.diminuir64_casos(baixo_zero, alto_zero, a, b)}) == Some{B.Numero64{a, b}} : Maybe<&2, B.Numero64>}:
  match baixo_zero alto_zero:
    case False{} _:
      aumentar_apos_diminuir_sem_transporte(a, b, eb)
    case True{} False{}:
      %Equal.sym(U32, b, 0, igualdade_u32(b, 0, eb)) :
        {B.incrementar64(Some{B.Numero64{(a - 1 : U32), 4294967295}}) == Some{B.Numero64{a, _}} : Maybe<&2, B.Numero64>}
      aumentar_apos_diminuir_com_transporte(a, ea)
    case True{} True{}:
      F.absurdo_booleano({B.incrementar64(Some{B.Numero64{0, 0}}) == Some{B.Numero64{a, b}} : Maybe<&2, B.Numero64>}, Equal.sym(Bool, True{}, False{}, nao_zero))

law incrementar_inverte_diminuir_quando_positivo:
  for +n: B.Numero64
  for nao_zero: {C.zero64(n) == False{} : Bool}
  {B.incrementar64(Some{C.diminuir64(n)}) == Some{n} : Maybe<&2, B.Numero64>}
def incrementar_inverte_diminuir_quando_positivo(n, nao_zero):
  match n:
    case B.Numero64{+a, +b}:
      inverter_diminuir_casos(U32.is_eq(b, 0), U32.is_eq(a, 0), a, b, {==}, {==}, nao_zero)

law decremento_positivo_exige_original_positivo:
  for +n: B.Numero64
  for positivo: {C.zero64(C.diminuir64(n)) == False{} : Bool}
  {C.zero64(n) == False{} : Bool}
def decremento_positivo_exige_original_positivo(n, positivo):
  falso_se_verdadeiro_impossivel(C.zero64(n), e =>
    F.falso_nao_verdadeiro(Equal.sym(Bool, True{}, False{},
      (%zero64_so_reconhece_zero(n, e) : {C.zero64(C.diminuir64(_)) == False{} : Bool}
        positivo))))

# Protocolo exato de ultimo/restantes usado por emitir nas duas aridades.
def ultimos(n: Nat, +q: B.Numero64) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n:
      C.um64(q)
    case 2n+p:
      Bool.not(C.um64(q)) && ultimos(1n+p, C.diminuir64(q))

law ultimos_aceitos_reconstroem_a_contagem_original:
  for +n: Nat
  for +q: B.Numero64
  for +aceito: {ultimos(n, q) == True{} : Bool}
  {B.nat64(n) == Some{q} : Maybe<&2, B.Numero64>}
def ultimos_aceitos_reconstroem_a_contagem_original(n, q, aceito):
  match n:
    case 0n:
      F.absurdo_booleano({Some{B.Numero64{0, 0}} == Some{q} : Maybe<&2, B.Numero64>}, aceito)
    case 1n:
      %Equal.sym(B.Numero64, q, B.Numero64{0, 1}, um64_so_reconhece_um(q, aceito)) :
        {Some{B.Numero64{0, 1}} == Some{_} : Maybe<&2, B.Numero64>}
      {==}
    case 2n+p:
      +cauda = ultimos_aceitos_reconstroem_a_contagem_original(1n+p, C.diminuir64(q),
        F.e_booleano_direita(Bool.not(C.um64(q)), ultimos(1n+p, C.diminuir64(q)), aceito))
      %Equal.sym(Maybe<&2, B.Numero64>, B.nat64(1n+p), Some{C.diminuir64(q)}, cauda) :
        {B.incrementar64(_) == Some{q} : Maybe<&2, B.Numero64>}
      incrementar_inverte_diminuir_quando_positivo(q,
        decremento_positivo_exige_original_positivo(q, nat64_sucessor_nunca_zero(p, C.diminuir64(q), cauda)))

law contagem_representavel_completa_o_protocolo_de_ultimos:
  for +n: Nat
  for +q: B.Numero64
  for +medido: {B.nat64(1n+n) == Some{q} : Maybe<&2, B.Numero64>}
  {ultimos(1n+n, q) == True{} : Bool}
def contagem_representavel_completa_o_protocolo_de_ultimos(n, q, medido):
  match n:
    case 0n:
      Equal.trans(Bool, C.um64(q), Nat.is_eq(1n, 1n), True{}, um64_reflete_contagem_natural(1n, q, medido), {==})
    case 1n+p:
      %Equal.sym(Bool, C.um64(q), False{}, um64_reflete_contagem_natural(2n+p, q, medido)) :
        {Bool.not(_) && ultimos(1n+p, C.diminuir64(q)) == True{} : Bool}
      contagem_representavel_completa_o_protocolo_de_ultimos(p, C.diminuir64(q),
        medida_decrementada(1n+p, q, nat64_sucessor_tem_antecessor_exato(1n+p, q, medido)))
