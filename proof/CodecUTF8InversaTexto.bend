# Inversao de QUALQUER entrada aceita. A inducao percorre a lista original
# byte por byte; Prefixo guarda somente o trecho escalar ainda incompleto.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./CodecUTF8.bend as T
import ./CodecUTF8Bits.bend as X
import ./CodecUTF8InversaBits.bend as I
import ./CodecUTF8Inversa.bend as E
import ./CodecUTF8InversaCanonica.bend as K
import ./CodecPalavrasWord.bend as W
import ./Fundamentos.bend as F

type Prefixo is Data:
  Livre{}
  Dois{hi: Word(5n)}
  Tres1{hi: Word(4n)}
  Tres2{hi: Word(4n), b0: Word(6n)}
  Quatro1{hi: Word(3n)}
  Quatro2{hi: Word(3n), b0: Word(6n)}
  Quatro3{hi: Word(3n), b0: Word(6n), b1: Word(6n)}

def inicio2(hi: Word(5n)) -> U32:
  U32{W.juntar(5n, 27n, hi, Word.zero(27n))}

def inicio3(hi: Word(4n)) -> U32:
  U32{W.juntar(4n, 28n, hi, Word.zero(28n))}

def inicio4(hi: Word(3n)) -> U32:
  U32{W.juntar(3n, 29n, hi, Word.zero(29n))}

def unicode(p: Prefixo) -> C.Unicode:
  match p:
    case Livre{}:
      C.Inicio{}
    case Dois{hi}:
      C.Continua{1n, inicio2(hi), 128}
    case Tres1{hi}:
      C.Continua{2n, inicio3(hi), 2048}
    case Tres2{hi, b0}:
      C.Continua{1n, E.acumular(inicio3(hi), b0), 2048}
    case Quatro1{hi}:
      C.Continua{3n, inicio4(hi), 65536}
    case Quatro2{hi, b0}:
      C.Continua{2n, E.acumular(inicio4(hi), b0), 65536}
    case Quatro3{hi, b0, b1}:
      C.Continua{1n, E.acumular(E.acumular(inicio4(hi), b0), b1), 65536}

def pendentes(p: Prefixo) -> List<&2, U32>:
  match p:
    case Livre{}:
      []
    case Dois{hi}:
      [I.prefixo2(hi)]
    case Tres1{hi}:
      [I.prefixo3(hi)]
    case Tres2{hi, b0}:
      [I.prefixo3(hi), X.continuacao(b0)]
    case Quatro1{hi}:
      [I.prefixo4(hi)]
    case Quatro2{hi, b0}:
      [I.prefixo4(hi), X.continuacao(b0)]
    case Quatro3{hi, b0, b1}:
      [I.prefixo4(hi), X.continuacao(b0), X.continuacao(b1)]

def Pendente(p: Prefixo) -> Type:
  match p:
    case Livre{}:
      Empty
    case _:
      Unit

def restante(p: Prefixo, bs: List<&2, U32>) -> List<&2, U32>:
  B.concatenar(pendentes(p), bs)

def codificar_acumulado(acc: String, bs: List<&2, U32>) -> List<&2, U32>:
  match acc:
    case SNil{}:
      bs
    case SCon{Chr{cp}, tail}:
      codificar_acumulado(tail, B.concatenar(B.utf8_codigo(cp), bs))

def Aceita(bs: List<&2, U32>, t: T.Texto, s: String) -> Type:
  {T.finalizar_texto(T.percorrer_texto(bs, t)) == Some{s} : Maybe<&2, String>}

def Inverte(bs: List<&2, U32>, p: Prefixo, acc: String, s: String) -> Type:
  {B.utf8(s) == codificar_acumulado(acc, restante(p, bs)) : List<&2, U32>}

def Sufixo(bs: List<&2, U32>) -> Type:
  @p: Prefixo -> @acc: String -> @s: String ->
  Aceita(bs, T.Lendo{unicode(p), acc}, s) -> Inverte(bs, p, acc, s)

def Passo(p: Prefixo, b: U32, tail: List<&2, U32>, acc: String, s: String) -> Type:
  Aceita(tail, T.passo_texto(T.Lendo{unicode(p), acc}, b), s) -> Inverte(Con{b, tail}, p, acc, s)

law utf8_reverse_acumulado:
  for +s: String
  for +acc: String
  {B.utf8(String.reverse.go(s, acc)) == codificar_acumulado(s, B.utf8(acc)) : List<&2, U32>}
def utf8_reverse_acumulado(s, acc):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{cp}, tail}:
      utf8_reverse_acumulado(tail, SCon{Chr{cp}, acc})

law percorrer_invalido:
  for +bs: List<&2, U32>
  {T.percorrer_texto(bs, T.TextoInvalido{}) == T.TextoInvalido{} : T.Texto}
def percorrer_invalido(bs):
  match bs:
    case Nil{}:
      {==}
    case Con{b, tail}:
      percorrer_invalido(tail)

def invalido_nao_aceita(-A: Type, +bs: List<&2, U32>, -s: String, aceito: Aceita(bs, T.TextoInvalido{}, s)) -> A:
  L.ex_falso(A, F.nenhum_nao_algum(String, s,
    Equal.trans(Maybe<&2, String>, None{}, T.finalizar_texto(T.percorrer_texto(bs, T.TextoInvalido{})), Some{s},
      Equal.cong(T.Texto, Maybe<&2, String>, t => T.finalizar_texto(t), T.TextoInvalido{}, T.percorrer_texto(bs, T.TextoInvalido{}),
        Equal.sym(T.Texto, T.percorrer_texto(bs, T.TextoInvalido{}), T.TextoInvalido{}, percorrer_invalido(bs))), aceito)))

law fim_inverte:
  for +p: Prefixo
  for +acc: String
  for +s: String
  for aceito: Aceita([], T.Lendo{unicode(p), acc}, s)
  Inverte([], p, acc, s)
def fim_inverte(p, acc, s, aceito):
  match p:
    case Livre{}:
      Equal.trans(List<&2, U32>, B.utf8(s), B.utf8(String.reverse(acc)), codificar_acumulado(acc, []),
        Equal.cong(String, List<&2, U32>, z => B.utf8(z), s, String.reverse(acc),
          Equal.sym(String, String.reverse(acc), s, F.algum_injetivo(String, String.reverse(acc), s, aceito))),
        utf8_reverse_acumulado(acc, ""))
    case Dois{hi}:
      L.ex_falso(Inverte([], p, acc, s), F.nenhum_nao_algum(String, s, aceito))
    case Tres1{hi}:
      L.ex_falso(Inverte([], p, acc, s), F.nenhum_nao_algum(String, s, aceito))
    case Tres2{hi, b0}:
      L.ex_falso(Inverte([], p, acc, s), F.nenhum_nao_algum(String, s, aceito))
    case Quatro1{hi}:
      L.ex_falso(Inverte([], p, acc, s), F.nenhum_nao_algum(String, s, aceito))
    case Quatro2{hi, b0}:
      L.ex_falso(Inverte([], p, acc, s), F.nenhum_nao_algum(String, s, aceito))
    case Quatro3{hi, b0, b1}:
      L.ex_falso(Inverte([], p, acc, s), F.nenhum_nao_algum(String, s, aceito))

law caractere_inverte:
  for +cp: U32
  for +bytes: List<&2, U32>
  for +tail: List<&2, U32>
  for +acc: String
  for +s: String
  for ih: Sufixo(tail)
  for recodifica: {B.utf8_codigo(cp) == bytes : List<&2, U32>}
  for aceito: Aceita(tail, T.Lendo{C.Inicio{}, SCon{Chr{cp}, acc}}, s)
  {B.utf8(s) == codificar_acumulado(acc, B.concatenar(bytes, tail)) : List<&2, U32>}
def caractere_inverte(cp, bytes, tail, acc, s, ih, recodifica, aceito):
  %recodifica : {B.utf8(s) == codificar_acumulado(acc, B.concatenar(_, tail)) : List<&2, U32>}
  ih(Livre{}, SCon{Chr{cp}, acc}, s, aceito)

law conferido_inverte:
  for ok: Bool
  for +cp: U32
  for +bytes: List<&2, U32>
  for +tail: List<&2, U32>
  for +acc: String
  for +s: String
  for ih: Sufixo(tail)
  for recodifica: {ok == True{} : Bool} -> {B.utf8_codigo(cp) == bytes : List<&2, U32>}
  for aceito: Aceita(tail, T.juntar(C.escalar_conferido(ok, cp), acc), s)
  {B.utf8(s) == codificar_acumulado(acc, B.concatenar(bytes, tail)) : List<&2, U32>}
def conferido_inverte(ok, cp, bytes, tail, acc, s, ih, recodifica, aceito):
  match ok:
    case False{}:
      invalido_nao_aceita({B.utf8(s) == codificar_acumulado(acc, B.concatenar(bytes, tail)) : List<&2, U32>}, tail, s, aceito)
    case True{}:
      caractere_inverte(cp, bytes, tail, acc, s, ih, recodifica({==}), aceito)

def InicialParcial(n: Nat, base: U32, minimo: U32, b: U32, tail: List<&2, U32>, acc: String, s: String) -> Type:
  Aceita(tail, T.Lendo{C.Continua{n, (b - base : U32), minimo}, acc}, s) ->
  {B.utf8(s) == codificar_acumulado(acc, Con{b, tail}) : List<&2, U32>}

law inicial2_inverte:
  for +b: U32
  for +tail: List<&2, U32>
  for +acc: String
  for +s: String
  for forma: {b == I.prefixo2(W.ajustar(5n, 32n, X.bits(b))) : U32}
  for ih: Sufixo(tail)
  InicialParcial(1n, 192, 128, b, tail, acc, s)
def inicial2_inverte(b, tail, acc, s, forma, ih):
  %Equal.sym(U32, b, I.prefixo2(W.ajustar(5n, 32n, X.bits(b))), forma) : InicialParcial(1n, 192, 128, _, tail, acc, s)
  aceito => ih(Dois{W.ajustar(5n, 32n, X.bits(b))}, acc, s,
    %I.prefixo2_subtrair(W.ajustar(5n, 32n, X.bits(b))) : Aceita(tail, T.Lendo{C.Continua{1n, _, 128}, acc}, s)
    aceito)

law inicial3_inverte:
  for +b: U32
  for +tail: List<&2, U32>
  for +acc: String
  for +s: String
  for forma: {b == I.prefixo3(W.ajustar(4n, 32n, X.bits(b))) : U32}
  for ih: Sufixo(tail)
  InicialParcial(2n, 224, 2048, b, tail, acc, s)
def inicial3_inverte(b, tail, acc, s, forma, ih):
  %Equal.sym(U32, b, I.prefixo3(W.ajustar(4n, 32n, X.bits(b))), forma) : InicialParcial(2n, 224, 2048, _, tail, acc, s)
  aceito => ih(Tres1{W.ajustar(4n, 32n, X.bits(b))}, acc, s,
    %I.prefixo3_subtrair(W.ajustar(4n, 32n, X.bits(b))) : Aceita(tail, T.Lendo{C.Continua{2n, _, 2048}, acc}, s)
    aceito)

law inicial4_inverte:
  for +b: U32
  for +tail: List<&2, U32>
  for +acc: String
  for +s: String
  for forma: {b == I.prefixo4(W.ajustar(3n, 32n, X.bits(b))) : U32}
  for ih: Sufixo(tail)
  InicialParcial(3n, 240, 65536, b, tail, acc, s)
def inicial4_inverte(b, tail, acc, s, forma, ih):
  %Equal.sym(U32, b, I.prefixo4(W.ajustar(3n, 32n, X.bits(b))), forma) : InicialParcial(3n, 240, 65536, _, tail, acc, s)
  aceito => ih(Quatro1{W.ajustar(3n, 32n, X.bits(b))}, acc, s,
    %I.prefixo4_subtrair(W.ajustar(3n, 32n, X.bits(b))) : Aceita(tail, T.Lendo{C.Continua{3n, _, 65536}, acc}, s)
    aceito)

law iniciar_inverte:
  for ascii: Bool
  for dois: Bool
  for tres: Bool
  for quatro: Bool
  for +b: U32
  for +tail: List<&2, U32>
  for +acc: String
  for +s: String
  for a: {U32.is_lt(b, 128) == ascii : Bool}
  for +d: {U32.is_ge(b, 194) && U32.is_le(b, 223) == dois : Bool}
  for +t: {U32.is_ge(b, 224) && U32.is_le(b, 239) == tres : Bool}
  for +q: {U32.is_ge(b, 240) && U32.is_le(b, 244) == quatro : Bool}
  for ih: Sufixo(tail)
  for aceito: Aceita(tail, T.juntar(C.iniciar_utf8(ascii, dois, tres, quatro, b), acc), s)
  Inverte(Con{b, tail}, Livre{}, acc, s)
def iniciar_inverte(ascii, dois, tres, quatro, b, tail, acc, s, a, d, t, q, ih, aceito):
  match ascii dois tres quatro:
    case True{} _ _ _:
      caractere_inverte(b, [b], tail, acc, s, ih, K.ascii_recodifica(b, a), aceito)
    case False{} True{} _ _:
      prova = inicial2_inverte(b, tail, acc, s,
        K.prefixo2_reconstituido(b, F.e_booleano_esquerda(U32.is_ge(b, 194), U32.is_le(b, 223), d), F.e_booleano_direita(U32.is_ge(b, 194), U32.is_le(b, 223), d)), ih)
      prova(aceito)
    case False{} False{} True{} _:
      prova = inicial3_inverte(b, tail, acc, s,
        K.prefixo3_reconstituido(b, F.e_booleano_esquerda(U32.is_ge(b, 224), U32.is_le(b, 239), t), F.e_booleano_direita(U32.is_ge(b, 224), U32.is_le(b, 239), t)), ih)
      prova(aceito)
    case False{} False{} False{} True{}:
      prova = inicial4_inverte(b, tail, acc, s,
        K.prefixo4_reconstituido(b, F.e_booleano_esquerda(U32.is_ge(b, 240), U32.is_le(b, 244), q), F.e_booleano_direita(U32.is_ge(b, 240), U32.is_le(b, 244), q)), ih)
      prova(aceito)
    case False{} False{} False{} False{}:
      invalido_nao_aceita(Inverte(Con{b, tail}, Livre{}, acc, s), tail, s, aceito)

# Um unico passo de continuacao, para todos os estados parciais alcancaveis.
law continuacao_normal_inverte:
  for +p: Prefixo
  for +lo: Word(6n)
  for +tail: List<&2, U32>
  for +acc: String
  for +s: String
  for pendente: Pendente(p)
  for ih: Sufixo(tail)
  Passo(p, X.continuacao(lo), tail, acc, s)
def continuacao_normal_inverte(p, lo, tail, acc, s, pendente, ih):
  match p:
    case Livre{}:
      L.ex_falso(Passo(Livre{}, X.continuacao(lo), tail, acc, s), pendente)
    case Dois{hi}:
      match hi lo:
        case WCon{+hi0, WCon{+hi1, WCon{+hi2, WCon{+hi3, WCon{+hi4, WNil{}}}}}} WCon{+lo0, WCon{+lo1, WCon{+lo2, WCon{+lo3, WCon{+lo4, WCon{+lo5, WNil{}}}}}}}:
          %Equal.sym(C.Escalar, C.passo_utf8(unicode(Dois{hi}), X.continuacao(lo)), C.completar_utf8(0n, X.escalar2(hi, lo), 128), I.passo_continuacao(0n, inicio2(hi), 128, lo)) :
            Aceita(tail, T.juntar(_, acc), s) -> Inverte(Con{X.continuacao(lo), tail}, Dois{hi}, acc, s)
          aceito => conferido_inverte(U32.is_ge(X.escalar2(hi, lo), 128) && B.codigo_valido(X.escalar2(hi, lo)), X.escalar2(hi, lo), [I.prefixo2(hi), X.continuacao(lo)], tail, acc, s, ih,
            e => K.forma2_recodifica(hi, lo, F.e_booleano_esquerda(U32.is_ge(X.escalar2(hi, lo), 128), B.codigo_valido(X.escalar2(hi, lo)), e)), aceito)
    case Tres1{hi}:
      match hi lo:
        case WCon{+hi0, WCon{+hi1, WCon{+hi2, WCon{+hi3, WNil{}}}}} WCon{+lo0, WCon{+lo1, WCon{+lo2, WCon{+lo3, WCon{+lo4, WCon{+lo5, WNil{}}}}}}}:
          %Equal.sym(C.Escalar, C.passo_utf8(unicode(Tres1{hi}), X.continuacao(lo)), C.completar_utf8(1n, E.acumular(inicio3(hi), lo), 2048), I.passo_continuacao(1n, inicio3(hi), 2048, lo)) :
            Aceita(tail, T.juntar(_, acc), s) -> Inverte(Con{X.continuacao(lo), tail}, Tres1{hi}, acc, s)
          aceito => ih(Tres2{hi, lo}, acc, s, aceito)
    case Tres2{hi, b0}:
      match hi b0 lo:
        case WCon{+hi0, WCon{+hi1, WCon{+hi2, WCon{+hi3, WNil{}}}}} WCon{+b00, WCon{+b01, WCon{+b02, WCon{+b03, WCon{+b04, WCon{+b05, WNil{}}}}}}} WCon{+lo0, WCon{+lo1, WCon{+lo2, WCon{+lo3, WCon{+lo4, WCon{+lo5, WNil{}}}}}}}:
          %Equal.sym(C.Escalar, C.passo_utf8(unicode(Tres2{hi, b0}), X.continuacao(lo)), C.completar_utf8(0n, X.escalar3(hi, b0, lo), 2048), I.passo_continuacao(0n, E.acumular(inicio3(hi), b0), 2048, lo)) :
            Aceita(tail, T.juntar(_, acc), s) -> Inverte(Con{X.continuacao(lo), tail}, Tres2{hi, b0}, acc, s)
          aceito => conferido_inverte(U32.is_ge(X.escalar3(hi, b0, lo), 2048) && B.codigo_valido(X.escalar3(hi, b0, lo)), X.escalar3(hi, b0, lo), [I.prefixo3(hi), X.continuacao(b0), X.continuacao(lo)], tail, acc, s, ih,
            e => K.forma3_recodifica(hi, b0, lo, F.e_booleano_esquerda(U32.is_ge(X.escalar3(hi, b0, lo), 2048), B.codigo_valido(X.escalar3(hi, b0, lo)), e)), aceito)
    case Quatro1{hi}:
      match hi lo:
        case WCon{+hi0, WCon{+hi1, WCon{+hi2, WNil{}}}} WCon{+lo0, WCon{+lo1, WCon{+lo2, WCon{+lo3, WCon{+lo4, WCon{+lo5, WNil{}}}}}}}:
          %Equal.sym(C.Escalar, C.passo_utf8(unicode(Quatro1{hi}), X.continuacao(lo)), C.completar_utf8(2n, E.acumular(inicio4(hi), lo), 65536), I.passo_continuacao(2n, inicio4(hi), 65536, lo)) :
            Aceita(tail, T.juntar(_, acc), s) -> Inverte(Con{X.continuacao(lo), tail}, Quatro1{hi}, acc, s)
          aceito => ih(Quatro2{hi, lo}, acc, s, aceito)
    case Quatro2{hi, b0}:
      match hi b0 lo:
        case WCon{+hi0, WCon{+hi1, WCon{+hi2, WNil{}}}} WCon{+b00, WCon{+b01, WCon{+b02, WCon{+b03, WCon{+b04, WCon{+b05, WNil{}}}}}}} WCon{+lo0, WCon{+lo1, WCon{+lo2, WCon{+lo3, WCon{+lo4, WCon{+lo5, WNil{}}}}}}}:
          %Equal.sym(C.Escalar, C.passo_utf8(unicode(Quatro2{hi, b0}), X.continuacao(lo)), C.completar_utf8(1n, E.acumular(E.acumular(inicio4(hi), b0), lo), 65536), I.passo_continuacao(1n, E.acumular(inicio4(hi), b0), 65536, lo)) :
            Aceita(tail, T.juntar(_, acc), s) -> Inverte(Con{X.continuacao(lo), tail}, Quatro2{hi, b0}, acc, s)
          aceito => ih(Quatro3{hi, b0, lo}, acc, s, aceito)
    case Quatro3{hi, b0, b1}:
      match hi b0 b1 lo:
        case WCon{+hi0, WCon{+hi1, WCon{+hi2, WNil{}}}} WCon{+b00, WCon{+b01, WCon{+b02, WCon{+b03, WCon{+b04, WCon{+b05, WNil{}}}}}}} WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WNil{}}}}}}} WCon{+lo0, WCon{+lo1, WCon{+lo2, WCon{+lo3, WCon{+lo4, WCon{+lo5, WNil{}}}}}}}:
          %Equal.sym(C.Escalar, C.passo_utf8(unicode(Quatro3{hi, b0, b1}), X.continuacao(lo)), C.completar_utf8(0n, X.escalar4(hi, b0, b1, lo), 65536), I.passo_continuacao(0n, E.acumular(E.acumular(inicio4(hi), b0), b1), 65536, lo)) :
            Aceita(tail, T.juntar(_, acc), s) -> Inverte(Con{X.continuacao(lo), tail}, Quatro3{hi, b0, b1}, acc, s)
          aceito => conferido_inverte(U32.is_ge(X.escalar4(hi, b0, b1, lo), 65536) && B.codigo_valido(X.escalar4(hi, b0, b1, lo)), X.escalar4(hi, b0, b1, lo), [I.prefixo4(hi), X.continuacao(b0), X.continuacao(b1), X.continuacao(lo)], tail, acc, s, ih,
            e => K.forma4_recodifica(hi, b0, b1, lo, F.e_booleano_esquerda(U32.is_ge(X.escalar4(hi, b0, b1, lo), 65536), B.codigo_valido(X.escalar4(hi, b0, b1, lo)), e)), aceito)

law passo_pendente_rejeitado:
  for +p: Prefixo
  for +b: U32
  for pendente: Pendente(p)
  for e: {U32.is_ge(b, 128) && U32.is_le(b, 191) == False{} : Bool}
  {C.passo_utf8(unicode(p), b) == C.UTFInvalido{} : C.Escalar}
def passo_pendente_rejeitado(p, b, pendente, e):
  match p:
    case Livre{}:
      L.ex_falso({C.passo_utf8(C.Inicio{}, b) == C.UTFInvalido{} : C.Escalar}, pendente)
    case Dois{hi}:
      %Equal.sym(Bool, U32.is_ge(b, 128) && U32.is_le(b, 191), False{}, e) :
        {C.continuar_utf8(_, 0n, inicio2(hi), 128, b) == C.UTFInvalido{} : C.Escalar}
      {==}
    case Tres1{hi}:
      %Equal.sym(Bool, U32.is_ge(b, 128) && U32.is_le(b, 191), False{}, e) :
        {C.continuar_utf8(_, 1n, inicio3(hi), 2048, b) == C.UTFInvalido{} : C.Escalar}
      {==}
    case Tres2{hi, b0}:
      %Equal.sym(Bool, U32.is_ge(b, 128) && U32.is_le(b, 191), False{}, e) :
        {C.continuar_utf8(_, 0n, E.acumular(inicio3(hi), b0), 2048, b) == C.UTFInvalido{} : C.Escalar}
      {==}
    case Quatro1{hi}:
      %Equal.sym(Bool, U32.is_ge(b, 128) && U32.is_le(b, 191), False{}, e) :
        {C.continuar_utf8(_, 2n, inicio4(hi), 65536, b) == C.UTFInvalido{} : C.Escalar}
      {==}
    case Quatro2{hi, b0}:
      %Equal.sym(Bool, U32.is_ge(b, 128) && U32.is_le(b, 191), False{}, e) :
        {C.continuar_utf8(_, 1n, E.acumular(inicio4(hi), b0), 65536, b) == C.UTFInvalido{} : C.Escalar}
      {==}
    case Quatro3{hi, b0, b1}:
      %Equal.sym(Bool, U32.is_ge(b, 128) && U32.is_le(b, 191), False{}, e) :
        {C.continuar_utf8(_, 0n, E.acumular(E.acumular(inicio4(hi), b0), b1), 65536, b) == C.UTFInvalido{} : C.Escalar}
      {==}

law passo_pendente_casos:
  for ok: Bool
  for +p: Prefixo
  for +b: U32
  for +tail: List<&2, U32>
  for +acc: String
  for +s: String
  for pendente: Pendente(p)
  for +e: {U32.is_ge(b, 128) && U32.is_le(b, 191) == ok : Bool}
  for ih: Sufixo(tail)
  Passo(p, b, tail, acc, s)
def passo_pendente_casos(ok, p, b, tail, acc, s, pendente, e, ih):
  match ok:
    case False{}:
      %Equal.sym(C.Escalar, C.passo_utf8(unicode(p), b), C.UTFInvalido{}, passo_pendente_rejeitado(p, b, pendente, e)) :
        Aceita(tail, T.juntar(_, acc), s) -> Inverte(Con{b, tail}, p, acc, s)
      aceito => invalido_nao_aceita(Inverte(Con{b, tail}, p, acc, s), tail, s, aceito)
    case True{}:
      forma = K.continuacao_reconstituida(b,
        F.e_booleano_esquerda(U32.is_ge(b, 128), U32.is_le(b, 191), e),
        F.e_booleano_direita(U32.is_ge(b, 128), U32.is_le(b, 191), e))
      %Equal.sym(U32, b, X.continuacao(E.lo6(b)), forma) : Passo(p, _, tail, acc, s)
      continuacao_normal_inverte(p, E.lo6(b), tail, acc, s, pendente, ih)

law passo_inverte:
  for +p: Prefixo
  for +b: U32
  for +tail: List<&2, U32>
  for +acc: String
  for +s: String
  for ih: Sufixo(tail)
  Passo(p, b, tail, acc, s)
def passo_inverte(p, b, tail, acc, s, ih):
  match p:
    case Livre{}:
      aceito => iniciar_inverte(U32.is_lt(b, 128), U32.is_ge(b, 194) && U32.is_le(b, 223), U32.is_ge(b, 224) && U32.is_le(b, 239), U32.is_ge(b, 240) && U32.is_le(b, 244),
        b, tail, acc, s, {==}, {==}, {==}, {==}, ih, aceito)
    case Dois{hi}:
      passo_pendente_casos(U32.is_ge(b, 128) && U32.is_le(b, 191), p, b, tail, acc, s, Unit{}, {==}, ih)
    case Tres1{hi}:
      passo_pendente_casos(U32.is_ge(b, 128) && U32.is_le(b, 191), p, b, tail, acc, s, Unit{}, {==}, ih)
    case Tres2{hi, b0}:
      passo_pendente_casos(U32.is_ge(b, 128) && U32.is_le(b, 191), p, b, tail, acc, s, Unit{}, {==}, ih)
    case Quatro1{hi}:
      passo_pendente_casos(U32.is_ge(b, 128) && U32.is_le(b, 191), p, b, tail, acc, s, Unit{}, {==}, ih)
    case Quatro2{hi, b0}:
      passo_pendente_casos(U32.is_ge(b, 128) && U32.is_le(b, 191), p, b, tail, acc, s, Unit{}, {==}, ih)
    case Quatro3{hi, b0, b1}:
      passo_pendente_casos(U32.is_ge(b, 128) && U32.is_le(b, 191), p, b, tail, acc, s, Unit{}, {==}, ih)

# A hipotese indutiva aplica-se estritamente a tail; nao ha premissa de
# canonicalidade, testemunha de segmentacao, octetos_validos ou roundtrip.
law todos_os_sufixos_invertem:
  for +bs: List<&2, U32>
  Sufixo(bs)
def todos_os_sufixos_invertem(bs):
  match bs:
    case Nil{}:
      p => acc => s => aceito => fim_inverte(p, acc, s, aceito)
    case Con{+b, +tail}:
      ih = todos_os_sufixos_invertem(tail)
      p => acc => s => aceito =>
        prova = passo_inverte(p, b, tail, acc, s, ih)
        prova(aceito)

# Direcao inversa geral: para toda lista aceita, a recodificacao original
# devolve EXATAMENTE os mesmos U32, na mesma ordem e sem truncamento.
law utf8_entrada_aceita_recodifica_exatamente:
  for +bs: List<&2, U32>
  for +s: String
  for aceito: {T.finalizar_texto(T.percorrer_texto(bs, T.Lendo{C.Inicio{}, ""})) == Some{s} : Maybe<&2, String>}
  {B.utf8(s) == bs : List<&2, U32>}
def utf8_entrada_aceita_recodifica_exatamente(bs, s, aceito):
  prova = todos_os_sufixos_invertem(bs)
  prova(Livre{}, "", s, aceito)

law concatenar_vazio_direita:
  for +bs: List<&2, U32>
  {B.concatenar(bs, []) == bs : List<&2, U32>}
def concatenar_vazio_direita(bs):
  match bs:
    case Nil{}:
      {==}
    case Con{b, tail}:
      Equal.cong(List<&2, U32>, List<&2, U32>, r => Con{b, r}, B.concatenar(tail, []), tail, concatenar_vazio_direita(tail))

# Cobre em particular cada sequencia de 1, 2, 3 ou 4 bytes que emite um
# unico escalar. A lista e arbitraria; nem seu comprimento e presumido.
law utf8_sequencia_escalar_aceita_recodifica_exatamente:
  for +bs: List<&2, U32>
  for +cp: U32
  for aceito: {T.finalizar_texto(T.percorrer_texto(bs, T.Lendo{C.Inicio{}, ""})) == Some{SCon{Chr{cp}, ""}} : Maybe<&2, String>}
  {B.utf8_codigo(cp) == bs : List<&2, U32>}
def utf8_sequencia_escalar_aceita_recodifica_exatamente(bs, cp, aceito):
  Equal.trans(List<&2, U32>, B.utf8_codigo(cp), B.utf8(SCon{Chr{cp}, ""}), bs,
    Equal.sym(List<&2, U32>, B.concatenar(B.utf8_codigo(cp), []), B.utf8_codigo(cp), concatenar_vazio_direita(B.utf8_codigo(cp))),
    utf8_entrada_aceita_recodifica_exatamente(bs, SCon{Chr{cp}, ""}, aceito))
