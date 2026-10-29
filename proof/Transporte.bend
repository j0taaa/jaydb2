# O transporte privado preserva exatamente os dois blocos; nao e um log
# escolhido para satisfazer as leis e nao altera o protocolo publico.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ../src/Transporte.bend as T
import ./Fundamentos.bend as F
import ./CodecContadores.bend as Q
import ./CodecPalavrasBE64.bend as E
import ./CodecPalavrasWord.bend as W
import ./CodecInteiros.bend as I
import ./CodecPalavrasInversa.bend as J

law palavra_de_quatro_blocos:
  for +a: Word(8n)
  for +b: Word(8n)
  for +c: Word(8n)
  for +d: Word(8n)
  {T.palavra(E.octeto(a), E.octeto(b), E.octeto(c), E.octeto(d)) ==
    E.quatro(a, b, c, d) : U32}
def palavra_de_quatro_blocos(a, b, c, d):
  match a b c d:
    case WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WNil{}}}}}}}}} WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}} WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}} WCon{d0, WCon{d1, WCon{d2, WCon{d3, WCon{d4, WCon{d5, WCon{d6, WCon{d7, WNil{}}}}}}}}}:
      %Equal.sym(Word(32n), Word.mul(32n, E.bits(E.octeto(a)), E.bits(16777216)),
        W.zeros_baixos(24n, 8n, a), W.multiplicar_potencia_dois(24n, 8n, 32n, E.bits(E.octeto(a)))) :
        {U32{Word.add(32n, Word.add(32n, Word.add(32n, _, Word.mul(32n, E.bits(E.octeto(b)), E.bits(65536))), Word.mul(32n, E.bits(E.octeto(c)), E.bits(256))), E.bits(E.octeto(d)))} == E.quatro(a, b, c, d) : U32}
      %Equal.sym(Word(32n), Word.mul(32n, E.bits(E.octeto(b)), E.bits(65536)),
        W.zeros_baixos(16n, 16n, W.juntar(8n, 8n, b, Word.zero(8n))), W.multiplicar_potencia_dois(16n, 16n, 32n, E.bits(E.octeto(b)))) :
        {U32{Word.add(32n, Word.add(32n, Word.add(32n, W.zeros_baixos(24n, 8n, a), _), Word.mul(32n, E.bits(E.octeto(c)), E.bits(256))), E.bits(E.octeto(d)))} == E.quatro(a, b, c, d) : U32}
      %Equal.sym(Word(32n), Word.mul(32n, E.bits(E.octeto(c)), E.bits(256)),
        W.zeros_baixos(8n, 24n, W.juntar(8n, 16n, c, Word.zero(16n))), W.multiplicar_potencia_dois(8n, 24n, 32n, E.bits(E.octeto(c)))) :
        {U32{Word.add(32n, Word.add(32n, Word.add(32n, W.zeros_baixos(24n, 8n, a), W.zeros_baixos(16n, 16n, W.juntar(8n, 8n, b, Word.zero(8n)))), _), E.bits(E.octeto(d)))} == E.quatro(a, b, c, d) : U32}
      %Equal.sym(Word(32n), Word.add(32n, W.zeros_baixos(24n, 8n, a), W.juntar(24n, 8n, W.zeros_baixos(16n, 8n, b), Word.zero(8n))),
        W.juntar(24n, 8n, W.zeros_baixos(16n, 8n, b), a), W.soma_blocos_separados(24n, 8n, W.zeros_baixos(16n, 8n, b), a)) :
        {U32{Word.add(32n, Word.add(32n, _, W.zeros_baixos(8n, 24n, W.juntar(8n, 16n, c, Word.zero(16n)))), E.bits(E.octeto(d)))} == E.quatro(a, b, c, d) : U32}
      %Equal.sym(Word(32n), Word.add(32n, W.zeros_baixos(16n, 16n, W.juntar(8n, 8n, b, a)), W.juntar(16n, 16n, W.zeros_baixos(8n, 8n, c), Word.zero(16n))),
        W.juntar(16n, 16n, W.zeros_baixos(8n, 8n, c), W.juntar(8n, 8n, b, a)), W.soma_blocos_separados(16n, 16n, W.zeros_baixos(8n, 8n, c), W.juntar(8n, 8n, b, a))) :
        {U32{Word.add(32n, _, E.bits(E.octeto(d)))} == E.quatro(a, b, c, d) : U32}
      %Equal.sym(Word(32n), Word.add(32n, W.zeros_baixos(8n, 24n, W.juntar(8n, 16n, c, W.juntar(8n, 8n, b, a))), E.bits(E.octeto(d))),
        W.juntar(8n, 24n, d, W.juntar(8n, 16n, c, W.juntar(8n, 8n, b, a))), W.soma_blocos_separados(8n, 24n, d, W.juntar(8n, 16n, c, W.juntar(8n, 8n, b, a)))) :
        {U32{_} == E.quatro(a, b, c, d) : U32}
      {==}

law cabecalho_de_blocos:
  for +a: Word(8n)
  for +b: Word(8n)
  for +c: Word(8n)
  for +d: Word(8n)
  for +e: Word(8n)
  for +f: Word(8n)
  for +g: Word(8n)
  for +h: Word(8n)
  for +resto: List<&2, U32>
  {T.cabecalho(B.concatenar(B.be64(E.quatro(a, b, c, d), E.quatro(e, f, g, h)), resto)) ==
    T.cortar(resto, B.Numero64{E.quatro(a, b, c, d), E.quatro(e, f, g, h)}, Nil{}) : Maybe<&2, T.Partes>}
def cabecalho_de_blocos(a, b, c, d, e, f, g, h, resto):
  %Equal.sym(List<&2, U32>, B.be32(E.quatro(a, b, c, d)),
    [E.octeto(a), E.octeto(b), E.octeto(c), E.octeto(d)], E.be32_quatro(a, b, c, d)) :
    {T.cabecalho(B.concatenar(B.concatenar(_, B.be32(E.quatro(e, f, g, h))), resto)) ==
      T.cortar(resto, B.Numero64{E.quatro(a, b, c, d), E.quatro(e, f, g, h)}, Nil{}) : Maybe<&2, T.Partes>}
  %Equal.sym(List<&2, U32>, B.be32(E.quatro(e, f, g, h)),
    [E.octeto(e), E.octeto(f), E.octeto(g), E.octeto(h)], E.be32_quatro(e, f, g, h)) :
    {T.cabecalho(B.concatenar(B.concatenar([E.octeto(a), E.octeto(b), E.octeto(c), E.octeto(d)], _), resto)) ==
      T.cortar(resto, B.Numero64{E.quatro(a, b, c, d), E.quatro(e, f, g, h)}, Nil{}) : Maybe<&2, T.Partes>}
  %Equal.sym(U32, T.palavra(E.octeto(a), E.octeto(b), E.octeto(c), E.octeto(d)), E.quatro(a, b, c, d), palavra_de_quatro_blocos(a, b, c, d)) :
    {T.cortar(resto, B.Numero64{_, T.palavra(E.octeto(e), E.octeto(f), E.octeto(g), E.octeto(h))}, Nil{}) ==
      T.cortar(resto, B.Numero64{E.quatro(a, b, c, d), E.quatro(e, f, g, h)}, Nil{}) : Maybe<&2, T.Partes>}
  Equal.cong(U32, Maybe<&2, T.Partes>, lo => T.cortar(resto, B.Numero64{E.quatro(a, b, c, d), lo}, Nil{}),
    T.palavra(E.octeto(e), E.octeto(f), E.octeto(g), E.octeto(h)), E.quatro(e, f, g, h), palavra_de_quatro_blocos(e, f, g, h))

law cabecalho_inverte_be64:
  for +alto: U32
  for +baixo: U32
  for +resto: List<&2, U32>
  {T.cabecalho(B.concatenar(B.be64(alto, baixo), resto)) ==
    T.cortar(resto, B.Numero64{alto, baixo}, Nil{}) : Maybe<&2, T.Partes>}
def cabecalho_inverte_be64(alto, baixo, resto):
  match alto baixo:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      cabecalho_de_blocos(WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WNil{}}}}}}}}}, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WNil{}}}}}}}}}, WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WNil{}}}}}}}}}, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WNil{}}}}}}}}}, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WNil{}}}}}}}}}, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}, resto)

law concatenar_vazio:
  for +xs: List<&2, U32>
  {B.concatenar(xs, Nil{}) == xs : List<&2, U32>}
def concatenar_vazio(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => Con{h, ys}, B.concatenar(t, Nil{}), t, concatenar_vazio(t))

law inversao_acumulada:
  for xs: List<&2, U32>
  for +acc: List<&2, U32>
  for +ys: List<&2, U32>
  {T.inverter(T.inverter(xs, acc), ys) == T.inverter(acc, B.concatenar(xs, ys)) : List<&2, U32>}
def inversao_acumulada(xs, acc, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      inversao_acumulada(t, Con{h, acc}, ys)

law inverter_duas_vezes:
  for +xs: List<&2, U32>
  {T.inverter(T.inverter(xs, Nil{}), Nil{}) == xs : List<&2, U32>}
def inverter_duas_vezes(xs):
  Equal.trans(List<&2, U32>, T.inverter(T.inverter(xs, Nil{}), Nil{}), B.concatenar(xs, Nil{}), xs,
    inversao_acumulada(xs, Nil{}, Nil{}), concatenar_vazio(xs))

law cortar_zero:
  for segunda: List<&2, U32>
  for +acc: List<&2, U32>
  {T.cortar(segunda, B.Numero64{0, 0}, acc) ==
    Some{T.Partes{T.inverter(acc, Nil{}), segunda}} : Maybe<&2, T.Partes>}
def cortar_zero(segunda, acc):
  match segunda:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

law cortar_bloco_de_comprimento_medido:
  for +primeira: List<&2, U32>
  for +segunda: List<&2, U32>
  for +numero: B.Numero64
  for +acc: List<&2, U32>
  for +medido: {B.nat64(B.comprimento(primeira)) == Some{numero} : Maybe<&2, B.Numero64>}
  {T.cortar(B.concatenar(primeira, segunda), numero, acc) ==
    Some{T.Partes{T.inverter(T.inverter(primeira, acc), Nil{}), segunda}} : Maybe<&2, T.Partes>}
def cortar_bloco_de_comprimento_medido(primeira, segunda, numero, acc, medido):
  match primeira:
    case Nil{}:
      %F.algum_injetivo(B.Numero64, B.Numero64{0, 0}, numero, medido) :
        {T.cortar(segunda, _, acc) == Some{T.Partes{T.inverter(acc, Nil{}), segunda}} : Maybe<&2, T.Partes>}
      cortar_zero(segunda, acc)
    case Con{+h, +t}:
      %Equal.sym(Bool, C.zero64(numero), False{}, Q.nat64_sucessor_nunca_zero(B.comprimento(t), numero, medido)) :
        {T.desviar(_, unidade => Some{T.Partes{T.inverter(acc, Nil{}), Con{h, B.concatenar(t, segunda)}}},
          unidade => T.cortar(B.concatenar(t, segunda), C.diminuir64(numero), Con{h, acc})) ==
          Some{T.Partes{T.inverter(T.inverter(t, Con{h, acc}), Nil{}), segunda}} : Maybe<&2, T.Partes>}
      cortar_bloco_de_comprimento_medido(t, segunda, C.diminuir64(numero), Con{h, acc},
        Q.comprimento_da_cauda_e_decremento_do_corpo(h, t, numero, medido))

law cortar_preserva_exatamente_os_dois_blocos:
  for +primeira: List<&2, U32>
  for +segunda: List<&2, U32>
  for +numero: B.Numero64
  for medido: {B.nat64(B.comprimento(primeira)) == Some{numero} : Maybe<&2, B.Numero64>}
  {T.cortar(B.concatenar(primeira, segunda), numero, Nil{}) ==
    Some{T.Partes{primeira, segunda}} : Maybe<&2, T.Partes>}
def cortar_preserva_exatamente_os_dois_blocos(primeira, segunda, numero, medido):
  Equal.trans(Maybe<&2, T.Partes>, T.cortar(B.concatenar(primeira, segunda), numero, Nil{}),
    Some{T.Partes{T.inverter(T.inverter(primeira, Nil{}), Nil{}), segunda}}, Some{T.Partes{primeira, segunda}},
    cortar_bloco_de_comprimento_medido(primeira, segunda, numero, Nil{}, medido),
    Equal.cong(List<&2, U32>, Maybe<&2, T.Partes>, xs => Some{T.Partes{xs, segunda}},
      T.inverter(T.inverter(primeira, Nil{}), Nil{}), primeira, inverter_duas_vezes(primeira)))

law separar_be64_e_blocos_validos:
  for +primeira: List<&2, U32>
  for +segunda: List<&2, U32>
  for numero: B.Numero64
  for medido: {B.nat64(B.comprimento(primeira)) == Some{numero} : Maybe<&2, B.Numero64>}
  for vp: {B.octetos_validos(primeira) == True{} : Bool}
  for vs: {B.octetos_validos(segunda) == True{} : Bool}
  {T.separar(B.concatenar(F.extrair_ou(List<&2, U32>, B.numero64_bytes(Some{numero}), Nil{}), B.concatenar(primeira, segunda))) ==
    Some{T.Partes{primeira, segunda}} : Maybe<&2, T.Partes>}
def separar_be64_e_blocos_validos(primeira, segunda, numero, medido, vp, vs):
  match numero:
    case B.Numero64{+alto, +baixo}:
      %Equal.sym(Bool, B.octetos_validos(B.concatenar(B.be64(alto, baixo), B.concatenar(primeira, segunda))), True{},
        I.concatenar_preserva_octetos(B.be64(alto, baixo), B.concatenar(primeira, segunda),
          I.be64_so_emite_octetos(alto, baixo), I.concatenar_preserva_octetos(primeira, segunda, vp, vs))) :
        {T.validar(_, B.concatenar(B.be64(alto, baixo), B.concatenar(primeira, segunda))) == Some{T.Partes{primeira, segunda}} : Maybe<&2, T.Partes>}
      Equal.trans(Maybe<&2, T.Partes>, T.cabecalho(B.concatenar(B.be64(alto, baixo), B.concatenar(primeira, segunda))),
        T.cortar(B.concatenar(primeira, segunda), B.Numero64{alto, baixo}, Nil{}), Some{T.Partes{primeira, segunda}},
        cabecalho_inverte_be64(alto, baixo, B.concatenar(primeira, segunda)),
        cortar_preserva_exatamente_os_dois_blocos(primeira, segunda, B.Numero64{alto, baixo}, medido))

def separar_montagem_medida(medida: Maybe<&2, B.Numero64>,
  +primeira: List<&2, U32>, +segunda: List<&2, U32>, -bytes: List<&2, U32>,
  medido: {B.nat64(B.comprimento(primeira)) == medida : Maybe<&2, B.Numero64>},
  montagem: {T.juntar_com_cabecalho(B.numero64_bytes(medida), primeira, segunda) == Some{bytes} : Maybe<&2, List<&2, U32>>},
  vp: {B.octetos_validos(primeira) == True{} : Bool},
  vs: {B.octetos_validos(segunda) == True{} : Bool}) ->
  {T.separar(bytes) == Some{T.Partes{primeira, segunda}} : Maybe<&2, T.Partes>}:
  match medida:
    case None{}:
      L.ex_falso({T.separar(bytes) == Some{T.Partes{primeira, segunda}} : Maybe<&2, T.Partes>},
        F.nenhum_nao_algum(List<&2, U32>, bytes, montagem))
    case Some{B.Numero64{+alto, +baixo}}:
      %F.algum_injetivo(List<&2, U32>,
        B.concatenar(B.be64(alto, baixo), B.concatenar(primeira, segunda)), bytes, montagem) :
        {T.separar(_) == Some{T.Partes{primeira, segunda}} : Maybe<&2, T.Partes>}
      separar_be64_e_blocos_validos(primeira, segunda, B.Numero64{alto, baixo}, medido, vp, vs)

# As unicas hipoteses externas sao os octetos dos dois blocos. O comprimento
# representavel e o cabecalho exato sao extraidos do Some de juntar.
law separar_inverte_toda_montagem_valida:
  for +primeira: List<&2, U32>
  for +segunda: List<&2, U32>
  for -bytes: List<&2, U32>
  for montagem: {T.juntar(primeira, segunda) == Some{bytes} : Maybe<&2, List<&2, U32>>}
  for vp: {B.octetos_validos(primeira) == True{} : Bool}
  for vs: {B.octetos_validos(segunda) == True{} : Bool}
  {T.separar(bytes) == Some{T.Partes{primeira, segunda}} : Maybe<&2, T.Partes>}
def separar_inverte_toda_montagem_valida(primeira, segunda, bytes, montagem, vp, vs):
  separar_montagem_medida(B.nat64(B.comprimento(primeira)), primeira, segunda, bytes, {==}, montagem, vp, vs)

def primeira(p: T.Partes) -> List<&2, U32>:
  T.Partes{p1, p2} = p
  p1

def segunda(p: T.Partes) -> List<&2, U32>:
  T.Partes{p1, p2} = p
  p2

type Corte<-bytes: List<&2, U32>, -numero: B.Numero64,
  -acc: List<&2, U32>, -partes: T.Partes> is Type:
  Corte{prefixo: List<&2, U32>,
    fatoracao: {bytes == B.concatenar(prefixo, segunda(partes)) : List<&2, U32>},
    montagem: {primeira(partes) == T.inverter(acc, prefixo) : List<&2, U32>},
    quantidade: {B.nat64(B.comprimento(prefixo)) == Some{numero} : Maybe<&2, B.Numero64>}}

def corte_zero(+bytes: List<&2, U32>, +numero: B.Numero64,
  +acc: List<&2, U32>, zero: {C.zero64(numero) == True{} : Bool}) ->
  Corte<bytes, numero, acc, T.Partes{T.inverter(acc, Nil{}), bytes}>:
  Corte{Nil{}, {==}, {==},
    Equal.cong(B.Numero64, Maybe<&2, B.Numero64>, n => Some{n}, B.Numero64{0, 0}, numero,
      Equal.sym(B.Numero64, numero, B.Numero64{0, 0}, Q.zero64_so_reconhece_zero(numero, zero)))}

def prolongar_corte(+h: U32, -t: List<&2, U32>, +numero: B.Numero64,
  -acc: List<&2, U32>, -partes: T.Partes,
  nao_zero: {C.zero64(numero) == False{} : Bool},
  corte: Corte<t, C.diminuir64(numero), Con{h, acc}, partes>) ->
  Corte<Con{h, t}, numero, acc, partes>:
  match corte:
    case Corte{+prefixo, fatoracao, montagem, quantidade}:
      Corte{Con{h, prefixo},
        Equal.cong(List<&2, U32>, List<&2, U32>, xs => Con{h, xs}, t, B.concatenar(prefixo, segunda(partes)), fatoracao),
        montagem,
        Equal.trans(Maybe<&2, B.Numero64>, B.incrementar64(B.nat64(B.comprimento(prefixo))),
          B.incrementar64(Some{C.diminuir64(numero)}), Some{numero},
          Equal.cong(Maybe<&2, B.Numero64>, Maybe<&2, B.Numero64>, n => B.incrementar64(n),
            B.nat64(B.comprimento(prefixo)), Some{C.diminuir64(numero)}, quantidade),
          Q.incrementar_inverte_diminuir_quando_positivo(numero, nao_zero))}

def inverter_corte_vazio(zero: Bool, +numero: B.Numero64, +acc: List<&2, U32>,
  -partes: T.Partes, e: {C.zero64(numero) == zero : Bool},
  aceito: {T.vazio(zero, acc) == Some{partes} : Maybe<&2, T.Partes>}) ->
  Corte<Nil{}, numero, acc, partes>:
  match zero:
    case False{}:
      L.ex_falso(Corte<Nil{}, numero, acc, partes>, F.nenhum_nao_algum(T.Partes, partes, aceito))
    case True{}:
      %F.algum_injetivo(T.Partes, T.Partes{T.inverter(acc, Nil{}), Nil{}}, partes, aceito) :
        Corte<Nil{}, numero, acc, _>
      corte_zero(Nil{}, numero, acc, e)

def inverter_corte_desvio(zero: Bool, +h: U32, +t: List<&2, U32>,
  +numero: B.Numero64, +acc: List<&2, U32>, -partes: T.Partes,
  e: {C.zero64(numero) == zero : Bool},
  aceito: {T.desviar(zero,
    unidade => Some{T.Partes{T.inverter(acc, Nil{}), Con{h, t}}},
    unidade => T.cortar(t, C.diminuir64(numero), Con{h, acc})) == Some{partes} : Maybe<&2, T.Partes>},
  continuar: {T.cortar(t, C.diminuir64(numero), Con{h, acc}) == Some{partes} : Maybe<&2, T.Partes>} ->
    Corte<t, C.diminuir64(numero), Con{h, acc}, partes>) ->
  Corte<Con{h, t}, numero, acc, partes>:
  match zero:
    case False{}:
      prolongar_corte(h, t, numero, acc, partes, e, continuar(aceito))
    case True{}:
      %F.algum_injetivo(T.Partes, T.Partes{T.inverter(acc, Nil{}), Con{h, t}}, partes, aceito) :
        Corte<Con{h, t}, numero, acc, _>
      corte_zero(Con{h, t}, numero, acc, e)

# A aceitacao, sozinha, reconstroi o comprimento e o prefixo consumido.
# Nao se presume que o cabecalho recebido diga a verdade.
law cortar_aceito_tem_prefixo_e_contagem_exatos:
  for +bytes: List<&2, U32>
  for +numero: B.Numero64
  for +acc: List<&2, U32>
  for -partes: T.Partes
  for aceito: {T.cortar(bytes, numero, acc) == Some{partes} : Maybe<&2, T.Partes>}
  Corte<bytes, numero, acc, partes>
def cortar_aceito_tem_prefixo_e_contagem_exatos(bytes, numero, acc, partes, aceito):
  match bytes:
    case Nil{}:
      inverter_corte_vazio(C.zero64(numero), numero, acc, partes, {==}, aceito)
    case Con{+h, +t}:
      inverter_corte_desvio(C.zero64(numero), h, t, numero, acc, partes, {==}, aceito,
        prova => cortar_aceito_tem_prefixo_e_contagem_exatos(t, C.diminuir64(numero), Con{h, acc}, partes, prova))

law palavra_de_octetos_validos:
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +va: {U32.is_le(a, 255) == True{} : Bool}
  for +vb: {U32.is_le(b, 255) == True{} : Bool}
  for +vc: {U32.is_le(c, 255) == True{} : Bool}
  for +vd: {U32.is_le(d, 255) == True{} : Bool}
  {T.palavra(a, b, c, d) == J.montar(a, b, c, d) : U32}
def palavra_de_octetos_validos(a, b, c, d, va, vb, vc, vd):
  %Equal.sym(U32, a, E.octeto(J.byte_word(a)), J.octeto_valido_reconstituido(a, va)) :
    {T.palavra(_, b, c, d) == J.montar(a, b, c, d) : U32}
  %Equal.sym(U32, b, E.octeto(J.byte_word(b)), J.octeto_valido_reconstituido(b, vb)) :
    {T.palavra(E.octeto(J.byte_word(a)), _, c, d) == J.montar(a, b, c, d) : U32}
  %Equal.sym(U32, c, E.octeto(J.byte_word(c)), J.octeto_valido_reconstituido(c, vc)) :
    {T.palavra(E.octeto(J.byte_word(a)), E.octeto(J.byte_word(b)), _, d) == J.montar(a, b, c, d) : U32}
  %Equal.sym(U32, d, E.octeto(J.byte_word(d)), J.octeto_valido_reconstituido(d, vd)) :
    {T.palavra(E.octeto(J.byte_word(a)), E.octeto(J.byte_word(b)), E.octeto(J.byte_word(c)), _) == J.montar(a, b, c, d) : U32}
  palavra_de_quatro_blocos(J.byte_word(a), J.byte_word(b), J.byte_word(c), J.byte_word(d))

law cabecalho_valido_reconstroi_octetos:
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +e: U32
  for +f: U32
  for +g: U32
  for +h: U32
  for +va: {U32.is_le(a, 255) == True{} : Bool}
  for +vb: {U32.is_le(b, 255) == True{} : Bool}
  for +vc: {U32.is_le(c, 255) == True{} : Bool}
  for +vd: {U32.is_le(d, 255) == True{} : Bool}
  for +ve: {U32.is_le(e, 255) == True{} : Bool}
  for +vf: {U32.is_le(f, 255) == True{} : Bool}
  for +vg: {U32.is_le(g, 255) == True{} : Bool}
  for +vh: {U32.is_le(h, 255) == True{} : Bool}
  {B.be64(T.palavra(a, b, c, d), T.palavra(e, f, g, h)) == [a, b, c, d, e, f, g, h] : List<&2, U32>}
def cabecalho_valido_reconstroi_octetos(a, b, c, d, e, f, g, h, va, vb, vc, vd, ve, vf, vg, vh):
  %Equal.sym(U32, T.palavra(a, b, c, d), J.montar(a, b, c, d), palavra_de_octetos_validos(a, b, c, d, va, vb, vc, vd)) :
    {B.be64(_, T.palavra(e, f, g, h)) == [a, b, c, d, e, f, g, h] : List<&2, U32>}
  %Equal.sym(U32, T.palavra(e, f, g, h), J.montar(e, f, g, h), palavra_de_octetos_validos(e, f, g, h, ve, vf, vg, vh)) :
    {B.be64(J.montar(a, b, c, d), _) == [a, b, c, d, e, f, g, h] : List<&2, U32>}
  J.recodificar_octetos_separados(a, b, c, d, e, f, g, h, va, vb, vc, vd, ve, vf, vg, vh)

def combinar_octetos_de_cauda(-h: U32, -t: List<&2, U32>, -ys: List<&2, U32>,
  cabeca: {U32.is_le(h, 255) == True{} : Bool},
  par: L.E<{B.octetos_validos(t) == True{} : Bool}, {B.octetos_validos(ys) == True{} : Bool}>) ->
  L.E<{B.octetos_validos(Con{h, t}) == True{} : Bool}, {B.octetos_validos(ys) == True{} : Bool}>:
  match par:
    case L.Ambos{vt, vy}:
      L.Ambos{F.e_booleano_intro(U32.is_le(h, 255), B.octetos_validos(t), cabeca, vt), vy}

law separar_octetos_de_concatenacao:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +validos: {B.octetos_validos(B.concatenar(xs, ys)) == True{} : Bool}
  L.E<{B.octetos_validos(xs) == True{} : Bool}, {B.octetos_validos(ys) == True{} : Bool}>
def separar_octetos_de_concatenacao(xs, ys, validos):
  match xs:
    case Nil{}:
      L.Ambos{{==}, validos}
    case Con{+h, +t}:
      combinar_octetos_de_cauda(h, t, ys,
        F.e_booleano_esquerda(U32.is_le(h, 255), B.octetos_validos(B.concatenar(t, ys)), validos),
        separar_octetos_de_concatenacao(t, ys,
          F.e_booleano_direita(U32.is_le(h, 255), B.octetos_validos(B.concatenar(t, ys)), validos)))

def remontar_corte(+alto: U32, +baixo: U32, +resto: List<&2, U32>,
  -partes: T.Partes, corte: Corte<resto, B.Numero64{alto, baixo}, Nil{}, partes>) ->
  {T.juntar(primeira(partes), segunda(partes)) ==
    Some{B.concatenar(B.be64(alto, baixo), resto)} : Maybe<&2, List<&2, U32>>}:
  match corte:
    case Corte{+prefixo, fatoracao, montagem, quantidade}:
      %Equal.sym(List<&2, U32>, primeira(partes), prefixo, montagem) :
        {T.juntar(_, segunda(partes)) == Some{B.concatenar(B.be64(alto, baixo), resto)} : Maybe<&2, List<&2, U32>>}
      %Equal.sym(Maybe<&2, B.Numero64>, B.nat64(B.comprimento(prefixo)), Some{B.Numero64{alto, baixo}}, quantidade) :
        {T.juntar_com_cabecalho(B.numero64_bytes(_), prefixo, segunda(partes)) == Some{B.concatenar(B.be64(alto, baixo), resto)} : Maybe<&2, List<&2, U32>>}
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, xs => Some{B.concatenar(B.be64(alto, baixo), xs)},
        B.concatenar(prefixo, segunda(partes)), resto,
        Equal.sym(List<&2, U32>, resto, B.concatenar(prefixo, segunda(partes)), fatoracao))

def blocos_do_corte_sao_octetos(-resto: List<&2, U32>, -numero: B.Numero64,
  +partes: T.Partes, validos: {B.octetos_validos(resto) == True{} : Bool},
  corte: Corte<resto, numero, Nil{}, partes>) ->
  L.E<{B.octetos_validos(primeira(partes)) == True{} : Bool},
    {B.octetos_validos(segunda(partes)) == True{} : Bool}>:
  match corte:
    case Corte{+prefixo, fatoracao, montagem, quantidade}:
      %Equal.sym(List<&2, U32>, primeira(partes), prefixo, montagem) :
        L.E<{B.octetos_validos(_) == True{} : Bool}, {B.octetos_validos(segunda(partes)) == True{} : Bool}>
      separar_octetos_de_concatenacao(prefixo, segunda(partes),
        (%fatoracao : {B.octetos_validos(_) == True{} : Bool}
          validos))

def SeparacaoExata(-bytes: List<&2, U32>, -partes: T.Partes) -> Type:
  L.E<{T.juntar(primeira(partes), segunda(partes)) == Some{bytes} : Maybe<&2, List<&2, U32>>},
    L.E<{B.octetos_validos(primeira(partes)) == True{} : Bool},
      {B.octetos_validos(segunda(partes)) == True{} : Bool}>>

def concluir_corte_fiel(+alto: U32, +baixo: U32, +resto: List<&2, U32>,
  +partes: T.Partes, validos: {B.octetos_validos(resto) == True{} : Bool},
  corte: Corte<resto, B.Numero64{alto, baixo}, Nil{}, partes>) ->
  SeparacaoExata(B.concatenar(B.be64(alto, baixo), resto), partes):
  match corte:
    case Corte{+prefixo, +fatoracao, +montagem, +quantidade}:
      L.Ambos{remontar_corte(alto, baixo, resto, partes, Corte{prefixo, fatoracao, montagem, quantidade}),
        blocos_do_corte_sao_octetos(resto, B.Numero64{alto, baixo}, partes, validos, Corte{prefixo, fatoracao, montagem, quantidade})}

def cabecalho_aceito_reconstituido(
  +a: U32,
  +b: U32,
  +c: U32,
  +d: U32,
  +e: U32,
  +f: U32,
  +g: U32,
  +h: U32,
  +resto: List<&2, U32>, +partes: T.Partes,
  va: {U32.is_le(a, 255) == True{} : Bool},
  vb: {U32.is_le(b, 255) == True{} : Bool},
  vc: {U32.is_le(c, 255) == True{} : Bool},
  vd: {U32.is_le(d, 255) == True{} : Bool},
  ve: {U32.is_le(e, 255) == True{} : Bool},
  vf: {U32.is_le(f, 255) == True{} : Bool},
  vg: {U32.is_le(g, 255) == True{} : Bool},
  vh: {U32.is_le(h, 255) == True{} : Bool},
  vr: {B.octetos_validos(resto) == True{} : Bool},
  aceito: {T.cortar(resto, B.Numero64{T.palavra(a, b, c, d), T.palavra(e, f, g, h)}, Nil{}) == Some{partes} : Maybe<&2, T.Partes>}) ->
  SeparacaoExata(Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Con{h, resto}}}}}}}}, partes):
  %Equal.cong(List<&2, U32>, List<&2, U32>, xs => B.concatenar(xs, resto),
    B.be64(T.palavra(a, b, c, d), T.palavra(e, f, g, h)), [a, b, c, d, e, f, g, h],
    cabecalho_valido_reconstroi_octetos(a, b, c, d, e, f, g, h, va, vb, vc, vd, ve, vf, vg, vh)) :
    SeparacaoExata(_, partes)
  concluir_corte_fiel(T.palavra(a, b, c, d), T.palavra(e, f, g, h), resto, partes, vr,
    cortar_aceito_tem_prefixo_e_contagem_exatos(resto,
      B.Numero64{T.palavra(a, b, c, d), T.palavra(e, f, g, h)}, Nil{}, partes, aceito))

def inverter_cabecalho_aceito(+bytes: List<&2, U32>, +partes: T.Partes,
  +validos: {B.octetos_validos(bytes) == True{} : Bool},
  aceito: {T.cabecalho(bytes) == Some{partes} : Maybe<&2, T.Partes>}) ->
  SeparacaoExata(bytes, partes):
  match bytes:
    case Nil{}:
      L.ex_falso(SeparacaoExata(Nil{}, partes), F.nenhum_nao_algum(T.Partes, partes, aceito))
    case Con{a, Nil{}}:
      L.ex_falso(SeparacaoExata(Con{a, Nil{}}, partes), F.nenhum_nao_algum(T.Partes, partes, aceito))
    case Con{a, Con{b, Nil{}}}:
      L.ex_falso(SeparacaoExata(Con{a, Con{b, Nil{}}}, partes), F.nenhum_nao_algum(T.Partes, partes, aceito))
    case Con{a, Con{b, Con{c, Nil{}}}}:
      L.ex_falso(SeparacaoExata(Con{a, Con{b, Con{c, Nil{}}}}, partes), F.nenhum_nao_algum(T.Partes, partes, aceito))
    case Con{a, Con{b, Con{c, Con{d, Nil{}}}}}:
      L.ex_falso(SeparacaoExata(Con{a, Con{b, Con{c, Con{d, Nil{}}}}}, partes), F.nenhum_nao_algum(T.Partes, partes, aceito))
    case Con{a, Con{b, Con{c, Con{d, Con{e, Nil{}}}}}}:
      L.ex_falso(SeparacaoExata(Con{a, Con{b, Con{c, Con{d, Con{e, Nil{}}}}}}, partes), F.nenhum_nao_algum(T.Partes, partes, aceito))
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Nil{}}}}}}}:
      L.ex_falso(SeparacaoExata(Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Nil{}}}}}}}, partes), F.nenhum_nao_algum(T.Partes, partes, aceito))
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Nil{}}}}}}}}:
      L.ex_falso(SeparacaoExata(Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Nil{}}}}}}}}, partes), F.nenhum_nao_algum(T.Partes, partes, aceito))
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Con{h, resto}}}}}}}}:
      +va = F.e_booleano_esquerda(U32.is_le(a, 255), B.octetos_validos(Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Con{h, resto}}}}}}}), validos)
      +cauda1 = F.e_booleano_direita(U32.is_le(a, 255), B.octetos_validos(Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Con{h, resto}}}}}}}), validos)
      +vb = F.e_booleano_esquerda(U32.is_le(b, 255), B.octetos_validos(Con{c, Con{d, Con{e, Con{f, Con{g, Con{h, resto}}}}}}), cauda1)
      +cauda2 = F.e_booleano_direita(U32.is_le(b, 255), B.octetos_validos(Con{c, Con{d, Con{e, Con{f, Con{g, Con{h, resto}}}}}}), cauda1)
      +vc = F.e_booleano_esquerda(U32.is_le(c, 255), B.octetos_validos(Con{d, Con{e, Con{f, Con{g, Con{h, resto}}}}}), cauda2)
      +cauda3 = F.e_booleano_direita(U32.is_le(c, 255), B.octetos_validos(Con{d, Con{e, Con{f, Con{g, Con{h, resto}}}}}), cauda2)
      +vd = F.e_booleano_esquerda(U32.is_le(d, 255), B.octetos_validos(Con{e, Con{f, Con{g, Con{h, resto}}}}), cauda3)
      +cauda4 = F.e_booleano_direita(U32.is_le(d, 255), B.octetos_validos(Con{e, Con{f, Con{g, Con{h, resto}}}}), cauda3)
      +ve = F.e_booleano_esquerda(U32.is_le(e, 255), B.octetos_validos(Con{f, Con{g, Con{h, resto}}}), cauda4)
      +cauda5 = F.e_booleano_direita(U32.is_le(e, 255), B.octetos_validos(Con{f, Con{g, Con{h, resto}}}), cauda4)
      +vf = F.e_booleano_esquerda(U32.is_le(f, 255), B.octetos_validos(Con{g, Con{h, resto}}), cauda5)
      +cauda6 = F.e_booleano_direita(U32.is_le(f, 255), B.octetos_validos(Con{g, Con{h, resto}}), cauda5)
      +vg = F.e_booleano_esquerda(U32.is_le(g, 255), B.octetos_validos(Con{h, resto}), cauda6)
      +cauda7 = F.e_booleano_direita(U32.is_le(g, 255), B.octetos_validos(Con{h, resto}), cauda6)
      +vh = F.e_booleano_esquerda(U32.is_le(h, 255), B.octetos_validos(resto), cauda7)
      +cauda8 = F.e_booleano_direita(U32.is_le(h, 255), B.octetos_validos(resto), cauda7)
      cabecalho_aceito_reconstituido(a, b, c, d, e, f, g, h, resto, partes,
        va, vb, vc, vd, ve, vf, vg, vh, cauda8, aceito)

def inverter_validacao_aceita(ok: Bool, +bytes: List<&2, U32>, +partes: T.Partes,
  validos: {B.octetos_validos(bytes) == ok : Bool},
  aceito: {T.validar(ok, bytes) == Some{partes} : Maybe<&2, T.Partes>}) ->
  SeparacaoExata(bytes, partes):
  match ok:
    case False{}:
      L.ex_falso(SeparacaoExata(bytes, partes), F.nenhum_nao_algum(T.Partes, partes, aceito))
    case True{}:
      inverter_cabecalho_aceito(bytes, partes, validos, aceito)

law toda_separacao_aceita_reconstroi_pacote_original:
  for +bytes: List<&2, U32>
  for +partes: T.Partes
  for aceito: {T.separar(bytes) == Some{partes} : Maybe<&2, T.Partes>}
  SeparacaoExata(bytes, partes)
def toda_separacao_aceita_reconstroi_pacote_original(bytes, partes, aceito):
  inverter_validacao_aceita(B.octetos_validos(bytes), bytes, partes, {==}, aceito)

