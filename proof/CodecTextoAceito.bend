# Soundness do estado textual contado, inclusive reconstrucao da contagem
# ORIGINAL a partir de uma aceitacao, sem pressupor nat64(comprimento).
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecContadores.bend as N
import ./CodecConteudo.bend as G
import ./CodecUTF8.bend as U
import ./CodecUTF8InversaTexto.bend as I
import ./CodecPercurso.bend as R
import ./CodecTextos.bend as T
import ./CodecPalavrasInversa.bend as W
import ../contrato/Protocolo.bend as P
import ./CodecPalavrasBE64.bend as H
import ./Codec.bend as V

def fim_sem_ultimo(e: C.Escalar, q: B.Numero64, invertido: String) ->
  {C.finalizar(C.guardar_escalar(e, False{}, False{}, q, invertido, C.Raiz{})) == C.Entrada{} : C.Resultado}:
  match e:
    case C.UTFInvalido{}:
      {==}
    case C.Caractere{cp}:
      {==}
    case C.Parcial{u}:
      {==}

def unico_octeto_confere_ultimo(ultimo: Bool, +e: C.Escalar, +q: B.Numero64,
  +invertido: String, -v: D.Valor,
  aceito: {C.finalizar(C.guardar_escalar(e, ultimo, False{}, q, invertido, C.Raiz{})) == C.Decodificado{v} : C.Resultado}) ->
  {ultimo == True{} : Bool}:
  match ultimo:
    case True{}:
      {==}
    case False{}:
      L.ex_falso({False{} == True{} : Bool}, R.entrada_nao_decodificada(v,
        Equal.trans(C.Resultado, C.Entrada{}, C.finalizar(C.guardar_escalar(e, False{}, False{}, q, invertido, C.Raiz{})), C.Decodificado{v},
          Equal.sym(C.Resultado, C.finalizar(C.guardar_escalar(e, False{}, False{}, q, invertido, C.Raiz{})), C.Entrada{}, fim_sem_ultimo(e, q, invertido)), aceito)))

law ultimo_escalar_recusa_qualquer_sufixo:
  for e: C.Escalar
  for +b: U32
  for +bs: List<&2, U32>
  for +q: B.Numero64
  for +invertido: String
  for +corpo: B.Numero64
  for +teto: B.Numero64
  {C.percorrer(Con{b, bs}, corpo, teto, C.guardar_escalar(e, True{}, False{}, q, invertido, C.Raiz{})) == C.Entrada{} : C.Resultado}
def ultimo_escalar_recusa_qualquer_sufixo(e, b, bs, q, invertido, corpo, teto):
  match e:
    case C.UTFInvalido{}:
      R.invalido_absorve_todo_sufixo(Con{b, bs}, corpo, teto)
    case C.Caractere{cp}:
      R.pronto_recusa_qualquer_octeto_extra(b, bs, corpo, teto, D.VTexto{String.reverse(SCon{Chr{cp}, invertido})})
    case C.Parcial{u}:
      R.invalido_absorve_todo_sufixo(Con{b, bs}, corpo, teto)

def continuar_contagem_escalar(+e: C.Escalar, +bs: List<&2, U32>, +q: B.Numero64,
  +invertido: String, +corpo: B.Numero64, +teto: B.Numero64, -v: D.Valor,
  aceito: {C.percorrer(bs, corpo, teto, C.guardar_escalar(e, False{}, False{}, C.diminuir64(q), invertido, C.Raiz{})) == C.Decodificado{v} : C.Resultado},
  continuar: @u: C.Unicode -> @texto: String ->
    {C.percorrer(bs, corpo, teto, C.Conteudo{False{}, C.um64(C.diminuir64(q)), C.diminuir64(C.diminuir64(q)), u, texto, C.Raiz{}}) == C.Decodificado{v} : C.Resultado} ->
    {N.ultimos(B.comprimento(bs), C.diminuir64(q)) == True{} : Bool}) ->
  {N.ultimos(B.comprimento(bs), C.diminuir64(q)) == True{} : Bool}:
  match e:
    case C.UTFInvalido{}:
      L.ex_falso({N.ultimos(B.comprimento(bs), C.diminuir64(q)) == True{} : Bool}, R.entrada_nao_decodificada(v,
        Equal.trans(C.Resultado, C.Entrada{}, C.percorrer(bs, corpo, teto, C.Invalido{}), C.Decodificado{v},
          Equal.sym(C.Resultado, C.percorrer(bs, corpo, teto, C.Invalido{}), C.Entrada{}, R.invalido_absorve_todo_sufixo(bs, corpo, teto)), aceito)))
    case C.Caractere{cp}:
      continuar(C.Inicio{}, SCon{Chr{cp}, invertido}, aceito)
    case C.Parcial{u}:
      continuar(u, invertido, aceito)

def conferir_contagem_restante(ultimo: Bool, +e: C.Escalar, +b: U32, +bs: List<&2, U32>, +q: B.Numero64,
  +invertido: String, +corpo: B.Numero64, +teto: B.Numero64, -v: D.Valor,
  aceito: {C.percorrer(Con{b, bs}, corpo, teto, C.guardar_escalar(e, ultimo, False{}, C.diminuir64(q), invertido, C.Raiz{})) == C.Decodificado{v} : C.Resultado},
  continuar: @u: C.Unicode -> @texto: String ->
    {C.percorrer(Con{b, bs}, corpo, teto, C.Conteudo{False{}, C.um64(C.diminuir64(q)), C.diminuir64(C.diminuir64(q)), u, texto, C.Raiz{}}) == C.Decodificado{v} : C.Resultado} ->
    {N.ultimos(B.comprimento(Con{b, bs}), C.diminuir64(q)) == True{} : Bool}) ->
  {Bool.not(ultimo) && N.ultimos(B.comprimento(Con{b, bs}), C.diminuir64(q)) == True{} : Bool}:
  match ultimo:
    case False{}:
      continuar_contagem_escalar(e, Con{b, bs}, q, invertido, corpo, teto, v, aceito, continuar)
    case True{}:
      L.ex_falso({False{} == True{} : Bool}, R.entrada_nao_decodificada(v,
        Equal.trans(C.Resultado, C.Entrada{}, C.percorrer(Con{b, bs}, corpo, teto, C.guardar_escalar(e, True{}, False{}, C.diminuir64(q), invertido, C.Raiz{})), C.Decodificado{v},
          Equal.sym(C.Resultado, C.percorrer(Con{b, bs}, corpo, teto, C.guardar_escalar(e, True{}, False{}, C.diminuir64(q), invertido, C.Raiz{})), C.Entrada{},
            ultimo_escalar_recusa_qualquer_sufixo(e, b, bs, C.diminuir64(q), invertido, corpo, teto)), aceito)))

law conteudo_aceito_conferiu_todos_os_ultimos:
  for +bs: List<&2, U32>
  for +q: B.Numero64
  for +u: C.Unicode
  for +invertido: String
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for -v: D.Valor
  for aceito: {C.percorrer(bs, corpo, teto, C.Conteudo{False{}, C.um64(q), C.diminuir64(q), u, invertido, C.Raiz{}}) == C.Decodificado{v} : C.Resultado}
  {N.ultimos(B.comprimento(bs), q) == True{} : Bool}
def conteudo_aceito_conferiu_todos_os_ultimos(bs, q, u, invertido, corpo, teto, v, aceito):
  match bs:
    case Nil{}:
      L.ex_falso({False{} == True{} : Bool}, R.entrada_nao_decodificada(v, aceito))
    case Con{+b, Nil{}}:
      unico_octeto_confere_ultimo(C.um64(q), C.passo_utf8(u, b), C.diminuir64(q), invertido, v, aceito)
    case Con{+b, Con{+x, +resto}}:
      conferir_contagem_restante(C.um64(q), C.passo_utf8(u, b), x, resto, q, invertido, C.diminuir64(corpo), C.diminuir64(teto), v, aceito,
        proximo => texto => e => conteudo_aceito_conferiu_todos_os_ultimos(Con{x, resto}, C.diminuir64(q), proximo, texto, C.diminuir64(corpo), C.diminuir64(teto), v, e))

law conteudo_aceito_reconstroi_contagem_original:
  for +bs: List<&2, U32>
  for +q: B.Numero64
  for +u: C.Unicode
  for +invertido: String
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for -v: D.Valor
  for aceito: {C.percorrer(bs, corpo, teto, C.Conteudo{False{}, C.um64(q), C.diminuir64(q), u, invertido, C.Raiz{}}) == C.Decodificado{v} : C.Resultado}
  {B.nat64(B.comprimento(bs)) == Some{q} : Maybe<&2, B.Numero64>}
def conteudo_aceito_reconstroi_contagem_original(bs, q, u, invertido, corpo, teto, v, aceito):
  N.ultimos_aceitos_reconstroem_a_contagem_original(B.comprimento(bs), q,
    conteudo_aceito_conferiu_todos_os_ultimos(bs, q, u, invertido, corpo, teto, v, aceito))

def conteudo_aceito_tem_bytes(+bs: List<&2, U32>, -q: B.Numero64, -u: C.Unicode, -invertido: String,
  -corpo: B.Numero64, -teto: B.Numero64, -v: D.Valor,
  aceito: {C.percorrer(bs, corpo, teto, C.Conteudo{False{}, C.um64(q), C.diminuir64(q), u, invertido, C.Raiz{}}) == C.Decodificado{v} : C.Resultado}) -> G.NaoVazio(bs):
  match bs:
    case Nil{}:
      R.entrada_nao_decodificada(v, aceito)
    case Con{b, t}:
      Unit{}

type TextoConcluido<-t: U.Texto, -v: D.Valor> is Type:
  TextoConcluido{texto: String,
    valor: {v == D.VTexto{texto} : D.Valor},
    transducao: {U.finalizar_texto(t) == Some{texto} : Maybe<&2, String>}}

def valor_resultado(r: C.Resultado) -> D.Valor:
  match r:
    case C.Decodificado{v}:
      v
    case _:
      D.VAusente{}

def texto_finalizado_aceito(t: U.Texto, -v: D.Valor,
  aceito: {C.finalizar(G.concluir_texto(False{}, C.Raiz{}, t)) == C.Decodificado{v} : C.Resultado}) -> TextoConcluido<t, v>:
  match t:
    case U.TextoInvalido{}:
      L.ex_falso(TextoConcluido<U.TextoInvalido{}, v>, R.entrada_nao_decodificada(v, aceito))
    case U.Lendo{C.Inicio{}, +invertido}:
      TextoConcluido{String.reverse(invertido),
        Equal.sym(D.Valor, D.VTexto{String.reverse(invertido)}, v, Equal.cong(C.Resultado, D.Valor, r => valor_resultado(r), C.Decodificado{D.VTexto{String.reverse(invertido)}}, C.Decodificado{v}, aceito)), {==}}
    case U.Lendo{C.Continua{n, cp, minimo}, invertido}:
      L.ex_falso(TextoConcluido<U.Lendo{C.Continua{n, cp, minimo}, invertido}, v>, R.entrada_nao_decodificada(v, aceito))

type ConteudoDecodificado<-bs: List<&2, U32>, -q: B.Numero64, -v: D.Valor> is Type:
  ConteudoDecodificado{texto: String,
    medida: {B.nat64(B.comprimento(bs)) == Some{q} : Maybe<&2, B.Numero64>},
    valor: {v == D.VTexto{texto} : D.Valor},
    bytes: {B.utf8(texto) == bs : List<&2, U32>}}

def recodificar_texto_concluido(+bs: List<&2, U32>, -q: B.Numero64, -v: D.Valor,
  medida: {B.nat64(B.comprimento(bs)) == Some{q} : Maybe<&2, B.Numero64>},
  texto: TextoConcluido<U.percorrer_texto(bs, U.Lendo{C.Inicio{}, ""}), v>) -> ConteudoDecodificado<bs, q, v>:
  match texto:
    case TextoConcluido{+s, valor, transducao}:
      ConteudoDecodificado{s, medida, valor, I.utf8_entrada_aceita_recodifica_exatamente(bs, s, transducao)}

law conteudo_textual_aceito_reconstroi_exatamente_os_bytes:
  for +bs: List<&2, U32>
  for +q: B.Numero64
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for -v: D.Valor
  for +aceito: {C.percorrer(bs, corpo, teto, C.Conteudo{False{}, C.um64(q), C.diminuir64(q), C.Inicio{}, "", C.Raiz{}}) == C.Decodificado{v} : C.Resultado}
  ConteudoDecodificado<bs, q, v>
def conteudo_textual_aceito_reconstroi_exatamente_os_bytes(bs, q, corpo, teto, v, aceito):
  +medida = conteudo_aceito_reconstroi_contagem_original(bs, q, C.Inicio{}, "", corpo, teto, v, aceito)
  +maquina = G.conteudo_contado_consume_exatamente_o_texto(bs, q, corpo, teto, False{}, C.Inicio{}, "", C.Raiz{},
    conteudo_aceito_tem_bytes(bs, q, C.Inicio{}, "", corpo, teto, v, aceito), medida)
  resultado = {(%R.percurso_e_execucao_integral(bs, R.Quadro{corpo, teto, C.Conteudo{False{}, C.um64(q), C.diminuir64(q), C.Inicio{}, "", C.Raiz{}}}) :
    {_ == C.Decodificado{v} : C.Resultado}
    aceito) : {C.finalizar(G.processar_conteudo(bs, q, corpo, teto, False{}, C.Inicio{}, "", C.Raiz{})) == C.Decodificado{v} : C.Resultado}}
  recodificar_texto_concluido(bs, q, v, medida,
    texto_finalizado_aceito(U.percorrer_texto(bs, U.Lendo{C.Inicio{}, ""}), v,
      (%maquina : {C.finalizar(_) == C.Decodificado{v} : C.Resultado}
        resultado)))

# Grande/Curto nao podem ser escondidos por bytes posteriores.
def conferencia_textual_aceita(c: C.Conferencia, +bs: List<&2, U32>, +q: B.Numero64,
  +corpo: B.Numero64, +teto: B.Numero64, -v: D.Valor,
  aceito: {C.percorrer(bs, corpo, teto, C.abrir_conferido(c, C.Texto{}, q, C.Raiz{})) == C.Decodificado{v} : C.Resultado}) ->
  {C.percorrer(bs, corpo, teto, C.abrir_variavel(C.zero64(q), C.Texto{}, q, C.Raiz{})) == C.Decodificado{v} : C.Resultado}:
  match c:
    case C.Cabe{}:
      aceito
    case C.Curto{}:
      L.ex_falso({C.percorrer(bs, corpo, teto, C.abrir_variavel(C.zero64(q), C.Texto{}, q, C.Raiz{})) == C.Decodificado{v} : C.Resultado}, R.entrada_nao_decodificada(v,
        Equal.trans(C.Resultado, C.Entrada{}, C.percorrer(bs, corpo, teto, C.Invalido{}), C.Decodificado{v}, Equal.sym(C.Resultado, C.percorrer(bs, corpo, teto, C.Invalido{}), C.Entrada{}, R.invalido_absorve_todo_sufixo(bs, corpo, teto)), aceito)))
    case C.Grande{}:
      L.ex_falso({C.percorrer(bs, corpo, teto, C.abrir_variavel(C.zero64(q), C.Texto{}, q, C.Raiz{})) == C.Decodificado{v} : C.Resultado}, R.limite_nao_decodificado(v,
        Equal.trans(C.Resultado, C.Limite{}, C.percorrer(bs, corpo, teto, C.Acima{}), C.Decodificado{v}, Equal.sym(C.Resultado, C.percorrer(bs, corpo, teto, C.Acima{}), C.Limite{}, R.acima_absorve_todo_sufixo(bs, corpo, teto)), aceito)))

def texto_aberto_aceito(zero: Bool, +bs: List<&2, U32>, +q: B.Numero64,
  +corpo: B.Numero64, +teto: B.Numero64, -v: D.Valor,
  ezero: {C.zero64(q) == zero : Bool},
  aceito: {C.percorrer(bs, corpo, teto, C.abrir_variavel(zero, C.Texto{}, q, C.Raiz{})) == C.Decodificado{v} : C.Resultado}) -> ConteudoDecodificado<bs, q, v>:
  match zero bs:
    case False{} _:
      conteudo_textual_aceito_reconstroi_exatamente_os_bytes(bs, q, corpo, teto, v, aceito)
    case True{} Nil{}:
      ConteudoDecodificado{"",
        Equal.cong(B.Numero64, Maybe<&2, B.Numero64>, n => Some{n}, B.Numero64{0, 0}, q, Equal.sym(B.Numero64, q, B.Numero64{0, 0}, N.zero64_so_reconhece_zero(q, ezero))),
        Equal.sym(D.Valor, D.VTexto{""}, v, Equal.cong(C.Resultado, D.Valor, r => valor_resultado(r), C.Decodificado{D.VTexto{""}}, C.Decodificado{v}, aceito)), {==}}
    case True{} Con{+b, +t}:
      L.ex_falso(ConteudoDecodificado<Con{b, t}, q, v>, R.entrada_nao_decodificada(v,
        Equal.trans(C.Resultado, C.Entrada{}, C.percorrer(Con{b, t}, corpo, teto, C.Pronto{D.VTexto{""}}), C.Decodificado{v},
          Equal.sym(C.Resultado, C.percorrer(Con{b, t}, corpo, teto, C.Pronto{D.VTexto{""}}), C.Entrada{}, R.pronto_recusa_qualquer_octeto_extra(b, t, corpo, teto, D.VTexto{""})), aceito)))

law concluir_palavra_textual_aceita_reconstroi_conteudo:
  for +bs: List<&2, U32>
  for +alto: U32
  for +baixo: U32
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for -v: D.Valor
  for aceito: {C.percorrer(bs, corpo, teto, C.concluir_palavra(C.Texto{}, alto, baixo, C.Raiz{}, corpo, teto)) == C.Decodificado{v} : C.Resultado}
  ConteudoDecodificado<bs, B.Numero64{alto, baixo}, v>
def concluir_palavra_textual_aceita_reconstroi_conteudo(bs, alto, baixo, corpo, teto, v, aceito):
  +q = {B.Numero64{alto, baixo} : B.Numero64}
  texto_aberto_aceito(C.zero64(q), bs, q, corpo, teto, v, {==},
    conferencia_textual_aceita(C.conferir(C.somar_opcionais(C.minimo_campo(C.Texto{}, q), C.minimo_pilha(C.Raiz{})), corpo, teto), bs, q, corpo, teto, v, aceito))

law octetos_validos_do_prefixo:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +validos: {B.octetos_validos(B.concatenar(xs, ys)) == True{} : Bool}
  {B.octetos_validos(xs) == True{} : Bool}
def octetos_validos_do_prefixo(xs, ys, validos):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      F.e_booleano_intro(U32.is_le(h, 255), B.octetos_validos(t),
        F.e_booleano_esquerda(U32.is_le(h, 255), B.octetos_validos(B.concatenar(t, ys)), validos),
        octetos_validos_do_prefixo(t, ys, F.e_booleano_direita(U32.is_le(h, 255), B.octetos_validos(B.concatenar(t, ys)), validos)))

# Canonicalidade completa depois de reconstituir o cabeçalho e o conteúdo.
def recodificar_texto_com_cabecalho(+a: U32, +b: U32, +c: U32, +d: U32,
  +e: U32, +f: U32, +g: U32, +h: U32, +bs: List<&2, U32>, -v: D.Valor,
  valido: {D.valor_valido(v) == True{} : Bool},
  cabecalho: {B.octetos_validos([a, b, c, d, e, f, g, h]) == True{} : Bool},
  dados: ConteudoDecodificado<bs, B.Numero64{W.montar(a, b, c, d), W.montar(e, f, g, h)}, v>) ->
  P.Codificacao(v, Con{4, B.concatenar([a, b, c, d, e, f, g, h], bs)}):
  match dados:
    case ConteudoDecodificado{+s, medida, +valor, +bytes}:
      unicode = {(%valor : {D.valor_valido(_) == True{} : Bool}
        valido) : {D.unicode_valido(s) == True{} : Bool}}
      texto_valido = Equal.trans(Bool, B.texto_valido(s), D.unicode_valido(s), True{}, T.predicados_de_texto_concordam(s), unicode)
      medida_texto = {(%Equal.sym(List<&2, U32>, B.utf8(s), bs, bytes) :
        {B.nat64(B.comprimento(_)) == Some{B.Numero64{W.montar(a, b, c, d), W.montar(e, f, g, h)}} : Maybe<&2, B.Numero64>}
        medida) : {B.nat64(B.comprimento(B.utf8(s))) == Some{B.Numero64{W.montar(a, b, c, d), W.montar(e, f, g, h)}} : Maybe<&2, B.Numero64>}}
      %Equal.sym(D.Valor, v, D.VTexto{s}, valor) : P.Codificacao(_, Con{4, B.concatenar([a, b, c, d, e, f, g, h], bs)})
      %W.be64_recodifica_oito_octetos_validos(a, b, c, d, e, f, g, h, cabecalho) :
        {P.codificar(D.VTexto{s}) == Some{Con{4, B.concatenar(_, bs)}} : Maybe<&2, List<&2, U32>>}
      %bytes : {P.codificar(D.VTexto{s}) == Some{Con{4, B.concatenar(B.be64(W.montar(a, b, c, d), W.montar(e, f, g, h)), _)}} : Maybe<&2, List<&2, U32>>}
      T.codificar_texto_medido_e_exato(s, W.montar(a, b, c, d), W.montar(e, f, g, h), texto_valido, medida_texto)

def analisar_cabecalho_textual(+a: U32, +b: U32, +c: U32, +d: U32,
  +e: U32, +f: U32, +g: U32, +h: U32, +bs: List<&2, U32>,
  +corpo: B.Numero64, +teto: B.Numero64, -v: D.Valor,
  cabecalho: {B.octetos_validos([a, b, c, d, e, f, g, h]) == True{} : Bool},
  aceito: {C.percorrer(B.concatenar([a, b, c, d, e, f, g, h], bs), corpo, teto, C.Palavra{C.Texto{}, 7n, 0, 0, C.Raiz{}}) == C.Decodificado{v} : C.Resultado}) ->
  ConteudoDecodificado<bs, B.Numero64{W.montar(a, b, c, d), W.montar(e, f, g, h)}, v>:
  concluir_palavra_textual_aceita_reconstroi_conteudo(bs, W.montar(a, b, c, d), W.montar(e, f, g, h), H.diminuir(8n, corpo), H.diminuir(8n, teto), v,
    (%W.oito_octetos_validos_concluem_palavra(C.Texto{}, a, b, c, d, e, f, g, h, C.Raiz{}, corpo, teto, cabecalho) :
      {R.percorrer_quadro(bs, _) == C.Decodificado{v} : C.Resultado}
      %R.percurso_de_concatenacao([a, b, c, d, e, f, g, h], bs, R.Quadro{corpo, teto, C.Palavra{C.Texto{}, 7n, 0, 0, C.Raiz{}}}) :
        {_ == C.Decodificado{v} : C.Resultado}
      aceito))

def texto_aceito_cabecalho(+a: U32, +b: U32, +c: U32, +d: U32,
  +e: U32, +f: U32, +g: U32, +h: U32, +bs: List<&2, U32>,
  +teto: B.Numero64, -v: D.Valor,
  valido: {D.valor_valido(v) == True{} : Bool},
  entrada: R.EntradaConferida<B.nat64(B.comprimento(Con{4, B.concatenar([a, b, c, d, e, f, g, h], bs)})), Con{4, B.concatenar([a, b, c, d, e, f, g, h], bs)}, teto, v>) ->
  P.Codificacao(v, Con{4, B.concatenar([a, b, c, d, e, f, g, h], bs)}):
  match entrada:
    case R.Conferida{+corpo, medida, cabe, octetos, percurso}:
      +cabecalho = octetos_validos_do_prefixo([a, b, c, d, e, f, g, h], bs,
        F.e_booleano_direita(True{}, B.octetos_validos(B.concatenar([a, b, c, d, e, f, g, h], bs)), octetos))
      recodificar_texto_com_cabecalho(a, b, c, d, e, f, g, h, bs, v, valido, cabecalho,
        analisar_cabecalho_textual(a, b, c, d, e, f, g, h, bs, C.diminuir64(corpo), C.diminuir64(teto), v, cabecalho, percurso))

# Ao contrario do inteiro, o texto pode ter bytes APOS a palavra de tamanho.
def PalavraSuficiente(n: Nat, bs: List<&2, U32>) -> Type:
  match n bs:
    case 0n Nil{}:
      Empty
    case 0n Con{b, t}:
      Unit
    case 1n+p Nil{}:
      Empty
    case 1n+p Con{b, t}:
      PalavraSuficiente(p, t)

law palavra_aceita_exige_todos_os_octetos_do_cabecalho:
  for n: Nat
  for +bs: List<&2, U32>
  for +alto: U32
  for +baixo: U32
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for -v: D.Valor
  for aceito: {C.percorrer(bs, corpo, teto, C.Palavra{C.Texto{}, n, alto, baixo, C.Raiz{}}) == C.Decodificado{v} : C.Resultado}
  PalavraSuficiente(n, bs)
def palavra_aceita_exige_todos_os_octetos_do_cabecalho(n, bs, alto, baixo, corpo, teto, v, aceito):
  match n bs:
    case 0n Nil{}:
      R.entrada_nao_decodificada(v, aceito)
    case 0n Con{b, t}:
      Unit{}
    case 1n+p Nil{}:
      R.entrada_nao_decodificada(v, aceito)
    case 1n+p Con{+b, +t}:
      palavra_aceita_exige_todos_os_octetos_do_cabecalho(p, t, (alto * 256 + U32.shrn(baixo, 24n) : U32), (baixo * 256 + b : U32), C.diminuir64(corpo), C.diminuir64(teto), v, aceito)

def texto_aceito_com_formato(+bs: List<&2, U32>, +teto: B.Numero64, -v: D.Valor,
  valido: {D.valor_valido(v) == True{} : Bool},
  aceito: {C.decodificar(Con{4, bs}, teto) == C.Decodificado{v} : C.Resultado},
  formato: PalavraSuficiente(7n, bs)) -> P.Codificacao(v, Con{4, bs}):
  match bs:
    case Nil{}:
      L.ex_falso(P.Codificacao(v, Con{4, Nil{}}), formato)
    case Con{a0, Nil{}}:
      L.ex_falso(P.Codificacao(v, Con{4, Con{a0, Nil{}}}), formato)
    case Con{a0, Con{a1, Nil{}}}:
      L.ex_falso(P.Codificacao(v, Con{4, Con{a0, Con{a1, Nil{}}}}), formato)
    case Con{a0, Con{a1, Con{a2, Nil{}}}}:
      L.ex_falso(P.Codificacao(v, Con{4, Con{a0, Con{a1, Con{a2, Nil{}}}}}), formato)
    case Con{a0, Con{a1, Con{a2, Con{a3, Nil{}}}}}:
      L.ex_falso(P.Codificacao(v, Con{4, Con{a0, Con{a1, Con{a2, Con{a3, Nil{}}}}}}), formato)
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Nil{}}}}}}:
      L.ex_falso(P.Codificacao(v, Con{4, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Nil{}}}}}}}), formato)
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Nil{}}}}}}}:
      L.ex_falso(P.Codificacao(v, Con{4, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Nil{}}}}}}}}), formato)
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Nil{}}}}}}}}:
      L.ex_falso(P.Codificacao(v, Con{4, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Nil{}}}}}}}}}), formato)
    case Con{+a0, Con{+a1, Con{+a2, Con{+a3, Con{+a4, Con{+a5, Con{+a6, Con{+a7, +resto}}}}}}}}:
      texto_aceito_cabecalho(a0, a1, a2, a3, a4, a5, a6, a7, resto, teto, v, valido,
        R.aceitacao_exige_corpo_representavel_octetos_e_limite(Con{4, B.concatenar([a0, a1, a2, a3, a4, a5, a6, a7], resto)}, teto, v, aceito))

def cabecalho_textual_aceito_e_completo(+bs: List<&2, U32>, +teto: B.Numero64, -v: D.Valor,
  entrada: R.EntradaConferida<B.nat64(B.comprimento(Con{4, bs})), Con{4, bs}, teto, v>) -> PalavraSuficiente(7n, bs):
  match entrada:
    case R.Conferida{corpo, medida, cabe, octetos, percurso}:
      palavra_aceita_exige_todos_os_octetos_do_cabecalho(7n, bs, 0, 0, C.diminuir64(corpo), C.diminuir64(teto), v, percurso)

law toda_aceitacao_iniciada_por_tag_texto_e_canonica:
  for +bs: List<&2, U32>
  for +teto: B.Numero64
  for -v: D.Valor
  for +aceito: {C.decodificar(Con{4, bs}, teto) == C.Decodificado{v} : C.Resultado}
  P.Codificacao(v, Con{4, bs})
def toda_aceitacao_iniciada_por_tag_texto_e_canonica(bs, teto, v, aceito):
  texto_aceito_com_formato(bs, teto, v, V.decodificar_so_devolve_valor_valido(Con{4, bs}, teto, v, aceito), aceito,
    cabecalho_textual_aceito_e_completo(bs, teto, v,
      R.aceitacao_exige_corpo_representavel_octetos_e_limite(Con{4, bs}, teto, v, aceito)))
