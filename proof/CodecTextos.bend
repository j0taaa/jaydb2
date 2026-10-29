# Composicao textual geral: transducao -> Conteudo real -> API publica.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecUTF8.bend as U
import ./CodecUTF8Inversa.bend as V
import ./CodecConteudo.bend as G
import ./CodecContadores.bend as N
import ./CodecMinimos.bend as M
import ./CodecPalavrasBE64.bend as H
import ./CodecPercurso.bend as R
import ./CodecInteiros.bend as J
import ./CodecUTF8InversaOctetos.bend as O
import ./CodecUnicode.bend as Q
import ./CodecCanonico.bend as K
import ../contrato/Protocolo.bend as P

def concluir_transducao_aceita(+nome: Bool, +pilha: C.Pilha,
  +t: U.Texto, -s: String,
  aceito: {U.finalizar_texto(t) == Some{s} : Maybe<&2, String>}) ->
  {G.concluir_texto(nome, pilha, t) == C.emitir_texto(nome, s, pilha) : C.Maquina}:
  match t:
    case U.TextoInvalido{}:
      L.ex_falso({C.Invalido{} == C.emitir_texto(nome, s, pilha) : C.Maquina}, F.nenhum_nao_algum(String, s, aceito))
    case U.Lendo{C.Inicio{}, +invertido}:
      Equal.cong(String, C.Maquina, texto => C.emitir_texto(nome, texto, pilha), String.reverse(invertido), s,
        F.algum_injetivo(String, String.reverse(invertido), s, aceito))
    case U.Lendo{C.Continua{n, cp, minimo}, invertido}:
      L.ex_falso({C.Invalido{} == C.emitir_texto(nome, s, pilha) : C.Maquina}, F.nenhum_nao_algum(String, s, aceito))

law abertura_textual_contada_reproduz_transducao_aceita:
  for +bs: List<&2, U32>
  for +q: B.Numero64
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for -s: String
  for +medido: {B.nat64(B.comprimento(bs)) == Some{q} : Maybe<&2, B.Numero64>}
  for aceito: {U.finalizar_texto(U.percorrer_texto(bs, U.Lendo{C.Inicio{}, ""})) == Some{s} : Maybe<&2, String>}
  {R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.abrir_variavel(C.zero64(q), C.Texto{}, q, C.Raiz{})})) == C.Pronto{D.VTexto{s}} : C.Maquina}
def abertura_textual_contada_reproduz_transducao_aceita(bs, q, corpo, teto, s, medido, aceito):
  match bs:
    case Nil{}:
      %F.algum_injetivo(B.Numero64, B.Numero64{0, 0}, q, medido) :
        {R.maquina(R.executar(Nil{}, R.Quadro{corpo, teto, C.abrir_variavel(C.zero64(_), C.Texto{}, q, C.Raiz{})})) == C.Pronto{D.VTexto{s}} : C.Maquina}
      Equal.cong(String, C.Maquina, texto => C.Pronto{D.VTexto{texto}}, "", s, F.algum_injetivo(String, "", s, aceito))
    case Con{+b, +t}:
      %Equal.sym(Bool, C.zero64(q), False{}, N.zero64_reflete_contagem_natural(B.comprimento(Con{b, t}), q, medido)) :
        {R.maquina(R.executar(Con{b, t}, R.Quadro{corpo, teto, C.abrir_variavel(_, C.Texto{}, q, C.Raiz{})})) == C.Pronto{D.VTexto{s}} : C.Maquina}
      Equal.trans(C.Maquina,
        G.processar_conteudo(Con{b, t}, q, corpo, teto, False{}, C.Inicio{}, "", C.Raiz{}),
        G.concluir_texto(False{}, C.Raiz{}, U.percorrer_texto(Con{b, t}, U.Lendo{C.Inicio{}, ""})), C.Pronto{D.VTexto{s}},
        G.conteudo_contado_consume_exatamente_o_texto(Con{b, t}, q, corpo, teto, False{}, C.Inicio{}, "", C.Raiz{}, Unit{}, medido),
        concluir_transducao_aceita(False{}, C.Raiz{}, U.percorrer_texto(Con{b, t}, U.Lendo{C.Inicio{}, ""}), s, aceito))

law texto_canonico_contado_e_reproduzido_exatamente:
  for +s: String
  for +q: B.Numero64
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for valido: {B.texto_valido(s) == True{} : Bool}
  for +medido: {B.nat64(B.comprimento(B.utf8(s))) == Some{q} : Maybe<&2, B.Numero64>}
  {R.maquina(R.executar(B.utf8(s), R.Quadro{corpo, teto, C.abrir_variavel(C.zero64(q), C.Texto{}, q, C.Raiz{})})) == C.Pronto{D.VTexto{s}} : C.Maquina}
def texto_canonico_contado_e_reproduzido_exatamente(s, q, corpo, teto, valido, medido):
  abertura_textual_contada_reproduz_transducao_aceita(B.utf8(s), q, corpo, teto, s, medido, V.utf8_texto_valido_decodifica_exatamente(s, valido))

law diminuir_comuta_com_iteracao:
  for +n: Nat
  for +q: B.Numero64
  {H.diminuir(n, C.diminuir64(q)) == C.diminuir64(H.diminuir(n, q)) : B.Numero64}
def diminuir_comuta_com_iteracao(n, q):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(B.Numero64, B.Numero64, x => C.diminuir64(x), H.diminuir(p, C.diminuir64(q)), C.diminuir64(H.diminuir(p, q)), diminuir_comuta_com_iteracao(p, q))

law remover_prefixo_da_medida:
  for +n: Nat
  for +resto: Nat
  for +corpo: B.Numero64
  for medido: {B.nat64(Nat.add(n, resto)) == Some{corpo} : Maybe<&2, B.Numero64>}
  {B.nat64(resto) == Some{H.diminuir(n, corpo)} : Maybe<&2, B.Numero64>}
def remover_prefixo_da_medida(n, resto, corpo, medido):
  match n:
    case 0n:
      medido
    case 1n+p:
      %diminuir_comuta_com_iteracao(p, corpo) :
        {B.nat64(resto) == Some{_} : Maybe<&2, B.Numero64>}
      remover_prefixo_da_medida(p, resto, C.diminuir64(corpo),
        N.medida_decrementada(Nat.add(p, resto), corpo, N.nat64_sucessor_tem_antecessor_exato(Nat.add(p, resto), corpo, medido)))

law concluir_texto_na_raiz_confere_o_minimo_exato:
  for +alto: U32
  for +baixo: U32
  for +teto: B.Numero64
  for cabe: {C.menor_igual64(B.Numero64{alto, baixo}, teto) == True{} : Bool}
  {C.concluir_palavra(C.Texto{}, alto, baixo, C.Raiz{}, B.Numero64{alto, baixo}, teto) ==
    C.abrir_variavel(C.zero64(B.Numero64{alto, baixo}), C.Texto{}, B.Numero64{alto, baixo}, C.Raiz{}) : C.Maquina}
def concluir_texto_na_raiz_confere_o_minimo_exato(alto, baixo, teto, cabe):
  %Equal.sym(Maybe<&2, B.Numero64>, C.somar_opcionais(C.minimo_campo(C.Texto{}, B.Numero64{alto, baixo}), C.minimo_pilha(C.Raiz{})), Some{B.Numero64{alto, baixo}},
    M.minimo_textual_na_raiz_e_exatamente_a_contagem(B.Numero64{alto, baixo})) :
    {C.abrir_conferido(C.conferir(_, B.Numero64{alto, baixo}, teto), C.Texto{}, B.Numero64{alto, baixo}, C.Raiz{}) == C.abrir_variavel(C.zero64(B.Numero64{alto, baixo}), C.Texto{}, B.Numero64{alto, baixo}, C.Raiz{}) : C.Maquina}
  %Equal.sym(C.Conferencia, C.conferir(Some{B.Numero64{alto, baixo}}, B.Numero64{alto, baixo}, teto), C.Cabe{},
    M.conferir_minimo_igual_ao_corpo_permite_limite(B.Numero64{alto, baixo}, teto, cabe)) :
    {C.abrir_conferido(_, C.Texto{}, B.Numero64{alto, baixo}, C.Raiz{}) == C.abrir_variavel(C.zero64(B.Numero64{alto, baixo}), C.Texto{}, B.Numero64{alto, baixo}, C.Raiz{}) : C.Maquina}
  {==}

def bytes_texto(alto: U32, baixo: U32, s: String) -> List<&2, U32>:
  Con{4, B.concatenar(B.be64(alto, baixo), B.utf8(s))}

law cabecalho_textual_canonico_abre_exatamente_o_conteudo:
  for +s: String
  for +alto: U32
  for +baixo: U32
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for medida_texto: {B.nat64(B.comprimento(B.utf8(s))) == Some{B.Numero64{alto, baixo}} : Maybe<&2, B.Numero64>}
  for medida_corpo: {B.nat64(B.comprimento(bytes_texto(alto, baixo, s))) == Some{corpo} : Maybe<&2, B.Numero64>}
  for cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {R.executar(Con{4, B.be64(alto, baixo)}, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}}) ==
    R.Quadro{H.diminuir(9n, corpo), H.diminuir(9n, teto), C.abrir_variavel(C.zero64(B.Numero64{alto, baixo}), C.Texto{}, B.Numero64{alto, baixo}, C.Raiz{})} : R.Quadro}
def cabecalho_textual_canonico_abre_exatamente_o_conteudo(s, alto, baixo, corpo, teto, medida_texto, medida_corpo, cabe):
  medida_resto = remover_prefixo_da_medida(9n, B.comprimento(B.utf8(s)), corpo, medida_corpo)
  +resto_igual = F.algum_injetivo(B.Numero64, H.diminuir(9n, corpo), B.Numero64{alto, baixo},
    Equal.trans(Maybe<&2, B.Numero64>, Some{H.diminuir(9n, corpo)}, B.nat64(B.comprimento(B.utf8(s))), Some{B.Numero64{alto, baixo}},
      Equal.sym(Maybe<&2, B.Numero64>, B.nat64(B.comprimento(B.utf8(s))), Some{H.diminuir(9n, corpo)}, medida_resto), medida_texto))
  cabe_resto = {(%resto_igual : {C.menor_igual64(_, H.diminuir(9n, teto)) == True{} : Bool}
    M.diminuir_repetido_preserva_ordem_dos_limites(9n, corpo, teto, cabe)) : {C.menor_igual64(B.Numero64{alto, baixo}, H.diminuir(9n, teto)) == True{} : Bool}}
  concluir = {(%Equal.sym(B.Numero64, H.diminuir(9n, corpo), B.Numero64{alto, baixo}, resto_igual) :
    {C.concluir_palavra(C.Texto{}, alto, baixo, C.Raiz{}, _, H.diminuir(9n, teto)) ==
      C.abrir_variavel(C.zero64(B.Numero64{alto, baixo}), C.Texto{}, B.Numero64{alto, baixo}, C.Raiz{}) : C.Maquina}
    concluir_texto_na_raiz_confere_o_minimo_exato(alto, baixo, H.diminuir(9n, teto), cabe_resto)) :
    {C.concluir_palavra(C.Texto{}, alto, baixo, C.Raiz{}, H.diminuir(9n, corpo), H.diminuir(9n, teto)) == C.abrir_variavel(C.zero64(B.Numero64{alto, baixo}), C.Texto{}, B.Numero64{alto, baixo}, C.Raiz{}) : C.Maquina}}
  Equal.trans(R.Quadro,
    R.executar(Con{4, B.be64(alto, baixo)}, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}}),
    R.Quadro{H.diminuir(9n, corpo), H.diminuir(9n, teto), C.concluir_palavra(C.Texto{}, alto, baixo, C.Raiz{}, H.diminuir(9n, corpo), H.diminuir(9n, teto))},
    R.Quadro{H.diminuir(9n, corpo), H.diminuir(9n, teto), C.abrir_variavel(C.zero64(B.Numero64{alto, baixo}), C.Texto{}, B.Numero64{alto, baixo}, C.Raiz{})},
    H.be64_conclui_palavra(C.Texto{}, alto, baixo, C.Raiz{}, C.diminuir64(corpo), C.diminuir64(teto)),
    Equal.cong(C.Maquina, R.Quadro, m => R.Quadro{H.diminuir(9n, corpo), H.diminuir(9n, teto), m},
      C.concluir_palavra(C.Texto{}, alto, baixo, C.Raiz{}, H.diminuir(9n, corpo), H.diminuir(9n, teto)),
      C.abrir_variavel(C.zero64(B.Numero64{alto, baixo}), C.Texto{}, B.Numero64{alto, baixo}, C.Raiz{}), concluir))

law executar_texto_canonico_dentro_do_limite_e_exato:
  for +s: String
  for +alto: U32
  for +baixo: U32
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for valido: {B.texto_valido(s) == True{} : Bool}
  for +medida_texto: {B.nat64(B.comprimento(B.utf8(s))) == Some{B.Numero64{alto, baixo}} : Maybe<&2, B.Numero64>}
  for medida_corpo: {B.nat64(B.comprimento(bytes_texto(alto, baixo, s))) == Some{corpo} : Maybe<&2, B.Numero64>}
  for cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {R.maquina(R.executar(bytes_texto(alto, baixo, s), R.Quadro{corpo, teto, C.Tag{C.Raiz{}}})) == C.Pronto{D.VTexto{s}} : C.Maquina}
def executar_texto_canonico_dentro_do_limite_e_exato(s, alto, baixo, corpo, teto, valido, medida_texto, medida_corpo, cabe):
  cabecalho = cabecalho_textual_canonico_abre_exatamente_o_conteudo(s, alto, baixo, corpo, teto, medida_texto, medida_corpo, cabe)
  Equal.trans(C.Maquina,
    R.maquina(R.executar(bytes_texto(alto, baixo, s), R.Quadro{corpo, teto, C.Tag{C.Raiz{}}})),
    R.maquina(R.executar(B.utf8(s), R.executar(Con{4, B.be64(alto, baixo)}, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}}))),
    C.Pronto{D.VTexto{s}},
    Equal.cong(R.Quadro, C.Maquina, q => R.maquina(q),
      R.executar(bytes_texto(alto, baixo, s), R.Quadro{corpo, teto, C.Tag{C.Raiz{}}}),
      R.executar(B.utf8(s), R.executar(Con{4, B.be64(alto, baixo)}, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}})),
      R.execucao_de_concatenacao(Con{4, B.be64(alto, baixo)}, B.utf8(s), R.Quadro{corpo, teto, C.Tag{C.Raiz{}}})),
    Equal.trans(C.Maquina,
      R.maquina(R.executar(B.utf8(s), R.executar(Con{4, B.be64(alto, baixo)}, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}}))),
      R.maquina(R.executar(B.utf8(s), R.Quadro{H.diminuir(9n, corpo), H.diminuir(9n, teto), C.abrir_variavel(C.zero64(B.Numero64{alto, baixo}), C.Texto{}, B.Numero64{alto, baixo}, C.Raiz{})})),
      C.Pronto{D.VTexto{s}},
      Equal.cong(R.Quadro, C.Maquina, q => R.maquina(R.executar(B.utf8(s), q)),
        R.executar(Con{4, B.be64(alto, baixo)}, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}}),
        R.Quadro{H.diminuir(9n, corpo), H.diminuir(9n, teto), C.abrir_variavel(C.zero64(B.Numero64{alto, baixo}), C.Texto{}, B.Numero64{alto, baixo}, C.Raiz{})}, cabecalho),
      texto_canonico_contado_e_reproduzido_exatamente(s, B.Numero64{alto, baixo}, H.diminuir(9n, corpo), H.diminuir(9n, teto), valido, medida_texto)))

law todo_texto_canonico_dentro_do_limite_e_aceito:
  for +s: String
  for +alto: U32
  for +baixo: U32
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +valido: {B.texto_valido(s) == True{} : Bool}
  for +medida_texto: {B.nat64(B.comprimento(B.utf8(s))) == Some{B.Numero64{alto, baixo}} : Maybe<&2, B.Numero64>}
  for +medida_corpo: {B.nat64(B.comprimento(bytes_texto(alto, baixo, s))) == Some{corpo} : Maybe<&2, B.Numero64>}
  for +cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {C.decodificar(bytes_texto(alto, baixo, s), teto) == C.Decodificado{D.VTexto{s}} : C.Resultado}
def todo_texto_canonico_dentro_do_limite_e_aceito(s, alto, baixo, corpo, teto, valido, medida_texto, medida_corpo, cabe):
  octetos = J.concatenar_preserva_octetos(B.be64(alto, baixo), B.utf8(s), J.be64_so_emite_octetos(alto, baixo), O.utf8_texto_valido_emite_octetos(s, valido))
  %Equal.sym(Maybe<&2, B.Numero64>, B.nat64(B.comprimento(bytes_texto(alto, baixo, s))), Some{corpo}, medida_corpo) :
    {C.decodificar_medida(_, bytes_texto(alto, baixo, s), teto) == C.Decodificado{D.VTexto{s}} : C.Resultado}
  %Equal.sym(Bool, C.menor_igual64(corpo, teto), True{}, cabe) :
    {C.decodificar_tamanho(_, bytes_texto(alto, baixo, s), corpo, teto) == C.Decodificado{D.VTexto{s}} : C.Resultado}
  %Equal.sym(Bool, B.octetos_validos(bytes_texto(alto, baixo, s)), True{}, octetos) :
    {C.decodificar_octetos(_, bytes_texto(alto, baixo, s), corpo, teto) == C.Decodificado{D.VTexto{s}} : C.Resultado}
  Equal.trans(C.Resultado, C.percorrer(bytes_texto(alto, baixo, s), corpo, teto, C.Tag{C.Raiz{}}),
    R.finalizar_quadro(R.executar(bytes_texto(alto, baixo, s), R.Quadro{corpo, teto, C.Tag{C.Raiz{}}})), C.Decodificado{D.VTexto{s}},
    R.percurso_e_execucao_integral(bytes_texto(alto, baixo, s), R.Quadro{corpo, teto, C.Tag{C.Raiz{}}}),
    Equal.cong(C.Maquina, C.Resultado, m => C.finalizar(m), R.maquina(R.executar(bytes_texto(alto, baixo, s), R.Quadro{corpo, teto, C.Tag{C.Raiz{}}})), C.Pronto{D.VTexto{s}},
      executar_texto_canonico_dentro_do_limite_e_exato(s, alto, baixo, corpo, teto, valido, medida_texto, medida_corpo, cabe)))

law predicados_de_texto_concordam:
  for +s: String
  {B.texto_valido(s) == D.unicode_valido(s) : Bool}
def predicados_de_texto_concordam(s):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+cp}, +t}:
      %Equal.sym(Bool, B.codigo_valido(cp), D.escalar_valido(cp), Q.predicados_unicode_concordam(cp)) :
        {_ && B.texto_valido(t) == D.escalar_valido(cp) && D.unicode_valido(t) : Bool}
      Equal.cong(Bool, Bool, b => D.escalar_valido(cp) && b, B.texto_valido(t), D.unicode_valido(t), predicados_de_texto_concordam(t))

law finalizar_atomo_opcional_preserva_resultado:
  for m: Maybe<&2, List<&2, U32>>
  {P.finalizar(P.atomo_opcional(m)) == m : Maybe<&2, List<&2, U32>>}
def finalizar_atomo_opcional_preserva_resultado(m):
  match m:
    case None{}:
      {==}
    case Some{bs}:
      {==}

law codificacao_exige_valor_valido:
  for valido: Bool
  for -resultado: Maybe<&2, List<&2, U32>>
  for -bs: List<&2, U32>
  for aceito: {P.codificar_casos(valido, resultado) == Some{bs} : Maybe<&2, List<&2, U32>>}
  {valido == True{} : Bool}
def codificacao_exige_valor_valido(valido, resultado, bs, aceito):
  match valido:
    case False{}:
      L.ex_falso({False{} == True{} : Bool}, F.nenhum_nao_algum(List<&2, U32>, bs, aceito))
    case True{}:
      {==}

type TextoCodificado<-s: String, -bs: List<&2, U32>> is Type:
  TextoCodificado{alto: U32, baixo: U32,
    valido: {B.texto_valido(s) == True{} : Bool},
    medida: {B.nat64(B.comprimento(B.utf8(s))) == Some{B.Numero64{alto, baixo}} : Maybe<&2, B.Numero64>},
    bytes: {bytes_texto(alto, baixo, s) == bs : List<&2, U32>}}

def tamanho_textual_codificado(n: Maybe<&2, B.Numero64>, +s: String, -bs: List<&2, U32>,
  valido: {B.texto_valido(s) == True{} : Bool},
  medida: {B.nat64(B.comprimento(B.utf8(s))) == n : Maybe<&2, B.Numero64>},
  codificado: {P.prefixar_tamanho(4, B.numero64_bytes(n), B.utf8(s)) == Some{bs} : Maybe<&2, List<&2, U32>>}) -> TextoCodificado<s, bs>:
  match n:
    case None{}:
      L.ex_falso(TextoCodificado<s, bs>, F.nenhum_nao_algum(List<&2, U32>, bs, codificado))
    case Some{B.Numero64{+alto, +baixo}}:
      TextoCodificado{alto, baixo, valido, medida, F.algum_injetivo(List<&2, U32>, bytes_texto(alto, baixo, s), bs, codificado)}

law codificacao_de_texto_expoe_texto_medida_e_bytes_exatos:
  for +s: String
  for -bs: List<&2, U32>
  for +codificado: {P.codificar(D.VTexto{s}) == Some{bs} : Maybe<&2, List<&2, U32>>}
  TextoCodificado<s, bs>
def codificacao_de_texto_expoe_texto_medida_e_bytes_exatos(s, bs, codificado):
  +unicode = codificacao_exige_valor_valido(D.unicode_valido(s), P.finalizar(P.codificar_parcial(D.VTexto{s})), bs, codificado)
  +valido = Equal.trans(Bool, B.texto_valido(s), D.unicode_valido(s), True{}, predicados_de_texto_concordam(s), unicode)
  texto = Equal.trans(Maybe<&2, List<&2, U32>>, P.texto(s), P.codificar(D.VTexto{s}), Some{bs},
    Equal.trans(Maybe<&2, List<&2, U32>>, P.texto(s), P.finalizar(P.atomo_opcional(P.texto(s))), P.codificar(D.VTexto{s}),
      Equal.sym(Maybe<&2, List<&2, U32>>, P.finalizar(P.atomo_opcional(P.texto(s))), P.texto(s), finalizar_atomo_opcional_preserva_resultado(P.texto(s))),
      Equal.sym(Maybe<&2, List<&2, U32>>, P.codificar(D.VTexto{s}), P.finalizar(P.codificar_parcial(D.VTexto{s})), K.valor_valido_libera_codificacao(D.VTexto{s}, unicode))), codificado)
  tamanho_textual_codificado(B.nat64(B.comprimento(B.utf8(s))), s, bs, valido, {==},
    (%valido : {P.texto_casos(_, B.utf8(s)) == Some{bs} : Maybe<&2, List<&2, U32>>}
      texto))

def aceitar_texto_codificado(+s: String, +bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64,
  medida_corpo: {B.nat64(B.comprimento(bs)) == Some{corpo} : Maybe<&2, B.Numero64>},
  cabe: {C.menor_igual64(corpo, teto) == True{} : Bool},
  dados: TextoCodificado<s, bs>) -> {C.decodificar(bs, teto) == C.Decodificado{D.VTexto{s}} : C.Resultado}:
  match dados:
    case TextoCodificado{+alto, +baixo, valido, medida, +bytes}:
      %bytes : {C.decodificar(_, teto) == C.Decodificado{D.VTexto{s}} : C.Resultado}
      todo_texto_canonico_dentro_do_limite_e_aceito(s, alto, baixo, corpo, teto, valido, medida,
        (%Equal.sym(List<&2, U32>, bytes_texto(alto, baixo, s), bs, bytes) :
          {B.nat64(B.comprimento(_)) == Some{corpo} : Maybe<&2, B.Numero64>}
          medida_corpo), cabe)

law toda_codificacao_textual_dentro_do_limite_e_aceita:
  for +s: String
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +codificado: {P.codificar(D.VTexto{s}) == Some{bs} : Maybe<&2, List<&2, U32>>}
  for medida_corpo: {B.nat64(B.comprimento(bs)) == Some{corpo} : Maybe<&2, B.Numero64>}
  for cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {C.decodificar(bs, teto) == C.Decodificado{D.VTexto{s}} : C.Resultado}
def toda_codificacao_textual_dentro_do_limite_e_aceita(s, bs, corpo, teto, codificado, medida_corpo, cabe):
  aceitar_texto_codificado(s, bs, corpo, teto, medida_corpo, cabe, codificacao_de_texto_expoe_texto_medida_e_bytes_exatos(s, bs, codificado))

law codificar_texto_medido_e_exato:
  for +s: String
  for +alto: U32
  for +baixo: U32
  for +valido: {B.texto_valido(s) == True{} : Bool}
  for medida: {B.nat64(B.comprimento(B.utf8(s))) == Some{B.Numero64{alto, baixo}} : Maybe<&2, B.Numero64>}
  {P.codificar(D.VTexto{s}) == Some{bytes_texto(alto, baixo, s)} : Maybe<&2, List<&2, U32>>}
def codificar_texto_medido_e_exato(s, alto, baixo, valido, medida):
  unicode = Equal.trans(Bool, D.unicode_valido(s), B.texto_valido(s), True{}, Equal.sym(Bool, B.texto_valido(s), D.unicode_valido(s), predicados_de_texto_concordam(s)), valido)
  Equal.trans(Maybe<&2, List<&2, U32>>, P.codificar(D.VTexto{s}), P.texto(s), Some{bytes_texto(alto, baixo, s)},
    Equal.trans(Maybe<&2, List<&2, U32>>, P.codificar(D.VTexto{s}), P.finalizar(P.atomo_opcional(P.texto(s))), P.texto(s),
      K.valor_valido_libera_codificacao(D.VTexto{s}, unicode), finalizar_atomo_opcional_preserva_resultado(P.texto(s))),
    (%Equal.sym(Bool, B.texto_valido(s), True{}, valido) : {P.texto_casos(_, B.utf8(s)) == Some{bytes_texto(alto, baixo, s)} : Maybe<&2, List<&2, U32>>}
      %Equal.sym(Maybe<&2, B.Numero64>, B.nat64(B.comprimento(B.utf8(s))), Some{B.Numero64{alto, baixo}}, medida) :
        {P.prefixar_tamanho(4, B.numero64_bytes(_), B.utf8(s)) == Some{bytes_texto(alto, baixo, s)} : Maybe<&2, List<&2, U32>>}
      {==}))
