# Extracao canonica do NOME a partir da execucao real de TagNome.
# As unicas premissas publicas sao octetos validos e chegada a Pronto.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./Ordens.bend as O
import ./CodecPercurso.bend as R
import ./CodecPalavrasBE64.bend as H
import ./CodecAceitacaoPalavra.bend as W
import ./CodecAceitacaoTexto.bend as T
import ./CodecConteudo.bend as G
import ./CodecComposicao.bend as X
import ./CodecMontagem.bend as M
import ./CodecNomesASCII.bend as A
import ./CodecCanonico.bend as K

def inicio(pilha: C.Pilha, corpo: B.Numero64, teto: B.Numero64) -> R.Quadro:
  R.Quadro{corpo, teto, C.TagNome{pilha}}

def conteudo(+q: B.Numero64, pilha: C.Pilha) -> C.Maquina:
  C.Conteudo{True{}, C.um64(q), C.diminuir64(q), C.Inicio{}, "", pilha}

# Em uma pilha Nome, esta conclusao reduz a comparacao real com anterior.
# Outras pilhas recusam emitir_nome e nao admitem continuacao aceita.
def OrdemNome(pilha: C.Pilha, nome: String) -> Type:
  match pilha:
    case C.Nome{u, q, anterior, xs, pai}:
      {String.is_lt(anterior, nome) == True{} : Bool}
    case _:
      Empty

law emissao_nome_recusada_absorve_todo_sufixo:
  for +pilha: C.Pilha
  for +nome: String
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for recusado: {C.emitir_nome(pilha, nome) == C.Invalido{} : C.Maquina}
  {R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.emitir_nome(pilha, nome)})) == C.Invalido{} : C.Maquina}
def emissao_nome_recusada_absorve_todo_sufixo(pilha, nome, bs, corpo, teto, recusado):
  %Equal.sym(C.Maquina, C.emitir_nome(pilha, nome), C.Invalido{}, recusado) :
    {R.maquina(R.executar(bs, R.Quadro{corpo, teto, _})) == C.Invalido{} : C.Maquina}
  G.executar_invalido_permanece_invalido(bs, corpo, teto)

def nome_conferido_aceito(valido: Bool, +u: Bool, +q: B.Numero64,
  +anterior: String, +nome: String, +xs: List<&2, D.Campo>, +pai: C.Pilha,
  +bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64, -v: D.Valor,
  teste: {D.nome_valido(nome) && String.is_lt(anterior, nome) == valido : Bool},
  aceito: {R.maquina(R.executar(bs, R.Quadro{corpo, teto,
    C.nome_conferido(valido, u, q, nome, xs, pai)})) == C.Pronto{v} : C.Maquina}) ->
  L.E<{D.nome_valido(nome) == True{} : Bool}, {String.is_lt(anterior, nome) == True{} : Bool}>:
  match valido:
    case False{}:
      T.invalido_nao_termina_pronto(
        L.E<{D.nome_valido(nome) == True{} : Bool}, {String.is_lt(anterior, nome) == True{} : Bool}>,
        bs, corpo, teto, v, aceito)
    case True{}:
      F.e_booleano_separar(D.nome_valido(nome), String.is_lt(anterior, nome), teste)

law continuacao_nome_aceita_confere_validade_e_ordem:
  for +pilha: C.Pilha
  for +nome: String
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for -v: D.Valor
  for aceito: {R.maquina(R.executar(bs,
    R.Quadro{corpo, teto, C.emitir_nome(pilha, nome)})) == C.Pronto{v} : C.Maquina}
  L.E<{D.nome_valido(nome) == True{} : Bool}, OrdemNome(pilha, nome)>
def continuacao_nome_aceita_confere_validade_e_ordem(pilha, nome, bs, corpo, teto, v, aceito):
  match pilha:
    case C.Nome{+u, +q, +anterior, +xs, +pai}:
      nome_conferido_aceito(D.nome_valido(nome) && String.is_lt(anterior, nome),
        u, q, anterior, nome, xs, pai, bs, corpo, teto, v, {==}, aceito)
    case C.Raiz{}:
      T.invalido_nao_termina_pronto(L.E<{D.nome_valido(nome) == True{} : Bool}, Empty>,
        bs, corpo, teto, v, aceito)
    case C.Lista{u, q, xs, pai}:
      T.invalido_nao_termina_pronto(L.E<{D.nome_valido(nome) == True{} : Bool}, Empty>,
        bs, corpo, teto, v, aceito)
    case C.Campo{u, q, n, xs, pai}:
      T.invalido_nao_termina_pronto(L.E<{D.nome_valido(nome) == True{} : Bool}, Empty>,
        bs, corpo, teto, v, aceito)

law executar_acima_permanece_acima:
  for bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  {R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.Acima{}})) == C.Acima{} : C.Maquina}
def executar_acima_permanece_acima(bs, corpo, teto):
  match bs:
    case Nil{}:
      {==}
    case Con{b, t}:
      executar_acima_permanece_acima(t, C.diminuir64(corpo), C.diminuir64(teto))

def acima_nao_termina_pronto(-A0: Type, +bs: List<&2, U32>,
  +corpo: B.Numero64, +teto: B.Numero64, -v: D.Valor,
  aceito: {R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.Acima{}})) == C.Pronto{v} : C.Maquina}) -> A0:
  L.ex_falso(A0, F.falso_nao_verdadeiro(Equal.cong(C.Maquina, Bool, m => T.pronto(m), C.Acima{}, C.Pronto{v},
    Equal.trans(C.Maquina, C.Acima{}, R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.Acima{}})), C.Pronto{v},
      Equal.sym(C.Maquina, R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.Acima{}})), C.Acima{},
        executar_acima_permanece_acima(bs, corpo, teto)), aceito))))

law nome_de_tamanho_zero_nao_aceita:
  for +bs: List<&2, U32>
  for +q: B.Numero64
  for +pilha: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for -v: D.Valor
  for aceito: {R.maquina(R.executar(bs, R.Quadro{corpo, teto,
    C.abrir_variavel(True{}, C.NomeTexto{}, q, pilha)})) == C.Pronto{v} : C.Maquina}
  Empty
def nome_de_tamanho_zero_nao_aceita(bs, q, pilha, corpo, teto, v, aceito):
  T.invalido_nao_termina_pronto(Empty, bs, corpo, teto, v, aceito)

def abrir_nome_aceito(cabe: Bool, +q: B.Numero64, +pilha: C.Pilha,
  +bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64, -v: D.Valor,
  aceito: {R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.abrir_nome(cabe, q, pilha)})) == C.Pronto{v} : C.Maquina}) ->
  {C.abrir_nome(cabe, q, pilha) == conteudo(q, pilha) : C.Maquina}:
  match cabe:
    case False{}:
      T.invalido_nao_termina_pronto({C.Invalido{} == conteudo(q, pilha) : C.Maquina}, bs, corpo, teto, v, aceito)
    case True{}:
      {==}

def abrir_variavel_nome_aceito(vazio: Bool, +q: B.Numero64, +pilha: C.Pilha,
  +bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64, -v: D.Valor,
  aceito: {R.maquina(R.executar(bs, R.Quadro{corpo, teto,
    C.abrir_variavel(vazio, C.NomeTexto{}, q, pilha)})) == C.Pronto{v} : C.Maquina}) ->
  {C.abrir_variavel(vazio, C.NomeTexto{}, q, pilha) == conteudo(q, pilha) : C.Maquina}:
  match vazio:
    case True{}:
      L.ex_falso({C.Invalido{} == conteudo(q, pilha) : C.Maquina},
        nome_de_tamanho_zero_nao_aceita(bs, q, pilha, corpo, teto, v, aceito))
    case False{}:
      abrir_nome_aceito(C.menor_igual64(q, B.Numero64{0, 64}), q, pilha, bs, corpo, teto, v, aceito)

def abrir_conferido_nome_aceito(conf: C.Conferencia, +q: B.Numero64, +pilha: C.Pilha,
  +bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64, -v: D.Valor,
  aceito: {R.maquina(R.executar(bs, R.Quadro{corpo, teto,
    C.abrir_conferido(conf, C.NomeTexto{}, q, pilha)})) == C.Pronto{v} : C.Maquina}) ->
  {C.abrir_conferido(conf, C.NomeTexto{}, q, pilha) == conteudo(q, pilha) : C.Maquina}:
  match conf:
    case C.Grande{}:
      acima_nao_termina_pronto({C.Acima{} == conteudo(q, pilha) : C.Maquina}, bs, corpo, teto, v, aceito)
    case C.Curto{}:
      T.invalido_nao_termina_pronto({C.Invalido{} == conteudo(q, pilha) : C.Maquina}, bs, corpo, teto, v, aceito)
    case C.Cabe{}:
      abrir_variavel_nome_aceito(C.zero64(q), q, pilha, bs, corpo, teto, v, aceito)

law cabecalho_nome_aceito_abre_conteudo:
  for +alto: U32
  for +baixo: U32
  for +pilha: C.Pilha
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for -v: D.Valor
  for aceito: {R.maquina(R.executar(bs, R.Quadro{corpo, teto,
    C.concluir_palavra(C.NomeTexto{}, alto, baixo, pilha, corpo, teto)})) == C.Pronto{v} : C.Maquina}
  {C.concluir_palavra(C.NomeTexto{}, alto, baixo, pilha, corpo, teto) == conteudo(B.Numero64{alto, baixo}, pilha) : C.Maquina}
def cabecalho_nome_aceito_abre_conteudo(alto, baixo, pilha, bs, corpo, teto, v, aceito):
  abrir_conferido_nome_aceito(C.conferir(
    C.somar_opcionais(C.minimo_campo(C.NomeTexto{}, B.Numero64{alto, baixo}), C.minimo_pilha(pilha)), corpo, teto),
    B.Numero64{alto, baixo}, pilha, bs, corpo, teto, v, aceito)

# bytes_nome e um prefixo da entrada ORIGINAL. Seu cabecalho BE64 e a
# medida do UTF-8 sao conclusoes das duas inversoes, nao hipoteses.
type NomeExtraido<-bs: List<&2, U32>, -corpo: B.Numero64, -teto: B.Numero64,
  -pilha: C.Pilha, -v: D.Valor> is Type:
  NomeExtraido{bytes_nome: List<&2, U32>, nome: String, sufixo: List<&2, U32>,
    alto: U32, baixo: U32, utf8: List<&2, U32>,
    corpo_emissao: B.Numero64, teto_emissao: B.Numero64,
    cabecalho: {bytes_nome == M.prefixo(4, B.Numero64{alto, baixo}, utf8) : List<&2, U32>},
    fatoracao: {bs == B.concatenar(bytes_nome, sufixo) : List<&2, U32>},
    octetos_nome: {B.octetos_validos(bytes_nome) == True{} : Bool},
    resto_valido: {B.octetos_validos(sufixo) == True{} : Bool},
    positivo: G.NaoVazio(utf8),
    bytes: {B.utf8(nome) == utf8 : List<&2, U32>},
    medida: {B.nat64(B.comprimento(utf8)) == Some{B.Numero64{alto, baixo}} : Maybe<&2, B.Numero64>},
    valido: {D.nome_valido(nome) == True{} : Bool},
    ordem: OrdemNome(pilha, nome),
    canonico: {P.texto(nome) == Some{bytes_nome} : Maybe<&2, List<&2, U32>>},
    corpo_exato: {corpo_emissao == H.diminuir(B.comprimento(bytes_nome), corpo) : B.Numero64},
    teto_exato: {teto_emissao == H.diminuir(B.comprimento(bytes_nome), teto) : B.Numero64},
    emissao: {R.executar(bytes_nome, inicio(pilha, corpo, teto)) ==
      R.Quadro{corpo_emissao, teto_emissao, C.emitir_nome(pilha, nome)} : R.Quadro},
    execucao: {R.executar(sufixo, R.Quadro{corpo_emissao, teto_emissao, C.emitir_nome(pilha, nome)}) ==
      R.executar(bs, inicio(pilha, corpo, teto)) : R.Quadro},
    continuacao: {R.maquina(R.executar(sufixo,
      R.Quadro{corpo_emissao, teto_emissao, C.emitir_nome(pilha, nome)})) == C.Pronto{v} : C.Maquina}}

def corpo_quadro(q: R.Quadro) -> B.Numero64:
  R.Quadro{c, t, m} = q
  c

def teto_quadro(q: R.Quadro) -> B.Numero64:
  R.Quadro{c, t, m} = q
  t

def execucao_apos_prefixo(+bs: List<&2, U32>, +prefixo: List<&2, U32>, +sufixo: List<&2, U32>,
  +inicio0: R.Quadro, +fim: R.Quadro,
  divisao: {bs == B.concatenar(prefixo, sufixo) : List<&2, U32>},
  emissao: {R.executar(prefixo, inicio0) == fim : R.Quadro}) ->
  {R.executar(sufixo, fim) == R.executar(bs, inicio0) : R.Quadro}:
  Equal.sym(R.Quadro, R.executar(bs, inicio0), R.executar(sufixo, fim),
    Equal.trans(R.Quadro, R.executar(bs, inicio0), R.executar(B.concatenar(prefixo, sufixo), inicio0), R.executar(sufixo, fim),
      Equal.cong(List<&2, U32>, R.Quadro, xs => R.executar(xs, inicio0), bs, B.concatenar(prefixo, sufixo), divisao),
      Equal.trans(R.Quadro, R.executar(B.concatenar(prefixo, sufixo), inicio0),
        R.executar(sufixo, R.executar(prefixo, inicio0)), R.executar(sufixo, fim),
        R.execucao_de_concatenacao(prefixo, sufixo, inicio0),
        Equal.cong(R.Quadro, R.Quadro, q => R.executar(sufixo, q), R.executar(prefixo, inicio0), fim, emissao))))

# Empacota os fatos ja extraidos; validade e ordem sao obtidas somente
# AGORA, pela continuacao aceita de emitir_nome.
def concluir_nome_extraido(+bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64,
  +pilha: C.Pilha, -v: D.Valor, +alto: U32, +baixo: U32,
  +utf8: List<&2, U32>, +nome: String, +sufixo: List<&2, U32>,
  +ca: B.Numero64, +ta: B.Numero64,
  +divisao: {bs == B.concatenar(M.prefixo(4, B.Numero64{alto, baixo}, utf8), sufixo) : List<&2, U32>},
  positivo: G.NaoVazio(utf8),
  +bytes: {B.utf8(nome) == utf8 : List<&2, U32>},
  +medida: {B.nat64(B.comprimento(utf8)) == Some{B.Numero64{alto, baixo}} : Maybe<&2, B.Numero64>},
  validos: {B.octetos_validos(bs) == True{} : Bool},
  +emissao: {R.executar(M.prefixo(4, B.Numero64{alto, baixo}, utf8), inicio(pilha, corpo, teto)) ==
    R.Quadro{ca, ta, C.emitir_nome(pilha, nome)} : R.Quadro},
  +aceito: {R.maquina(R.executar(sufixo,
    R.Quadro{ca, ta, C.emitir_nome(pilha, nome)})) == C.Pronto{v} : C.Maquina}) ->
  NomeExtraido<bs, corpo, teto, pilha, v>:
  +prefixo = M.prefixo(4, B.Numero64{alto, baixo}, utf8)
  +fim = {R.Quadro{ca, ta, C.emitir_nome(pilha, nome)} : R.Quadro}
  +contadores = Equal.trans(R.Quadro, fim, R.executar(prefixo, inicio(pilha, corpo, teto)),
    X.depois(prefixo, corpo, teto, C.emitir_nome(pilha, nome)),
    Equal.sym(R.Quadro, R.executar(prefixo, inicio(pilha, corpo, teto)), fim, emissao),
    X.execucao_com_maquina_conhecida_tem_contadores_exatos(prefixo, corpo, teto, C.TagNome{pilha},
      C.emitir_nome(pilha, nome), Equal.cong(R.Quadro, C.Maquina, q => R.maquina(q),
        R.executar(prefixo, inicio(pilha, corpo, teto)), fim, emissao)))
  F.com_par(NomeExtraido<bs, corpo, teto, pilha, v>,
    {B.octetos_validos(prefixo) == True{} : Bool}, {B.octetos_validos(sufixo) == True{} : Bool},
    W.separar_octetos_validos(prefixo, sufixo,
      (%divisao :
        {B.octetos_validos(_) == True{} : Bool}
        validos)),
    octetos_nome => resto_valido =>
      F.com_par(NomeExtraido<bs, corpo, teto, pilha, v>,
        {D.nome_valido(nome) == True{} : Bool}, OrdemNome(pilha, nome),
        continuacao_nome_aceita_confere_validade_e_ordem(pilha, nome, sufixo, ca, ta, v, aceito),
        +valido => ordem =>
          NomeExtraido{prefixo, nome, sufixo, alto, baixo, utf8, ca, ta, {==}, divisao,
            octetos_nome, resto_valido, positivo, bytes, medida, valido, ordem,
            M.nome_medido_tem_codificacao_textual_exata(nome, utf8, B.Numero64{alto, baixo},
              A.nome_valido_e_texto_valido(nome, valido), bytes, medida),
            Equal.cong(R.Quadro, B.Numero64, q => corpo_quadro(q), fim,
              X.depois(prefixo, corpo, teto, C.emitir_nome(pilha, nome)), contadores),
            Equal.cong(R.Quadro, B.Numero64, q => teto_quadro(q), fim,
              X.depois(prefixo, corpo, teto, C.emitir_nome(pilha, nome)), contadores),
            emissao, execucao_apos_prefixo(bs, prefixo, sufixo, inicio(pilha, corpo, teto), fim, divisao, emissao), aceito}))

def montar_nome_textual(+bs: List<&2, U32>, +resto: List<&2, U32>,
  +alto: U32, +baixo: U32, +pilha: C.Pilha, +corpo: B.Numero64, +teto: B.Numero64, -v: D.Valor,
  validos: {B.octetos_validos(bs) == True{} : Bool},
  divisao_cabecalho: {bs == Con{4, B.concatenar(B.be64(alto, baixo), resto)} : List<&2, U32>},
  cabecalho: {R.executar(Con{4, B.be64(alto, baixo)}, inicio(pilha, corpo, teto)) ==
    R.Quadro{H.diminuir(8n, C.diminuir64(corpo)), H.diminuir(8n, C.diminuir64(teto)),
      conteudo(B.Numero64{alto, baixo}, pilha)} : R.Quadro},
  extraido: T.ConteudoContadoAceito<resto, H.diminuir(8n, C.diminuir64(corpo)),
    H.diminuir(8n, C.diminuir64(teto)), True{}, B.Numero64{alto, baixo}, pilha, v>) ->
  NomeExtraido<bs, corpo, teto, pilha, v>:
  match extraido:
    case T.ConteudoContadoAceito{+utf8, +sufixo, +nome, +ca, +ta,
      divisao_texto, positivo, +bytes, +medida, transducao, emissao_texto, continuacao}:
      +prefixo = M.prefixo(4, B.Numero64{alto, baixo}, utf8)
      +cab = {Con{4, B.be64(alto, baixo)} : List<&2, U32>}
      +c9 = H.diminuir(8n, C.diminuir64(corpo))
      +t9 = H.diminuir(8n, C.diminuir64(teto))
      divisao = Equal.trans(List<&2, U32>, bs, B.concatenar(cab, resto), B.concatenar(prefixo, sufixo),
        divisao_cabecalho,
        Equal.trans(List<&2, U32>, B.concatenar(cab, resto), B.concatenar(cab, B.concatenar(utf8, sufixo)),
          B.concatenar(prefixo, sufixo),
          Equal.cong(List<&2, U32>, List<&2, U32>, xs => B.concatenar(cab, xs),
            resto, B.concatenar(utf8, sufixo), divisao_texto),
          Equal.sym(List<&2, U32>, B.concatenar(prefixo, sufixo), B.concatenar(cab, B.concatenar(utf8, sufixo)),
            K.concatenacao_associativa(cab, utf8, sufixo))))
      emissao = Equal.trans(R.Quadro, R.executar(prefixo, inicio(pilha, corpo, teto)),
        R.executar(utf8, R.executar(cab, inicio(pilha, corpo, teto))), R.Quadro{ca, ta, C.emitir_nome(pilha, nome)},
        R.execucao_de_concatenacao(cab, utf8, inicio(pilha, corpo, teto)),
        Equal.trans(R.Quadro, R.executar(utf8, R.executar(cab, inicio(pilha, corpo, teto))),
          R.executar(utf8, R.Quadro{c9, t9, conteudo(B.Numero64{alto, baixo}, pilha)}),
          R.Quadro{ca, ta, C.emitir_nome(pilha, nome)},
          Equal.cong(R.Quadro, R.Quadro, q => R.executar(utf8, q), R.executar(cab, inicio(pilha, corpo, teto)),
            R.Quadro{c9, t9, conteudo(B.Numero64{alto, baixo}, pilha)}, cabecalho), emissao_texto))
      concluir_nome_extraido(bs, corpo, teto, pilha, v, alto, baixo, utf8, nome, sufixo, ca, ta,
        divisao, positivo, bytes, medida, validos, emissao, continuacao)

def montar_nome_palavra(+bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64,
  +pilha: C.Pilha, -v: D.Valor,
  validos: {B.octetos_validos(Con{4, bs}) == True{} : Bool},
  palavra: W.PalavraExtraida<bs, C.NomeTexto{}, pilha, C.diminuir64(corpo), C.diminuir64(teto), v>) ->
  NomeExtraido<Con{4, bs}, corpo, teto, pilha, v>:
  match palavra:
    case W.Extraida{+a, +b, +c, +d, +e, +f0, +g, +h, +resto, +alto, +baixo,
      fatoracao, octetos, resto_valido, numero, +be64, fatoracao_be64, quadro, execucao, +pronto}:
      +c9 = H.diminuir(8n, C.diminuir64(corpo))
      +t9 = H.diminuir(8n, C.diminuir64(teto))
      +abertura = cabecalho_nome_aceito_abre_conteudo(alto, baixo, pilha, resto, c9, t9, v, pronto)
      cabecalho = Equal.trans(R.Quadro,
        R.executar(Con{4, B.be64(alto, baixo)}, inicio(pilha, corpo, teto)),
        W.apos_palavra(C.NomeTexto{}, alto, baixo, pilha, C.diminuir64(corpo), C.diminuir64(teto)),
        R.Quadro{c9, t9, conteudo(B.Numero64{alto, baixo}, pilha)},
        (%Equal.sym(List<&2, U32>, B.be64(alto, baixo), [a, b, c, d, e, f0, g, h], be64) :
          {R.executar(_, W.inicio(C.NomeTexto{}, pilha, C.diminuir64(corpo), C.diminuir64(teto))) ==
          W.apos_palavra(C.NomeTexto{}, alto, baixo, pilha, C.diminuir64(corpo), C.diminuir64(teto)) : R.Quadro}
          quadro),
        Equal.cong(C.Maquina, R.Quadro, m => R.Quadro{c9, t9, m},
          C.concluir_palavra(C.NomeTexto{}, alto, baixo, pilha, c9, t9),
          conteudo(B.Numero64{alto, baixo}, pilha), abertura))
      montar_nome_textual(Con{4, bs}, resto, alto, baixo, pilha, corpo, teto, v, validos,
        Equal.cong(List<&2, U32>, List<&2, U32>, xs => Con{4, xs}, bs, B.concatenar(B.be64(alto, baixo), resto), fatoracao_be64),
        cabecalho,
        T.conteudo_contado_aceito_reconstroi_prefixo_texto_e_contagem(resto, c9, t9, True{}, B.Numero64{alto, baixo}, pilha, v,
          (%abertura :
            {R.maquina(R.executar(resto, R.Quadro{c9, t9, _})) == C.Pronto{v} : C.Maquina}
            pronto)))

def ler_tag_nome_aceita(correto: Bool, +pilha: C.Pilha, +bs: List<&2, U32>,
  +corpo: B.Numero64, +teto: B.Numero64, -v: D.Valor,
  aceito: {R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.ler_tag_nome(correto, pilha)})) == C.Pronto{v} : C.Maquina}) ->
  {correto == True{} : Bool}:
  match correto:
    case False{}:
      T.invalido_nao_termina_pronto({False{} == True{} : Bool}, bs, corpo, teto, v, aceito)
    case True{}:
      {==}

# A tag e um U32 arbitrario recebido. Sua igualdade a 4 e extraida da
# aceitacao de ler_tag_nome(U32.is_eq(tag,4)), antes de inverter a palavra.
law tag_nome_aceita_extrai_prefixo_canonico:
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +pilha: C.Pilha
  for -v: D.Valor
  for +validos: {B.octetos_validos(bs) == True{} : Bool}
  for +aceito: {R.maquina(R.executar(bs, inicio(pilha, corpo, teto))) == C.Pronto{v} : C.Maquina}
  NomeExtraido<bs, corpo, teto, pilha, v>
def tag_nome_aceita_extrai_prefixo_canonico(bs, corpo, teto, pilha, v, validos, aceito):
  match bs:
    case Nil{}:
      L.ex_falso(NomeExtraido<Nil{}, corpo, teto, pilha, v>,
        F.falso_nao_verdadeiro(Equal.cong(C.Maquina, Bool, m => T.pronto(m), C.TagNome{pilha}, C.Pronto{v}, aceito)))
    case Con{+tag, +tail}:
      +tag4 = O.u32_igual(tag, 4, O.cmp_eq(U32.cmp(tag, 4),
        ler_tag_nome_aceita(U32.is_eq(tag, 4), pilha, tail, C.diminuir64(corpo), C.diminuir64(teto), v, aceito)))
      %Equal.sym(U32, tag, 4, tag4) : NomeExtraido<Con{_, tail}, corpo, teto, pilha, v>
      montar_nome_palavra(tail, corpo, teto, pilha, v,
        (%tag4 : {B.octetos_validos(Con{_, tail}) == True{} : Bool}
          validos),
        W.palavra_aceita_extrai_be64_e_execucao_restante(tail, C.NomeTexto{}, pilha,
          C.diminuir64(corpo), C.diminuir64(teto), v,
          F.e_booleano_direita(U32.is_le(tag, 255), B.octetos_validos(tail), validos),
          (%tag4 :
            {R.maquina(R.executar(Con{_, tail}, inicio(pilha, corpo, teto))) == C.Pronto{v} : C.Maquina}
            aceito)))

# Especializacao para o instante exato pedido pelo passo de registros.
# OrdemNome reduz aqui a String.is_lt(anterior,nome)==True.
law nome_aceito_extrai_prefixo_canonico:
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +u: Bool
  for +q: B.Numero64
  for +anterior: String
  for +xs: List<&2, D.Campo>
  for +pai: C.Pilha
  for -v: D.Valor
  for validos: {B.octetos_validos(bs) == True{} : Bool}
  for aceito: {R.maquina(R.executar(bs,
    R.Quadro{corpo, teto, C.TagNome{C.Nome{u, q, anterior, xs, pai}}})) == C.Pronto{v} : C.Maquina}
  NomeExtraido<bs, corpo, teto, C.Nome{u, q, anterior, xs, pai}, v>
def nome_aceito_extrai_prefixo_canonico(bs, corpo, teto, u, q, anterior, xs, pai, v, validos, aceito):
  tag_nome_aceita_extrai_prefixo_canonico(bs, corpo, teto, C.Nome{u, q, anterior, xs, pai}, v, validos, aceito)
