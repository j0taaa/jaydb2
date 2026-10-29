# Reaplicacoes universais e amostras concretas dos adaptadores REAIS.
import Base
import ../../contrato/Bytes.bend as B
import ../../contrato/Dados.bend as D
import ../../contrato/Protocolo.bend as P
import ../../contrato/Semantica.bend as S
import ../../contrato/Requisitos.bend as R
import ../../contrato/Interface.bend as I
import ../../contrato/Logica.bend as L
import ../../src/Codec.bend as C
import ../../src/Entrada.bend as E
import ../../src/Transporte.bend as T
import ../../proof/Entrada.bend as G
import ../../proof/CodecMinimos.bend as M

# Os fallbacks sao apenas funcoes de fixture. Cada uso no teorema geral
# abaixo prova separadamente codificacao, medida e montagem por igualdade.
def lista_ou_vazio(resultado: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match resultado:
    case None{}:
      Nil{}
    case Some{bs}:
      bs

def bytes(v: D.Valor) -> List<&2, U32>:
  lista_ou_vazio(P.codificar(v))

def numero_ou_zero(resultado: Maybe<&2, B.Numero64>) -> B.Numero64:
  match resultado:
    case None{}:
      B.Numero64{0, 0}
    case Some{n}:
      n

def numero(bs: List<&2, U32>) -> B.Numero64:
  numero_ou_zero(B.nat64(B.comprimento(bs)))

def pacote(be: List<&2, U32>, br: List<&2, U32>) -> List<&2, U32>:
  lista_ou_vazio(T.juntar(be, br))

def usuario(+id: String, cred: String) -> D.Linha:
  D.Linha{id, [D.Campo{"credencial", D.VTexto{cred}}, D.Campo{"id", D.VTexto{id}},
    D.Campo{"tipo", D.VTexto{"pessoa"}}]}

def esquema() -> D.Esquema:
  D.Esquema{Nil{}}

def publicado() -> D.Estado:
  D.Estado{Nil{}, [usuario("a", "primeira"), usuario("é", "segunda")]}

def argumentos() -> D.Valor:
  D.VLista{D.VInt{2147483648, 0}, D.VLista{D.VInt{2147483647, 4294967295},
    D.VLista{D.VAusente{}, D.VLista{D.VTexto{"é\n𝄞"}, D.VListaVazia{}}}}}

def requisicao() -> P.Requisicao:
  P.Requisicao{"segunda", "fonte exata\n𝄞", argumentos(), "π\n\\prova"}

def estado_bytes() -> List<&2, U32>:
  bytes(D.estado_valor(publicado()))

def mensagem_bytes() -> List<&2, U32>:
  bytes(P.requisicao_valor(requisicao()))

def montado() -> List<&2, U32>:
  pacote(estado_bytes(), mensagem_bytes())

def limites() -> S.Limites:
  S.Limites{B.comprimento(mensagem_bytes()), B.comprimento(estado_bytes()), 0n}

def limite_mensagem_zero() -> S.Limites:
  S.Limites{0n, B.comprimento(estado_bytes()), 0n}

law pronta_exata_nos_dois_limites_inclusivos:
  {E.decodificar(montado(), esquema(), limites()) == E.Pronta{publicado(), requisicao()} : E.PreAutenticacao}
def pronta_exata_nos_dois_limites_inclusivos():
  G.bytes_canonicos_montados_produzem_pronta_exata(esquema(), publicado(), requisicao(), limites(),
    estado_bytes(), mensagem_bytes(), montado(), numero(estado_bytes()), numero(mensagem_bytes()),
    numero(estado_bytes()), numero(mensagem_bytes()), {==}, {==}, {==}, {==}, {==}, {==}, {==},
    M.menor_igual64_reflexivo(numero(estado_bytes())), M.menor_igual64_reflexivo(numero(mensagem_bytes())), {==})

law autenticacao_no_fim_do_cadastro_com_unicode_e_bits_exatos:
  {E.analisar(montado(), esquema(), limites()) ==
    E.Recebida{publicado(), requisicao(), D.Contexto{"é", "pessoa"}} : E.Analise}
def autenticacao_no_fim_do_cadastro_com_unicode_e_bits_exatos():
  G.analisar_aceita_exatamente_contexto_autenticado(montado(), esquema(), limites(), publicado(),
    requisicao(), D.Contexto{"é", "pessoa"}, pronta_exata_nos_dois_limites_inclusivos(), {==})

law trabalho_com_vazio_e_duplicatas_nao_altera_semantica_original:
  {E.autenticar(Some{P.Requisicao{"", "codigo", D.VAusente{}, "prova"}},
    D.Estado{Nil{}, [usuario("a", ""), usuario("b", "")]}) ==
    E.Recebida{D.Estado{Nil{}, [usuario("a", ""), usuario("b", "")]},
      P.Requisicao{"", "codigo", D.VAusente{}, "prova"}, D.Contexto{"a", "pessoa"}} : E.Analise}
def trabalho_com_vazio_e_duplicatas_nao_altera_semantica_original():
  G.autenticar_preserva_exatamente_estado_requisicao_e_contexto(
    D.Estado{Nil{}, [usuario("a", ""), usuario("b", "")]}, P.Requisicao{"", "codigo", D.VAusente{}, "prova"})

law estado_publicado_com_credencial_vazia_e_recusado:
  {E.analisar(pacote(estado_bytes(), bytes(P.requisicao_valor(P.Requisicao{"", "c", D.VAusente{}, "p"}))),
    esquema(), limites()) == E.Rejeitada{S.Autenticacao{}} : E.Analise}
def estado_publicado_com_credencial_vazia_e_recusado():
  {==}

law credencial_desconhecida_e_recusada_apos_envelope:
  {E.analisar(pacote(estado_bytes(), bytes(P.requisicao_valor(P.Requisicao{"outra", "c", D.VAusente{}, "p"}))),
    esquema(), limites()) == E.Rejeitada{S.Autenticacao{}} : E.Analise}
def credencial_desconhecida_e_recusada_apos_envelope():
  {==}

law header_privado_incompleto_nao_e_erro_cliente:
  {E.analisar([0, 0, 0, 0, 0, 0, 0], esquema(), limites()) == E.TransporteInvalido{} : E.Analise}
def header_privado_incompleto_nao_e_erro_cliente():
  {==}

law estado_invalido_precede_envelope_valido:
  {E.analisar(pacote([0], mensagem_bytes()), esquema(), limites()) == E.TransporteInvalido{} : E.Analise}
def estado_invalido_precede_envelope_valido():
  {==}

law codec_do_estado_invalido_nao_e_erro_cliente:
  {E.analisar(pacote([255], mensagem_bytes()), esquema(), limites()) == E.TransporteInvalido{} : E.Analise}
def codec_do_estado_invalido_nao_e_erro_cliente():
  {==}

law valor_canonico_fora_do_envelope_produz_entrada:
  {E.analisar(pacote(estado_bytes(), [0]), esquema(), limites()) == E.Rejeitada{S.Entrada{}} : E.Analise}
def valor_canonico_fora_do_envelope_produz_entrada():
  {==}

law sufixo_extra_na_mensagem_produz_entrada:
  {E.analisar(pacote(estado_bytes(), [0, 0]), esquema(), limites()) == E.Rejeitada{S.Entrada{}} : E.Analise}
def sufixo_extra_na_mensagem_produz_entrada():
  {==}

law mensagem_acima_do_teto_nao_vira_autenticacao:
  {E.analisar(montado(), esquema(), limite_mensagem_zero()) == E.Rejeitada{S.Limite{}} : E.Analise}
def mensagem_acima_do_teto_nao_vira_autenticacao():
  {==}

law estado_acima_do_teto_e_erro_transporte:
  {E.analisar(montado(), esquema(), S.Limites{1000n, 0n, 0n}) ==
    E.TransporteInvalido{} : E.Analise}
def estado_acima_do_teto_e_erro_transporte():
  {==}

law todo_estado_e_requisicao_canonicos_reaplicam_composicao:
  for +e: D.Esquema
  for +s: D.Estado
  for +r: P.Requisicao
  for +l: S.Limites
  for +be: List<&2, U32>
  for +br: List<&2, U32>
  for +bs: List<&2, U32>
  for +ce: B.Numero64
  for +cr: B.Numero64
  for +te: B.Numero64
  for +tr: B.Numero64
  for cod_e: P.Codificacao(D.estado_valor(s), be)
  for cod_r: P.Codificacao(P.requisicao_valor(r), br)
  for montagem: {T.juntar(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>}
  for medida_e: {B.nat64(B.comprimento(be)) == Some{ce} : Maybe<&2, B.Numero64>}
  for medida_r: {B.nat64(B.comprimento(br)) == Some{cr} : Maybe<&2, B.Numero64>}
  for teto_e: {B.nat64(R.limite_estado(l)) == Some{te} : Maybe<&2, B.Numero64>}
  for teto_r: {B.nat64(R.limite_mensagem(l)) == Some{tr} : Maybe<&2, B.Numero64>}
  for cabe_e: {C.menor_igual64(ce, te) == True{} : Bool}
  for cabe_r: {C.menor_igual64(cr, tr) == True{} : Bool}
  for estrutura: {D.estrutura(e, s) == True{} : Bool}
  {E.decodificar(bs, e, l) == E.Pronta{s, r} : E.PreAutenticacao}
def todo_estado_e_requisicao_canonicos_reaplicam_composicao(e, s, r, l, be, br, bs, ce, cr, te, tr,
  cod_e, cod_r, montagem, medida_e, medida_r, teto_e, teto_r, cabe_e, cabe_r, estrutura):
  G.bytes_canonicos_montados_produzem_pronta_exata(e, s, r, l, be, br, bs, ce, cr, te, tr,
  cod_e, cod_r, montagem, medida_e, medida_r, teto_e, teto_r, cabe_e, cabe_r, estrutura)

law todo_pacote_canonico_reaplica_analise_exata:
  for +e: D.Esquema
  for +s: D.Estado
  for +r: P.Requisicao
  for +l: S.Limites
  for +be: List<&2, U32>
  for +br: List<&2, U32>
  for +bs: List<&2, U32>
  for +ce: B.Numero64
  for +cr: B.Numero64
  for +te: B.Numero64
  for +tr: B.Numero64
  for cod_e: P.Codificacao(D.estado_valor(s), be)
  for cod_r: P.Codificacao(P.requisicao_valor(r), br)
  for montagem: {T.juntar(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>}
  for medida_e: {B.nat64(B.comprimento(be)) == Some{ce} : Maybe<&2, B.Numero64>}
  for medida_r: {B.nat64(B.comprimento(br)) == Some{cr} : Maybe<&2, B.Numero64>}
  for teto_e: {B.nat64(R.limite_estado(l)) == Some{te} : Maybe<&2, B.Numero64>}
  for teto_r: {B.nat64(R.limite_mensagem(l)) == Some{tr} : Maybe<&2, B.Numero64>}
  for cabe_e: {C.menor_igual64(ce, te) == True{} : Bool}
  for cabe_r: {C.menor_igual64(cr, tr) == True{} : Bool}
  for estrutura: {D.estrutura(e, s) == True{} : Bool}
  L.E<{E.decodificar(bs, e, l) == E.Pronta{s, r} : E.PreAutenticacao},
    {E.analisar(bs, e, l) == E.identidade(D.autenticar(s, I.credencial(r)), s, r) : E.Analise}>
def todo_pacote_canonico_reaplica_analise_exata(e, s, r, l, be, br, bs, ce, cr, te, tr,
  cod_e, cod_r, montagem, medida_e, medida_r, teto_e, teto_r, cabe_e, cabe_r, estrutura):
  G.bytes_canonicos_montados_sao_analisados_com_identidade_exata(e, s, r, l, be, br, bs, ce, cr, te, tr,
  cod_e, cod_r, montagem, medida_e, medida_r, teto_e, teto_r, cabe_e, cabe_r, estrutura)

law existencia_do_pacote_sem_assumir_montagem:
  for +e: D.Esquema
  for +s: D.Estado
  for +r: P.Requisicao
  for +l: S.Limites
  for +be: List<&2, U32>
  for +br: List<&2, U32>
  for +ce: B.Numero64
  for +cr: B.Numero64
  for +te: B.Numero64
  for +tr: B.Numero64
  for cod_e: P.Codificacao(D.estado_valor(s), be)
  for cod_r: P.Codificacao(P.requisicao_valor(r), br)
  for +medida_e: {B.nat64(B.comprimento(be)) == Some{ce} : Maybe<&2, B.Numero64>}
  for medida_r: {B.nat64(B.comprimento(br)) == Some{cr} : Maybe<&2, B.Numero64>}
  for teto_e: {B.nat64(R.limite_estado(l)) == Some{te} : Maybe<&2, B.Numero64>}
  for teto_r: {B.nat64(R.limite_mensagem(l)) == Some{tr} : Maybe<&2, B.Numero64>}
  for cabe_e: {C.menor_igual64(ce, te) == True{} : Bool}
  for cabe_r: {C.menor_igual64(cr, tr) == True{} : Bool}
  for estrutura: {D.estrutura(e, s) == True{} : Bool}
  G.PacotePronto(e, s, r, l, be, br)
def existencia_do_pacote_sem_assumir_montagem(e, s, r, l, be, br, ce, cr, te, tr,
  cod_e, cod_r, medida_e, medida_r, teto_e, teto_r, cabe_e, cabe_r, estrutura):
  G.toda_entrada_canonica_admissivel_tem_pacote_pronto_e_analise_exata(e, s, r, l, be, br, ce, cr, te, tr,
  cod_e, cod_r, medida_e, medida_r, teto_e, teto_r, cabe_e, cabe_r, estrutura)

law reaplicar_autenticar_preserva_exatamente_estado_requisicao_e_contexto:
  for +s: D.Estado
  for r: P.Requisicao
  {E.autenticar(Some{r}, s) == E.identidade(D.autenticar(s, I.credencial(r)), s, r) : E.Analise}
def reaplicar_autenticar_preserva_exatamente_estado_requisicao_e_contexto(s, r):
  G.autenticar_preserva_exatamente_estado_requisicao_e_contexto(s, r)

law reaplicar_analisar_pronta_e_autenticacao_estavel_exata:
  for +bs: List<&2, U32>
  for +e: D.Esquema
  for +l: S.Limites
  for +s: D.Estado
  for +r: P.Requisicao
  for pronta: {E.decodificar(bs, e, l) == E.Pronta{s, r} : E.PreAutenticacao}
  {E.analisar(bs, e, l) == E.identidade(D.autenticar(s, I.credencial(r)), s, r) : E.Analise}
def reaplicar_analisar_pronta_e_autenticacao_estavel_exata(bs, e, l, s, r, pronta):
  G.analisar_pronta_e_autenticacao_estavel_exata(bs, e, l, s, r, pronta)

law reaplicar_analisar_aceita_exatamente_contexto_autenticado:
  for +bs: List<&2, U32>
  for +e: D.Esquema
  for +l: S.Limites
  for +s: D.Estado
  for +r: P.Requisicao
  for +ctx: D.Contexto
  for pronta: {E.decodificar(bs, e, l) == E.Pronta{s, r} : E.PreAutenticacao}
  for aut: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>}
  {E.analisar(bs, e, l) == E.Recebida{s, r, ctx} : E.Analise}
def reaplicar_analisar_aceita_exatamente_contexto_autenticado(bs, e, l, s, r, ctx, pronta, aut):
  G.analisar_aceita_exatamente_contexto_autenticado(bs, e, l, s, r, ctx, pronta, aut)

law reaplicar_analisar_recusa_exatamente_autenticacao_ausente:
  for +bs: List<&2, U32>
  for +e: D.Esquema
  for +l: S.Limites
  for +s: D.Estado
  for +r: P.Requisicao
  for pronta: {E.decodificar(bs, e, l) == E.Pronta{s, r} : E.PreAutenticacao}
  for aut: {D.autenticar(s, I.credencial(r)) == None{} : Maybe<&2, D.Contexto>}
  {E.analisar(bs, e, l) == E.Rejeitada{S.Autenticacao{}} : E.Analise}
def reaplicar_analisar_recusa_exatamente_autenticacao_ausente(bs, e, l, s, r, pronta, aut):
  G.analisar_recusa_exatamente_autenticacao_ausente(bs, e, l, s, r, pronta, aut)

law reaplicar_analisar_pronta_publicavel_recusa_credencial_vazia:
  for +bs: List<&2, U32>
  for +e: D.Esquema
  for +l: S.Limites
  for +s: D.Estado
  for +r: P.Requisicao
  for pronta: {E.decodificar(bs, e, l) == E.Pronta{s, r} : E.PreAutenticacao}
  for estrutura: {D.estrutura(e, s) == True{} : Bool}
  for vazia: {I.credencial(r) == "" : String}
  {E.analisar(bs, e, l) == E.Rejeitada{S.Autenticacao{}} : E.Analise}
def reaplicar_analisar_pronta_publicavel_recusa_credencial_vazia(bs, e, l, s, r, pronta, estrutura, vazia):
  G.analisar_pronta_publicavel_recusa_credencial_vazia(bs, e, l, s, r, pronta, estrutura, vazia)
