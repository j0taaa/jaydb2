# Composicao geral dos adaptadores REAIS. As hipoteses sao codificacao,
# medidas/limites efetivos e estrutura exigida pelo decoder de estado.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Semantica.bend as S
import ../contrato/Requisitos.bend as R
import ../contrato/Interface.bend as I
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ../src/Entrada.bend as E
import ../src/Estado.bend as Estado
import ../src/Requisicao.bend as Q
import ../src/Transporte.bend as T
import ./Representacao.bend as V
import ./Transporte.bend as Transporte
import ./CodecCompleto.bend as Completo
import ./CodecLei2.bend as Codec
import ./CodecOctetos.bend as Octetos
import ./Fundamentos.bend as F
import ./Autenticacao.bend as A
import ./EntradaMedida.bend as Medida

# Lema de composicao: nenhuma das hipoteses ja e a conclusao de Entrada.
law etapas_reais_produzem_pronta_exata:
  for +bs: List<&2, U32>
  for +be: List<&2, U32>
  for +br: List<&2, U32>
  for +e: D.Esquema
  for +l: S.Limites
  for +te: B.Numero64
  for +tr: B.Numero64
  for +ve: D.Valor
  for +vr: D.Valor
  for +s: D.Estado
  for +r: P.Requisicao
  for separado: {T.separar(bs) == Some{T.Partes{be, br}} : Maybe<&2, T.Partes>}
  for teto_e: {B.nat64(R.limite_estado(l)) == Some{te} : Maybe<&2, B.Numero64>}
  for teto_r: {B.nat64(R.limite_mensagem(l)) == Some{tr} : Maybe<&2, B.Numero64>}
  for estado_bytes: {C.decodificar(be, te) == C.Decodificado{ve} : C.Resultado}
  for estado_valor: {Estado.decodificar(ve, e) == Some{s} : Maybe<&2, D.Estado>}
  for +mensagem_bytes: {C.decodificar(br, tr) == C.Decodificado{vr} : C.Resultado}
  for envelope: {Q.extrair(vr) == Some{r} : Maybe<&2, P.Requisicao>}
  {E.decodificar(bs, e, l) == E.Pronta{s, r} : E.PreAutenticacao}
def etapas_reais_produzem_pronta_exata(bs, be, br, e, l, te, tr, ve, vr, s, r,
  separado, teto_e, teto_r, estado_bytes, estado_valor, mensagem_bytes, envelope):
  %Equal.sym(Maybe<&2, T.Partes>, T.separar(bs), Some{T.Partes{be, br}}, separado) :
    {E.partes(_, e, l) == E.Pronta{s, r} : E.PreAutenticacao}
  %Equal.sym(Maybe<&2, B.Numero64>, B.nat64(R.limite_estado(l)), Some{te}, teto_e) :
    {E.ler_estado(_, e, be, br, B.nat64(R.limite_mensagem(l))) == E.Pronta{s, r} : E.PreAutenticacao}
  %Equal.sym(C.Resultado, C.decodificar(be, te), C.Decodificado{ve}, estado_bytes) :
    {E.estado_decodificado(_, e, br, B.nat64(R.limite_mensagem(l))) == E.Pronta{s, r} : E.PreAutenticacao}
  %Equal.sym(Maybe<&2, D.Estado>, Estado.decodificar(ve, e), Some{s}, estado_valor) :
    {E.estado_lido(_, br, B.nat64(R.limite_mensagem(l))) == E.Pronta{s, r} : E.PreAutenticacao}
  %Equal.sym(Maybe<&2, B.Numero64>, B.nat64(R.limite_mensagem(l)), Some{tr}, teto_r) :
    {E.ler_mensagem(_, br, s) == E.Pronta{s, r} : E.PreAutenticacao}
  %Equal.sym(E.PreAutenticacao, E.ler_mensagem(Some{tr}, br, s), E.mensagem(C.decodificar(br, tr), s),
    Medida.decodificacao_aceita_preserva_mensagem(br, tr, s, vr, mensagem_bytes)) :
    {_ == E.Pronta{s, r} : E.PreAutenticacao}
  %Equal.sym(C.Resultado, C.decodificar(br, tr), C.Decodificado{vr}, mensagem_bytes) :
    {E.mensagem(_, s) == E.Pronta{s, r} : E.PreAutenticacao}
  %Equal.sym(Maybe<&2, P.Requisicao>, Q.extrair(vr), Some{r}, envelope) :
    {E.envelope(_, s) == E.Pronta{s, r} : E.PreAutenticacao}
  {==}

# Nenhuma premissa de sucesso de Codec, Entrada, autenticacao ou Contrato.
# Validade do envelope e dos octetos e DERIVADA da codificacao original.
law bytes_canonicos_montados_produzem_pronta_exata:
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
def bytes_canonicos_montados_produzem_pronta_exata(e, s, r, l, be, br, bs, ce, cr, te, tr,
  cod_e, cod_r, montagem, medida_e, medida_r, teto_e, teto_r, cabe_e, cabe_r, estrutura):
  +canon_e = {cod_e : {P.codificar(D.estado_valor(s)) == Some{be} : Maybe<&2, List<&2, U32>>}}
  +dec_r = Completo.toda_codificacao_canonica_representavel_e_decodificada(
    P.requisicao_valor(r), br, cr, tr, cod_r, medida_r, cabe_r)
  F.com_par({E.decodificar(bs, e, l) == E.Pronta{s, r} : E.PreAutenticacao},
    P.Codificacao(P.requisicao_valor(r), br), {D.valor_valido(P.requisicao_valor(r)) == True{} : Bool},
    Codec.aceitacao_reconstitui_codificacao_original_e_validade(br, tr, P.requisicao_valor(r), dec_r),
    canonica => valida => etapas_reais_produzem_pronta_exata(bs, be, br, e, l, te, tr,
      D.estado_valor(s), P.requisicao_valor(r), s, r,
      Transporte.separar_inverte_toda_montagem_valida(be, br, bs, montagem,
        Octetos.qualquer_codificacao_so_emite_octetos(D.estado_valor(s), be, canon_e),
        Octetos.qualquer_codificacao_so_emite_octetos(P.requisicao_valor(r), br, canonica)),
      teto_e, teto_r,
      Completo.toda_codificacao_canonica_representavel_e_decodificada(D.estado_valor(s), be, ce, te, canon_e, medida_e, cabe_e),
      V.transporte_privado_preserva_estado(e, s, estrutura), dec_r,
      V.requisicao_valida_preserva_todos_os_campos(r, valida)))

# A medida do estado ja basta para a montagem existir; nao ha nova quota
# sobre a soma privada header + estado + requisicao.
def MontagemExiste(-be: List<&2, U32>, -br: List<&2, U32>) -> Type:
  &bs: List<&2, U32> -> {T.juntar(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>}

law medida_do_estado_garante_montagem:
  for +be: List<&2, U32>
  for +br: List<&2, U32>
  for ce: B.Numero64
  for medida: {B.nat64(B.comprimento(be)) == Some{ce} : Maybe<&2, B.Numero64>}
  MontagemExiste(be, br)
def medida_do_estado_garante_montagem(be, br, ce, medida):
  match ce:
    case B.Numero64{alto, baixo}:
      (B.concatenar(B.be64(alto, baixo), B.concatenar(be, br)),
      (%Equal.sym(Maybe<&2, B.Numero64>, B.nat64(B.comprimento(be)), Some{B.Numero64{alto, baixo}}, medida) :
        {T.juntar_com_cabecalho(B.numero64_bytes(_), be, br) ==
          Some{B.concatenar(B.be64(alto, baixo), B.concatenar(be, br))} : Maybe<&2, List<&2, U32>>}
      {==}))

# Igualdade exata, para TODO estado/requisicao, inclusive estados de trabalho
# com credenciais temporarias. Nao exige estrutura/publicabilidade aqui.
law autenticar_preserva_exatamente_estado_requisicao_e_contexto:
  for +s: D.Estado
  for r: P.Requisicao
  {E.autenticar(Some{r}, s) == E.identidade(D.autenticar(s, I.credencial(r)), s, r) : E.Analise}
def autenticar_preserva_exatamente_estado_requisicao_e_contexto(s, r):
  match r:
    case P.Requisicao{cred, cod, args, pi}:
      {==}

law analisar_pronta_e_autenticacao_estavel_exata:
  for +bs: List<&2, U32>
  for +e: D.Esquema
  for +l: S.Limites
  for +s: D.Estado
  for +r: P.Requisicao
  for pronta: {E.decodificar(bs, e, l) == E.Pronta{s, r} : E.PreAutenticacao}
  {E.analisar(bs, e, l) == E.identidade(D.autenticar(s, I.credencial(r)), s, r) : E.Analise}
def analisar_pronta_e_autenticacao_estavel_exata(bs, e, l, s, r, pronta):
  %Equal.sym(E.PreAutenticacao, E.decodificar(bs, e, l), E.Pronta{s, r}, pronta) :
    {E.autenticar_pre(_) == E.identidade(D.autenticar(s, I.credencial(r)), s, r) : E.Analise}
  autenticar_preserva_exatamente_estado_requisicao_e_contexto(s, r)

law analisar_aceita_exatamente_contexto_autenticado:
  for +bs: List<&2, U32>
  for +e: D.Esquema
  for +l: S.Limites
  for +s: D.Estado
  for +r: P.Requisicao
  for +ctx: D.Contexto
  for pronta: {E.decodificar(bs, e, l) == E.Pronta{s, r} : E.PreAutenticacao}
  for aut: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>}
  {E.analisar(bs, e, l) == E.Recebida{s, r, ctx} : E.Analise}
def analisar_aceita_exatamente_contexto_autenticado(bs, e, l, s, r, ctx, pronta, aut):
  Equal.trans(E.Analise, E.analisar(bs, e, l), E.identidade(D.autenticar(s, I.credencial(r)), s, r),
    E.Recebida{s, r, ctx}, analisar_pronta_e_autenticacao_estavel_exata(bs, e, l, s, r, pronta),
    Equal.cong(Maybe<&2, D.Contexto>, E.Analise, q => E.identidade(q, s, r),
      D.autenticar(s, I.credencial(r)), Some{ctx}, aut))

law analisar_recusa_exatamente_autenticacao_ausente:
  for +bs: List<&2, U32>
  for +e: D.Esquema
  for +l: S.Limites
  for +s: D.Estado
  for +r: P.Requisicao
  for pronta: {E.decodificar(bs, e, l) == E.Pronta{s, r} : E.PreAutenticacao}
  for aut: {D.autenticar(s, I.credencial(r)) == None{} : Maybe<&2, D.Contexto>}
  {E.analisar(bs, e, l) == E.Rejeitada{S.Autenticacao{}} : E.Analise}
def analisar_recusa_exatamente_autenticacao_ausente(bs, e, l, s, r, pronta, aut):
  Equal.trans(E.Analise, E.analisar(bs, e, l), E.identidade(D.autenticar(s, I.credencial(r)), s, r),
    E.Rejeitada{S.Autenticacao{}}, analisar_pronta_e_autenticacao_estavel_exata(bs, e, l, s, r, pronta),
    Equal.cong(Maybe<&2, D.Contexto>, E.Analise, q => E.identidade(q, s, r),
      D.autenticar(s, I.credencial(r)), None{}, aut))

law analisar_pronta_publicavel_recusa_credencial_vazia:
  for +bs: List<&2, U32>
  for +e: D.Esquema
  for +l: S.Limites
  for +s: D.Estado
  for +r: P.Requisicao
  for pronta: {E.decodificar(bs, e, l) == E.Pronta{s, r} : E.PreAutenticacao}
  for estrutura: {D.estrutura(e, s) == True{} : Bool}
  for vazia: {I.credencial(r) == "" : String}
  {E.analisar(bs, e, l) == E.Rejeitada{S.Autenticacao{}} : E.Analise}
def analisar_pronta_publicavel_recusa_credencial_vazia(bs, e, l, s, r, pronta, estrutura, vazia):
  analisar_recusa_exatamente_autenticacao_ausente(bs, e, l, s, r, pronta,
    (%Equal.sym(String, I.credencial(r), "", vazia) :
      {D.autenticar(s, _) == None{} : Maybe<&2, D.Contexto>}
      A.estado_publicavel_nao_autentica_vazio(e, s, estrutura)))

# Composicao completa, sem receber Pronta ou analisar como hipotese.
law bytes_canonicos_montados_sao_analisados_com_identidade_exata:
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
def bytes_canonicos_montados_sao_analisados_com_identidade_exata(e, s, r, l, be, br, bs, ce, cr, te, tr,
  cod_e, cod_r, montagem, medida_e, medida_r, teto_e, teto_r, cabe_e, cabe_r, estrutura):
  +pronta = bytes_canonicos_montados_produzem_pronta_exata(e, s, r, l, be, br, bs, ce, cr, te, tr,
    cod_e, cod_r, montagem, medida_e, medida_r, teto_e, teto_r, cabe_e, cabe_r, estrutura)
  L.Ambos{pronta, analisar_pronta_e_autenticacao_estavel_exata(bs, e, l, s, r, pronta)}

# A montagem nao precisa ser presumida: a propria medida real fornece
# uma testemunha concreta de pacote, com Pronta e analisar exatos.
def PacotePronto(-e: D.Esquema, -s: D.Estado, -r: P.Requisicao,
  -l: S.Limites, -be: List<&2, U32>, -br: List<&2, U32>) -> Type:
  &bs: List<&2, U32> -> L.E<{T.juntar(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>},
    L.E<{E.decodificar(bs, e, l) == E.Pronta{s, r} : E.PreAutenticacao},
      {E.analisar(bs, e, l) == E.identidade(D.autenticar(s, I.credencial(r)), s, r) : E.Analise}>>


def construir_pacote_pronto(+e: D.Esquema, +s: D.Estado, +r: P.Requisicao,
  +l: S.Limites, +be: List<&2, U32>, +br: List<&2, U32>,
  +ce: B.Numero64, +cr: B.Numero64, +te: B.Numero64, +tr: B.Numero64,
  cod_e: P.Codificacao(D.estado_valor(s), be), cod_r: P.Codificacao(P.requisicao_valor(r), br),
  medida_e: {B.nat64(B.comprimento(be)) == Some{ce} : Maybe<&2, B.Numero64>},
  medida_r: {B.nat64(B.comprimento(br)) == Some{cr} : Maybe<&2, B.Numero64>},
  teto_e: {B.nat64(R.limite_estado(l)) == Some{te} : Maybe<&2, B.Numero64>},
  teto_r: {B.nat64(R.limite_mensagem(l)) == Some{tr} : Maybe<&2, B.Numero64>},
  cabe_e: {C.menor_igual64(ce, te) == True{} : Bool},
  cabe_r: {C.menor_igual64(cr, tr) == True{} : Bool},
  estrutura: {D.estrutura(e, s) == True{} : Bool},
  montada: MontagemExiste(be, br)) -> PacotePronto(e, s, r, l, be, br):
  match montada:
    case (+bs, montou):
      +montagem = {montou : {T.juntar(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>}}
      (bs, L.Ambos{montagem,
        bytes_canonicos_montados_sao_analisados_com_identidade_exata(e, s, r, l, be, br, bs, ce, cr, te, tr,
          cod_e, cod_r, montagem, medida_e, medida_r, teto_e, teto_r, cabe_e, cabe_r, estrutura)})

law toda_entrada_canonica_admissivel_tem_pacote_pronto_e_analise_exata:
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
  PacotePronto(e, s, r, l, be, br)
def toda_entrada_canonica_admissivel_tem_pacote_pronto_e_analise_exata(e, s, r, l, be, br, ce, cr, te, tr,
  cod_e, cod_r, medida_e, medida_r, teto_e, teto_r, cabe_e, cabe_r, estrutura):
  construir_pacote_pronto(e, s, r, l, be, br, ce, cr, te, tr,
    cod_e, cod_r, medida_e, medida_r, teto_e, teto_r, cabe_e, cabe_r, estrutura,
    medida_do_estado_garante_montagem(be, br, ce, medida_e))
