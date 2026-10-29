# Inversao da composicao REAL de Entrada, ligada a Interface original.
# Os erros carregam Unit; nenhuma conclusao sobre Pronta e pressuposta.
# Nao se instancia Ambiente, Acontece, Processavel ou Contrato.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Semantica.bend as S
import ../contrato/Requisitos.bend as R
import ../contrato/Recursos.bend as X
import ../contrato/Interface.bend as I
import ../contrato/Logica.bend as L
import ../src/Entrada.bend as E
import ../src/Estado.bend as Estado
import ../src/Requisicao.bend as Q
import ../src/Transporte.bend as T
import ../src/Codec.bend as C
import ./CodecLei2.bend as Codec
import ./CodecCompleto.bend as Completo
import ./Representacao.bend as V
import ./Transporte.bend as Transporte
import ./Fundamentos.bend as F

def ValorAceito(-bs: List<&2, U32>, -teto: B.Numero64, -v: D.Valor) -> Type:
  L.E<{C.decodificar(bs, teto) == C.Decodificado{v} : C.Resultado},
    L.E<P.Codificacao(v, bs), {D.valor_valido(v) == True{} : Bool}>>

def RequisicaoAceita(-br: List<&2, U32>, -tr: B.Numero64, -r: P.Requisicao) -> Type:
  ValorAceito(br, tr, P.requisicao_valor(r))

def EstadoAceito(-be: List<&2, U32>, -te: B.Numero64, -e: D.Esquema, -s: D.Estado) -> Type:
  &ve: D.Valor -> L.E<ValorAceito(be, te, ve),
    L.E<{Estado.decodificar(ve, e) == Some{s} : Maybe<&2, D.Estado>},
      {D.estrutura(e, s) == True{} : Bool}>>

# Todos os blocos, tetos e valores sao testemunhas extraidas da execucao.
# SeparacaoExata inclui remontagem do pacote ORIGINAL e octetos dos blocos.
def InversaoPronta(-bs: List<&2, U32>, -e: D.Esquema, -l: S.Limites,
  -s: D.Estado, -r: P.Requisicao) -> Type:
  &be: List<&2, U32> -> &br: List<&2, U32> -> &te: B.Numero64 -> &tr: B.Numero64 ->
    L.E<{T.separar(bs) == Some{T.Partes{be, br}} : Maybe<&2, T.Partes>},
      L.E<Transporte.SeparacaoExata(bs, T.Partes{be, br}),
        L.E<{B.nat64(R.limite_estado(l)) == Some{te} : Maybe<&2, B.Numero64>},
          L.E<{B.nat64(R.limite_mensagem(l)) == Some{tr} : Maybe<&2, B.Numero64>},
            L.E<EstadoAceito(be, te, e, s), RequisicaoAceita(br, tr, r)>>>>>

def MensagemFiel(pre: E.PreAutenticacao, -origem: D.Estado,
  -br: List<&2, U32>, -tr: B.Numero64) -> Type:
  match pre:
    case E.Pronta{s, r}:
      L.E<{s == origem : D.Estado}, RequisicaoAceita(br, tr, r)>
    case _:
      Unit

def LimiteMensagemFiel(pre: E.PreAutenticacao, -origem: D.Estado,
  -br: List<&2, U32>, -limite: Maybe<&2, B.Numero64>) -> Type:
  match pre:
    case E.Pronta{s, r}:
      &tr: B.Numero64 -> L.E<{limite == Some{tr} : Maybe<&2, B.Numero64>},
        MensagemFiel(E.Pronta{s, r}, origem, br, tr)>
    case _:
      Unit

def EstadoFiel(pre: E.PreAutenticacao, -be: List<&2, U32>, -te: B.Numero64,
  -e: D.Esquema, -br: List<&2, U32>, -limite: Maybe<&2, B.Numero64>) -> Type:
  match pre:
    case E.Pronta{s, r}:
      &tr: B.Numero64 -> L.E<{limite == Some{tr} : Maybe<&2, B.Numero64>},
        L.E<EstadoAceito(be, te, e, s), RequisicaoAceita(br, tr, r)>>
    case _:
      Unit

def LimiteEstadoFiel(pre: E.PreAutenticacao, -limite_estado: Maybe<&2, B.Numero64>,
  -be: List<&2, U32>, -e: D.Esquema, -br: List<&2, U32>,
  -limite_msg: Maybe<&2, B.Numero64>) -> Type:
  match pre:
    case E.Pronta{s, r}:
      &te: B.Numero64 -> L.E<{limite_estado == Some{te} : Maybe<&2, B.Numero64>},
        EstadoFiel(E.Pronta{s, r}, be, te, e, br, limite_msg)>
    case _:
      Unit

def ProntaRelacionada(pre: E.PreAutenticacao, -bs: List<&2, U32>,
  -e: D.Esquema, -l: S.Limites) -> Type:
  match pre:
    case E.Pronta{s, r}:
      InversaoPronta(bs, e, l, s, r)
    case _:
      Unit

def valor_aceito(+br: List<&2, U32>, +tr: B.Numero64, +v: D.Valor,
  +aceito: {C.decodificar(br, tr) == C.Decodificado{v} : C.Resultado}) -> ValorAceito(br, tr, v):
  L.Ambos{aceito, Codec.aceitacao_reconstitui_codificacao_original_e_validade(br, tr, v, aceito)}

def requisicao_do_valor_aceito(+br: List<&2, U32>, +tr: B.Numero64, +v: D.Valor,
  +r: P.Requisicao, aceito: {C.decodificar(br, tr) == C.Decodificado{v} : C.Resultado},
  extraido: {Q.extrair(v) == Some{r} : Maybe<&2, P.Requisicao>}) -> RequisicaoAceita(br, tr, r):
  F.com_par(RequisicaoAceita(br, tr, r), {D.valor_valido(v) == True{} : Bool},
    {v == P.requisicao_valor(r) : D.Valor}, V.extrair_preserva_valor_e_valida(v, r, extraido),
    valido => exato =>
      %exato : ValorAceito(br, tr, _)
      valor_aceito(br, tr, v, aceito))

def envelope_fiel(q: Maybe<&2, P.Requisicao>, +s: D.Estado,
  +br: List<&2, U32>, +tr: B.Numero64, +v: D.Valor,
  aceito: {C.decodificar(br, tr) == C.Decodificado{v} : C.Resultado},
  extraido: {Q.extrair(v) == q : Maybe<&2, P.Requisicao>}) ->
  MensagemFiel(E.envelope(q, s), s, br, tr):
  match q:
    case None{}:
      Unit{}
    case Some{+r}:
      L.Ambos{{==}, requisicao_do_valor_aceito(br, tr, v, r, aceito, extraido)}

def mensagem_fiel(resultado: C.Resultado, +s: D.Estado,
  +br: List<&2, U32>, +tr: B.Numero64,
  aceito: {C.decodificar(br, tr) == resultado : C.Resultado}) ->
  MensagemFiel(E.mensagem(resultado, s), s, br, tr):
  match resultado:
    case C.Entrada{}:
      Unit{}
    case C.Limite{}:
      Unit{}
    case C.Decodificado{+v}:
      envelope_fiel(Q.extrair(v), s, br, tr, v, aceito, {==})

def anexar_limite_mensagem(pre: E.PreAutenticacao, -s: D.Estado,
  -br: List<&2, U32>, +tr: B.Numero64, fiel: MensagemFiel(pre, s, br, tr)) ->
  LimiteMensagemFiel(pre, s, br, Some{tr}):
  match pre:
    case E.Pronta{estado, requisicao}:
      (tr, L.Ambos{{==}, fiel})
    case E.ErroMensagem{status}:
      Unit{}
    case E.ErroTransporte{}:
      Unit{}

def mensagem_cabe_fiel(cabe: Bool, +br: List<&2, U32>, +tr: B.Numero64, +s: D.Estado) ->
  LimiteMensagemFiel(E.mensagem_cabe(cabe, br, tr, s), s, br, Some{tr}):
  match cabe:
    case False{}:
      Unit{}
    case True{}:
      anexar_limite_mensagem(E.mensagem(C.decodificar(br, tr), s), s, br, tr,
        mensagem_fiel(C.decodificar(br, tr), s, br, tr, {==}))

def mensagem_medida_fiel(medida: Maybe<&2, B.Numero64>, +br: List<&2, U32>, +tr: B.Numero64, +s: D.Estado) ->
  LimiteMensagemFiel(E.mensagem_medida(medida, br, tr, s), s, br, Some{tr}):
  match medida:
    case None{}:
      Unit{}
    case Some{corpo}:
      mensagem_cabe_fiel(C.menor_igual64(corpo, tr), br, tr, s)

def ler_mensagem_fiel(limite: Maybe<&2, B.Numero64>, +br: List<&2, U32>, +s: D.Estado) ->
  LimiteMensagemFiel(E.ler_mensagem(limite, br, s), s, br, limite):
  match limite:
    case None{}:
      Unit{}
    case Some{+tr}:
      mensagem_medida_fiel(B.nat64(B.comprimento(br)), br, tr, s)

def ligar_estado_ao_corpo(pre: E.PreAutenticacao, +origem: D.Estado,
  +ve: D.Valor, +be: List<&2, U32>, +te: B.Numero64, +e: D.Esquema,
  -br: List<&2, U32>, -limite: Maybe<&2, B.Numero64>,
  aceito: {C.decodificar(be, te) == C.Decodificado{ve} : C.Resultado},
  +estado: {Estado.decodificar(ve, e) == Some{origem} : Maybe<&2, D.Estado>},
  mensagem: LimiteMensagemFiel(pre, origem, br, limite)) -> EstadoFiel(pre, be, te, e, br, limite):
  match pre:
    case E.Pronta{+s, r}:
      match mensagem:
        case (tr, L.Ambos{teto, L.Ambos{+igual, requisicao}}):
          (tr, L.Ambos{teto, L.Ambos{
            (ve, L.Ambos{valor_aceito(be, te, ve, aceito), L.Ambos{
              (%Equal.sym(D.Estado, s, origem, igual) :
                {Estado.decodificar(ve, e) == Some{_} : Maybe<&2, D.Estado>}
                estado),
              (%Equal.sym(D.Estado, s, origem, igual) : {D.estrutura(e, _) == True{} : Bool}
                V.transporte_privado_so_devolve_estado_estruturado(ve, e, origem, estado))}}),
            requisicao}})
    case E.ErroMensagem{status}:
      Unit{}
    case E.ErroTransporte{}:
      Unit{}

def estado_lido_fiel(q: Maybe<&2, D.Estado>, +ve: D.Valor,
  +be: List<&2, U32>, +te: B.Numero64, +e: D.Esquema,
  +br: List<&2, U32>, +limite: Maybe<&2, B.Numero64>,
  aceito: {C.decodificar(be, te) == C.Decodificado{ve} : C.Resultado},
  estado: {Estado.decodificar(ve, e) == q : Maybe<&2, D.Estado>}) ->
  EstadoFiel(E.estado_lido(q, br, limite), be, te, e, br, limite):
  match q:
    case None{}:
      Unit{}
    case Some{+s}:
      ligar_estado_ao_corpo(E.ler_mensagem(limite, br, s), s, ve, be, te, e, br, limite,
        aceito, estado, ler_mensagem_fiel(limite, br, s))

def estado_decodificado_fiel(resultado: C.Resultado, +be: List<&2, U32>, +te: B.Numero64,
  +e: D.Esquema, +br: List<&2, U32>, +limite: Maybe<&2, B.Numero64>,
  aceito: {C.decodificar(be, te) == resultado : C.Resultado}) ->
  EstadoFiel(E.estado_decodificado(resultado, e, br, limite), be, te, e, br, limite):
  match resultado:
    case C.Entrada{}:
      Unit{}
    case C.Limite{}:
      Unit{}
    case C.Decodificado{+ve}:
      estado_lido_fiel(Estado.decodificar(ve, e), ve, be, te, e, br, limite, aceito, {==})

def anexar_limite_estado(pre: E.PreAutenticacao, +te: B.Numero64,
  -be: List<&2, U32>, -e: D.Esquema, -br: List<&2, U32>, -limite: Maybe<&2, B.Numero64>,
  fiel: EstadoFiel(pre, be, te, e, br, limite)) ->
  LimiteEstadoFiel(pre, Some{te}, be, e, br, limite):
  match pre:
    case E.Pronta{estado, requisicao}:
      (te, L.Ambos{{==}, fiel})
    case E.ErroMensagem{status}:
      Unit{}
    case E.ErroTransporte{}:
      Unit{}

def ler_estado_fiel(limite_estado: Maybe<&2, B.Numero64>, +e: D.Esquema,
  +be: List<&2, U32>, +br: List<&2, U32>, +limite: Maybe<&2, B.Numero64>) ->
  LimiteEstadoFiel(E.ler_estado(limite_estado, e, be, br, limite), limite_estado, be, e, br, limite):
  match limite_estado:
    case None{}:
      Unit{}
    case Some{+te}:
      anexar_limite_estado(E.estado_decodificado(C.decodificar(be, te), e, br, limite), te,
        be, e, br, limite, estado_decodificado_fiel(C.decodificar(be, te), be, te, e, br, limite, {==}))

def ligar_blocos(pre: E.PreAutenticacao, +bs: List<&2, U32>, +be: List<&2, U32>,
  +br: List<&2, U32>, +e: D.Esquema, +l: S.Limites,
  +separado: {T.separar(bs) == Some{T.Partes{be, br}} : Maybe<&2, T.Partes>},
  leitura: LimiteEstadoFiel(pre, B.nat64(R.limite_estado(l)), be, e, br,
    B.nat64(R.limite_mensagem(l)))) -> ProntaRelacionada(pre, bs, e, l):
  match pre:
    case E.Pronta{s, r}:
      match leitura:
        case (te, L.Ambos{teto_e, (tr, L.Ambos{teto_r, L.Ambos{estado, requisicao}})}):
          (be, br, te, tr, L.Ambos{separado, L.Ambos{
            Transporte.toda_separacao_aceita_reconstroi_pacote_original(bs, T.Partes{be, br}, separado),
            L.Ambos{teto_e, L.Ambos{teto_r, L.Ambos{estado, requisicao}}}}})
    case E.ErroMensagem{status}:
      Unit{}
    case E.ErroTransporte{}:
      Unit{}

def partes_fieis(partes: Maybe<&2, T.Partes>, +bs: List<&2, U32>, +e: D.Esquema,
  +l: S.Limites, separado: {T.separar(bs) == partes : Maybe<&2, T.Partes>}) ->
  ProntaRelacionada(E.partes(partes, e, l), bs, e, l):
  match partes:
    case None{}:
      Unit{}
    case Some{T.Partes{+be, +br}}:
      ligar_blocos(E.ler_estado(B.nat64(R.limite_estado(l)), e, be, br,
        B.nat64(R.limite_mensagem(l))), bs, be, br, e, l, separado,
        ler_estado_fiel(B.nat64(R.limite_estado(l)), e, be, br, B.nat64(R.limite_mensagem(l))))

law decodificar_reconstroi_etapas_reais:
  for +bs: List<&2, U32>
  for +e: D.Esquema
  for +l: S.Limites
  ProntaRelacionada(E.decodificar(bs, e, l), bs, e, l)
def decodificar_reconstroi_etapas_reais(bs, e, l):
  partes_fieis(T.separar(bs), bs, e, l, {==})

# A unica hipotese operacional e o resultado efetivamente obtido.
law pronta_reconstroi_blocos_tetos_estado_e_requisicao:
  for +bs: List<&2, U32>
  for +e: D.Esquema
  for +l: S.Limites
  for -s: D.Estado
  for -r: P.Requisicao
  for pronta: {E.decodificar(bs, e, l) == E.Pronta{s, r} : E.PreAutenticacao}
  InversaoPronta(bs, e, l, s, r)
def pronta_reconstroi_blocos_tetos_estado_e_requisicao(bs, e, l, s, r, pronta):
  %pronta : ProntaRelacionada(_, bs, e, l)
  decodificar_reconstroi_etapas_reais(bs, e, l)

# O corpo e extraido da inversao, antes de receber a igualdade da recepcao.
# A funcao final recebe SOMENTE a decisao real ProcessarCorpo{br}.
def CorpoParaInterface(-bs: List<&2, U32>, -r: P.Requisicao,
  -mundo: Nat, -c: S.Configuracao, -s: D.Estado, -entrada: X.Recepcao) -> Type:
  &be: List<&2, U32> -> &br: List<&2, U32> ->
    L.E<{T.separar(bs) == Some{T.Partes{be, br}} : Maybe<&2, T.Partes>},
      L.E<P.Codificacao(P.requisicao_valor(r), br),
        ({X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{br} : X.Disposicao} ->
          I.RequisicaoRecebida(I.Atender{mundo, c, s, entrada}, r))>>

def ligar_inversao_a_interface(-bs: List<&2, U32>, -e: D.Esquema, -l: S.Limites,
  -s: D.Estado, +r: P.Requisicao, -mundo: Nat, -c: S.Configuracao, -entrada: X.Recepcao,
  inversao: InversaoPronta(bs, e, l, s, r)) -> CorpoParaInterface(bs, r, mundo, c, s, entrada):
  match inversao:
    case (+be, +br, te, tr, L.Ambos{separado, L.Ambos{transporte,
      L.Ambos{teto_e, L.Ambos{teto_r, L.Ambos{estado, L.Ambos{codec, L.Ambos{canonico, valido}}}}}}}):
      +codificacao = {canonico : {P.codificar(P.requisicao_valor(r)) == Some{br} : Maybe<&2, List<&2, U32>>}}
      (be, br, L.Ambos{separado, L.Ambos{codificacao,
        recepcao => (br, L.Ambos{recepcao, codificacao})}})

law pronta_fornece_corpo_e_ligacao_a_interface_original:
  for +bs: List<&2, U32>
  for +e: D.Esquema
  for +l: S.Limites
  for +s: D.Estado
  for +r: P.Requisicao
  for -mundo: Nat
  for -c: S.Configuracao
  for +entrada: X.Recepcao
  for pronta: {E.decodificar(bs, e, l) == E.Pronta{s, r} : E.PreAutenticacao}
  CorpoParaInterface(bs, r, mundo, c, s, entrada)
def pronta_fornece_corpo_e_ligacao_a_interface_original(bs, e, l, s, r, mundo, c, entrada, pronta):
  ligar_inversao_a_interface(bs, e, l, s, r, mundo, c, entrada,
    pronta_reconstroi_blocos_tetos_estado_e_requisicao(bs, e, l, s, r, pronta))

# Recusa do envelope: a completude impede que os MESMOS bytes sejam a
# codificacao de alguma requisicao. Medida e teto sao os reais do corpo.
def extracao_do_resultado(resultado: C.Resultado) -> Maybe<&2, P.Requisicao>:
  match resultado:
    case C.Decodificado{v}:
      Q.extrair(v)
    case _:
      None{}

def SemRequisicaoCodificada(-br: List<&2, U32>) -> Type:
  @r: P.Requisicao -> P.Codificacao(P.requisicao_valor(r), br) -> Empty

def excluir_requisicao_alternativa(+br: List<&2, U32>, +corpo: B.Numero64,
  +tr: B.Numero64, +v: D.Valor,
  +medido: {B.nat64(B.comprimento(br)) == Some{corpo} : Maybe<&2, B.Numero64>},
  +cabe: {C.menor_igual64(corpo, tr) == True{} : Bool},
  +aceito: {C.decodificar(br, tr) == C.Decodificado{v} : C.Resultado},
  +recusado: {Q.extrair(v) == None{} : Maybe<&2, P.Requisicao>},
  +r: P.Requisicao, codificado: P.Codificacao(P.requisicao_valor(r), br)) -> Empty:
  +decodificado = Completo.toda_codificacao_canonica_representavel_e_decodificada(
    P.requisicao_valor(r), br, corpo, tr, codificado, medido, cabe)
  F.com_par(Empty, P.Codificacao(P.requisicao_valor(r), br),
    {D.valor_valido(P.requisicao_valor(r)) == True{} : Bool},
    Codec.aceitacao_reconstitui_codificacao_original_e_validade(br, tr, P.requisicao_valor(r), decodificado),
    canonico => valido =>
      F.nenhum_nao_algum(P.Requisicao, r,
        Equal.trans(Maybe<&2, P.Requisicao>, None{}, Q.extrair(v), Some{r},
          Equal.sym(Maybe<&2, P.Requisicao>, Q.extrair(v), None{}, recusado),
          Equal.trans(Maybe<&2, P.Requisicao>, Q.extrair(v), Q.extrair(P.requisicao_valor(r)), Some{r},
            Equal.cong(C.Resultado, Maybe<&2, P.Requisicao>, extracao_do_resultado,
              C.Decodificado{v}, C.Decodificado{P.requisicao_valor(r)},
              Equal.trans(C.Resultado, C.Decodificado{v}, C.decodificar(br, tr),
                C.Decodificado{P.requisicao_valor(r)},
                Equal.sym(C.Resultado, C.decodificar(br, tr), C.Decodificado{v}, aceito), decodificado)),
            V.requisicao_valida_preserva_todos_os_campos(r, valido)))))

law codec_aceito_com_envelope_invalido_exclui_requisicao_canonica:
  for +br: List<&2, U32>
  for +corpo: B.Numero64
  for +tr: B.Numero64
  for +v: D.Valor
  for +medido: {B.nat64(B.comprimento(br)) == Some{corpo} : Maybe<&2, B.Numero64>}
  for +cabe: {C.menor_igual64(corpo, tr) == True{} : Bool}
  for +aceito: {C.decodificar(br, tr) == C.Decodificado{v} : C.Resultado}
  for +recusado: {Q.extrair(v) == None{} : Maybe<&2, P.Requisicao>}
  SemRequisicaoCodificada(br)
def codec_aceito_com_envelope_invalido_exclui_requisicao_canonica(br, corpo, tr, v, medido, cabe, aceito, recusado):
  r => codificado => excluir_requisicao_alternativa(br, corpo, tr, v, medido, cabe, aceito, recusado, r, codificado)

# A igualdade da disposicao e a unica premissa de recepcao; nao se recebe
# EntradaInvalida, Acontece ou uma relacao privada de fatos.
law envelope_invalido_do_corpo_real_implica_entrada_invalida_original:
  for -mundo: Nat
  for -c: S.Configuracao
  for -s: D.Estado
  for -entrada: X.Recepcao
  for +br: List<&2, U32>
  for +corpo: B.Numero64
  for +tr: B.Numero64
  for +v: D.Valor
  for recepcao: {X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{br} : X.Disposicao}
  for +teto: {B.nat64(R.limite_mensagem(S.limites(c))) == Some{tr} : Maybe<&2, B.Numero64>}
  for +medido: {B.nat64(B.comprimento(br)) == Some{corpo} : Maybe<&2, B.Numero64>}
  for +cabe: {C.menor_igual64(corpo, tr) == True{} : Bool}
  for +aceito: {C.decodificar(br, tr) == C.Decodificado{v} : C.Resultado}
  for +recusado: {Q.extrair(v) == None{} : Maybe<&2, P.Requisicao>}
  I.EntradaInvalida(I.Atender{mundo, c, s, entrada})
def envelope_invalido_do_corpo_real_implica_entrada_invalida_original(mundo, c, s, entrada,
  br, corpo, tr, v, recepcao, teto, medido, cabe, aceito, recusado):
  L.Direita{(br, L.Ambos{recepcao,
    codec_aceito_com_envelope_invalido_exclui_requisicao_canonica(br, corpo, tr, v, medido, cabe, aceito, recusado)})}
