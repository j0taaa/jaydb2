# Proposta binaria real: sucesso e enquadravel quando o estado publicado e valido.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../contrato/Protocolo.bend as P
import ../contrato/Requisitos.bend as R
import ../contrato/Semantica.bend as S
import ../src/Nucleo.bend as N
import ../src/Execucao.bend as E
import ../src/Transporte.bend as T
import ./Fundamentos.bend as F
import ./Preparacao.bend as Q
import ./Chamada.bend as C
import ./CodecSomasOrdem.bend as O

def estado_representado(l: S.Limites, h: {R.limites_validos(l) == True{} : Bool}) ->
  O.NumeroRepresentado<B.nat64(R.limite_estado(l))>:
  match l:
    case S.Limites{+msg, +est, +resp}:
      +a = R.cabe_erro(resp, S.Entrada{})
      +b = R.cabe_erro(resp, S.Autenticacao{})
      +c = R.cabe_erro(resp, S.Certificado{})
      +d = R.cabe_erro(resp, S.Dados{})
      +e = R.cabe_erro(resp, S.Limite{})
      +f = R.cabe_erro(resp, S.Falha{})
      +prefixo = Q.prefixo_limites(msg, est, resp)
      h5 = F.e_booleano_esquerda(prefixo && a && b && c && d && e, f, h)
      h4 = F.e_booleano_esquerda(prefixo && a && b && c && d, e, h5)
      h3 = F.e_booleano_esquerda(prefixo && a && b && c, d, h4)
      h2 = F.e_booleano_esquerda(prefixo && a && b, c, h3)
      h1 = F.e_booleano_esquerda(prefixo && a, b, h2)
      C.representado(est, F.e_booleano_direita(P.representavel_resultado(B.comprimento64(msg)),
        P.representavel_resultado(B.comprimento64(est)),
        F.e_booleano_esquerda(
          P.representavel_resultado(B.comprimento64(msg)) && P.representavel_resultado(B.comprimento64(est)),
          P.representavel_resultado(B.comprimento64(resp)),
          F.e_booleano_esquerda(prefixo, a, h1))))

def juntar_medido(+bs: List<&2, U32>, +resp: List<&2, U32>,
  medida: O.NumeroRepresentado<B.nat64(B.comprimento(bs))>) ->
  &pacote: List<&2, U32> -> {T.juntar(bs, resp) == Some{pacote} : Maybe<&2, List<&2, U32>>}:
  match medida:
    case O.Representado{B.Numero64{+alto, +baixo}, medido}:
      (B.concatenar(B.be64(alto, baixo), B.concatenar(bs, resp)),
        (%Equal.sym(Maybe<&2, B.Numero64>, B.nat64(B.comprimento(bs)), Some{B.Numero64{alto, baixo}}, medido) :
          {T.juntar_com_cabecalho(B.numero64_bytes(_), bs, resp) ==
            Some{B.concatenar(B.be64(alto, baixo), B.concatenar(bs, resp))} : Maybe<&2, List<&2, U32>>}
          {==}))

def Montada(-q: Maybe<&2, List<&2, U32>>, -resp: List<&2, U32>) -> Type:
  &bs: List<&2, U32> -> &pacote: List<&2, U32> ->
    L.E<{q == Some{bs} : Maybe<&2, List<&2, U32>>},
      L.E<{T.juntar(bs, resp) == Some{pacote} : Maybe<&2, List<&2, U32>>},
        {E.estado_codificado(q, resp) == E.Encerrar{Con{1, pacote}} : E.Iteracao}>>

def sucesso_com_pacote(+resp: List<&2, U32>, +bs: List<&2, U32>,
  resultado: &pacote: List<&2, U32> -> {T.juntar(bs, resp) == Some{pacote} : Maybe<&2, List<&2, U32>>}) ->
  Montada(Some{bs}, resp):
  match resultado:
    case (+pacote, junto):
      F.com_par(Montada(Some{bs}, resp),
        {T.juntar(bs, resp) == Some{pacote} : Maybe<&2, List<&2, U32>>},
        {T.juntar(bs, resp) == Some{pacote} : Maybe<&2, List<&2, U32>>},
        C.duplicar_igualdade(Maybe<&2, List<&2, U32>>, T.juntar(bs, resp), Some{pacote}, junto),
        exato => encerrar => (bs, pacote, L.Ambos{{==}, L.Ambos{exato,
          Equal.cong(Maybe<&2, List<&2, U32>>, E.Iteracao, E.pacote_pronto,
            T.juntar(bs, resp), Some{pacote}, encerrar)}}))

def sucesso_codificado(q: Maybe<&2, List<&2, U32>>, +resp: List<&2, U32>, +limite: Nat,
  teto: O.NumeroRepresentado<B.nat64(limite)>,
  cabe: {R.cabe_resultado(q, limite) == True{} : Bool}) -> Montada(q, resp):
  match q:
    case None{}:
      F.absurdo_booleano(Montada(None{}, resp), cabe)
    case Some{+bs}:
      match teto:
        case O.Representado{numero, medido}:
          sucesso_com_pacote(resp, bs,
            juntar_medido(bs, resp, O.nat64_representabilidade_fechada_para_baixo(
              B.comprimento(bs), limite, numero, medido, cabe)))

law sucesso_valido_tem_proposta_real:
  for c: S.Configuracao
  for +estado: D.Estado
  for -valor: D.Valor
  for +resp: List<&2, U32>
  for configurada: {R.configuracao_valida(c) == True{} : Bool}
  for valido: R.Valido(c, estado)
  exs bs: List<&2, U32>
  exs pacote: List<&2, U32>
  L.E<{P.codificar(D.estado_valor(estado)) == Some{bs} : Maybe<&2, List<&2, U32>>},
    L.E<{T.juntar(bs, resp) == Some{pacote} : Maybe<&2, List<&2, U32>>},
      {E.concluir(N.Conclusao{estado, S.Resposta{S.Sucesso{}, valor}, resp}) == E.Encerrar{Con{1, pacote}} : E.Iteracao}>>
def sucesso_valido_tem_proposta_real(c, estado, valor, resp, configurada, valido):
  match c:
    case S.Configuracao{+e, leis, +lim, amb}:
      estrutura = L.e_esquerda({R.estrutura(S.Configuracao{e, leis, lim, amb}, estado) == True{} : Bool},
        S.Cumpre(S.Configuracao{e, leis, lim, amb}, S.Estavel{estado}), valido)
      sucesso_codificado(P.codificar(D.estado_valor(estado)), resp, R.limite_estado(lim),
        estado_representado(lim, Q.limites_da_configuracao(S.Configuracao{e, S.NenhumaLei{}, lim, amb}, configurada)),
        F.e_booleano_direita(D.estrutura(e, estado), R.cabe(R.limite_estado(lim), D.estado_valor(estado)), estrutura))

law sem_sucesso_nao_envia_estado:
  for -estado: D.Estado
  for r: S.Resposta
  for -resp: List<&2, U32>
  for sem_sucesso: {S.eh_sucesso(status(r)) == False{} : Bool}
  {E.concluir(N.Conclusao{estado, r, resp}) == E.Encerrar{Con{0, resp}} : E.Iteracao}

def status(r: S.Resposta) -> S.Status:
  S.Resposta{s, v} = r
  s

def sem_sucesso_nao_envia_estado(estado, r, resp, sem_sucesso):
  match r:
    case S.Resposta{S.Sucesso{}, v}:
      F.absurdo_booleano({E.concluir(N.Conclusao{estado, S.Resposta{S.Sucesso{}, v}, resp}) ==
        E.Encerrar{Con{0, resp}} : E.Iteracao}, Equal.sym(Bool, True{}, False{}, sem_sucesso))
    case S.Resposta{S.Recusa{}, v}: {==}
    case S.Resposta{S.Entrada{}, v}: {==}
    case S.Resposta{S.Autenticacao{}, v}: {==}
    case S.Resposta{S.Certificado{}, v}: {==}
    case S.Resposta{S.Dados{}, v}: {==}
    case S.Resposta{S.Limite{}, v}: {==}
    case S.Resposta{S.Falha{}, v}: {==}
