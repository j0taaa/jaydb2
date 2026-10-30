# Invariante de estado por inducao nos resultados reais de N.concluir.
# Inclui stores seguidos de perda do processo, sem exigir resposta entregue.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Interface.bend as I
import ../contrato/Logica.bend as L
import ../contrato/Protocolo.bend as P
import ../contrato/Requisitos.bend as R
import ../contrato/Semantica.bend as S
import ../src/Nucleo.bend as N
import ./Publicacao.bend as U
import ./Preparacao.bend as Q

# Metadados sem estado privado na fonte do cliente. O historico e semantico,
# nao um log novo exigido do servidor.
type Registro is Data:
  Registro{requisicao: P.Requisicao, contexto: D.Contexto, passos: Nat,
    trabalho: D.Estado, eventos: List<&2, S.Evento>, proposta: S.Resposta,
    preparada: N.Preparada}

def seguinte(s: D.Estado, r: Registro) -> D.Estado:
  match r:
    case Registro{req, ctx, n, w, ts, prop, preparada}:
      U.publicado(N.concluir(preparada, s))

def estado(rs: List<&2, Registro>, s: D.Estado) -> D.Estado:
  match rs:
    case Nil{}: s
    case Con{h, t}: estado(t, seguinte(s, h))

# Origem guarda o certificado e IGUALDADES das funcoes, nao as conclusoes da Lei6.
def Origem(-c: S.Configuracao, -s: D.Estado, r: Registro) -> Type:
  match r:
    case Registro{req, ctx, n, w, ts, prop, preparada}:
      &p: S.Programa ->
        L.E<R.Certifica(c, I.codigo(req), p, ctx, I.argumentos(req)),
          L.E<{D.autenticar(s, I.credencial(req)) == Some{ctx} : Maybe<&2, D.Contexto>},
            L.E<{N.percorrer(n, N.iniciar(p, ctx, I.argumentos(req), s), S.esquema(c)) ==
              S.Final{w, ts, prop} : S.Percurso},
              {N.preparar(N.Parada{w, ts, prop}, c) == Some{preparada} : Maybe<&2, N.Preparada>}>>>

def Fontes(-c: S.Configuracao, rs: List<&2, Registro>, +s: D.Estado) -> Type:
  match rs:
    case Nil{}: Unit
    case Con{+h, t}: L.E<Origem(c, s, h), Fontes(c, t, seguinte(s, h))>

law passo_preserva_validade:
  for ~c: S.Configuracao
  for +s: D.Estado
  for +r: Registro
  for valido: R.Valido(c, s)
  for origem: Origem(c, s, r)
  R.Valido(c, seguinte(s, r))
def passo_preserva_validade(c, s, r, valido, origem):
  match r:
    case Registro{req, ctx, n, w, ts, prop, preparada}:
      match origem:
        case (p, L.Ambos{certificado, L.Ambos{aut, L.Ambos{obtido, obtida}}}):
          U.conclusao_de_preparacao_certificada_e_valida(c, I.codigo(req), p, ctx, I.argumentos(req),
            certificado, s, valido, I.credencial(req), aut, n, w, ts, prop, obtido, preparada,
            Q.preparar_preserva_resposta_estado_eventos_e_bytes(N.Parada{w, ts, prop}, c, preparada, obtida))

law historico_preserva_validade:
  for ~c: S.Configuracao
  for rs: List<&2, Registro>
  for +s: D.Estado
  for inicial: R.Valido(c, s)
  for fontes: Fontes(c, rs, s)
  R.Valido(c, estado(rs, s))
def historico_preserva_validade(c, rs, s, inicial, fontes):
  match rs fontes:
    case Nil{} _: inicial
    case Con{+h, t} L.Ambos{origem, resto}:
      historico_preserva_validade(c, t, seguinte(s, h),
        passo_preserva_validade(c, s, h, inicial, origem), resto)
