# Interpretador incremental: cada avancar consome exatamente a acao corrente.
# O combustivel de percorrer e exclusivo da caracterizacao matematica;
# o servidor avanca a maquina sob os limites fisicos, sem reexecutar prefixos.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Semantica.bend as S
import ../contrato/Requisitos.bend as R
import ../contrato/Protocolo.bend as P

type Maquina is Type:
  EmCurso{trabalho: D.Estado, acao: S.Acao, eventos: List<&2, S.Evento>}
  Parada{trabalho: D.Estado, eventos: List<&2, S.Evento>, resposta: S.Resposta}

def iniciar(p: S.Programa, contexto: D.Contexto, argumentos: D.Valor,
  inicial: D.Estado) -> Maquina:
  EmCurso{inicial, S.iniciar(p, contexto, argumentos), Nil{}}

def passo_maquina(passo: S.Passo, eventos: List<&2, S.Evento>) -> Maquina:
  match passo:
    case S.Continua{w, a, evento}:
      EmCurso{w, a, S.acrescentar(eventos, evento)}
    case S.Parou{w, resposta}:
      Parada{w, eventos, resposta}
    case S.OperacaoFalhou{w, evento}:
      Parada{w, S.acrescentar(eventos, evento), S.resposta_erro(S.Dados{})}

def avancar(maquina: Maquina, esquema: D.Esquema) -> Maquina:
  match maquina:
    case EmCurso{w, a, eventos}:
      passo_maquina(S.passo(a, esquema, w), eventos)
    case Parada{w, eventos, resposta}:
      Parada{w, eventos, resposta}

def instantaneo(maquina: Maquina) -> S.Percurso:
  match maquina:
    case EmCurso{w, a, eventos}:
      S.Prefixo{w, eventos}
    case Parada{w, eventos, resposta}:
      S.Final{w, eventos, resposta}

def percorrer(n: Nat, maquina: Maquina, +esquema: D.Esquema) -> S.Percurso:
  match n:
    case 0n:
      instantaneo(maquina)
    case 1n+m:
      percorrer(m, avancar(maquina, esquema), esquema)

type Preparada is Data:
  Preparada{trabalho: D.Estado, eventos: List<&2, S.Evento>,
    resposta: S.Resposta, bytes: List<&2, U32>}

def preparar_bytes(resultado: Maybe<&2, List<&2, U32>>, trabalho: D.Estado,
  eventos: List<&2, S.Evento>, resposta: S.Resposta) -> Maybe<&2, Preparada>:
  match resultado:
    case None{}:
      None{}
    case Some{bytes}:
      Some{Preparada{trabalho, eventos, resposta, bytes}}

def preparar_resposta(+resposta: S.Resposta, trabalho: D.Estado,
  eventos: List<&2, S.Evento>) -> Maybe<&2, Preparada>:
  preparar_bytes(P.enquadrar(S.resposta_valor(resposta)), trabalho, eventos, resposta)

# Usa exclusivamente as condicoes tecnicas do contrato, nunca testa leis
# do administrador em tempo de execucao. As leis foram exigidas na admissao.
def preparar(maquina: Maquina, configuracao: S.Configuracao) -> Maybe<&2, Preparada>:
  match maquina:
    case EmCurso{w, a, eventos}:
      None{}
    case Parada{+w, eventos, proposta}:
      preparar_resposta(R.finalizar(proposta, configuracao, w), w, eventos)

type Conclusao is Data:
  Conclusao{publicado: D.Estado, resposta: S.Resposta, bytes: List<&2, U32>}

# O chamador so troca a raiz publicada depois que preparar retorna Some.
def concluir(preparada: Preparada, inicial: D.Estado) -> Conclusao:
  Preparada{w, eventos, +resposta, bytes} = preparada
  Conclusao{S.publica(resposta, inicial, w), resposta, bytes}

law recusa_descarta_estado_de_trabalho:
  for -w: D.Estado
  for -eventos: List<&2, S.Evento>
  for -v: D.Valor
  for -bytes: List<&2, U32>
  for -inicial: D.Estado
  {concluir(Preparada{w, eventos, S.Resposta{S.Recusa{}, v}, bytes}, inicial) ==
    Conclusao{inicial, S.Resposta{S.Recusa{}, v}, bytes} : Conclusao}
def recusa_descarta_estado_de_trabalho(w, eventos, v, bytes, inicial):
  {==}

law sucesso_publica_estado_inteiro:
  for -w: D.Estado
  for -eventos: List<&2, S.Evento>
  for -v: D.Valor
  for -bytes: List<&2, U32>
  for -inicial: D.Estado
  {concluir(Preparada{w, eventos, S.Resposta{S.Sucesso{}, v}, bytes}, inicial) ==
    Conclusao{w, S.Resposta{S.Sucesso{}, v}, bytes} : Conclusao}
def sucesso_publica_estado_inteiro(w, eventos, v, bytes, inicial):
  {==}

law inicio_usa_estado_e_argumentos_recebidos:
  for -p: S.Programa
  for -ctx: D.Contexto
  for -args: D.Valor
  for -s: D.Estado
  {instantaneo(iniciar(p, ctx, args, s)) == S.Prefixo{s, Nil{}} : S.Percurso}
def inicio_usa_estado_e_argumentos_recebidos(p, ctx, args, s):
  {==}

# O percurso matematico da maquina incremental coincide com a referencia.
# A prova nao recebe essa correspondencia como premissa.
law parada_absorve:
  for n: Nat
  for -w: D.Estado
  for -eventos: List<&2, S.Evento>
  for -resposta: S.Resposta
  for -esquema: D.Esquema
  {percorrer(n, Parada{w, eventos, resposta}, esquema) ==
    S.Final{w, eventos, resposta} : S.Percurso}
def parada_absorve(n, w, eventos, resposta, esquema):
  match n:
    case 0n:
      {==}
    case 1n+m:
      parada_absorve(m, w, eventos, resposta, esquema)

law passo_corresponde_a_referencia:
  for n: Nat
  for passo: S.Passo
  for +esquema: D.Esquema
  for eventos: List<&2, S.Evento>
  {percorrer(n, passo_maquina(passo, eventos), esquema) ==
    S.continuar_percurso(n, passo, esquema, eventos) : S.Percurso}
def passo_corresponde_a_referencia(n, passo, esquema, eventos):
  match n passo:
    case 0n S.Continua{w, a, evento}:
      {==}
    case 0n S.Parou{w, resposta}:
      {==}
    case 0n S.OperacaoFalhou{w, evento}:
      {==}
    case 1n+m S.Continua{w, a, evento}:
      passo_corresponde_a_referencia(m, S.passo(a, esquema, w), esquema,
        S.acrescentar(eventos, evento))
    case 1n+m S.Parou{w, resposta}:
      parada_absorve(1n+m, w, eventos, resposta, esquema)
    case 1n+m S.OperacaoFalhou{w, evento}:
      parada_absorve(1n+m, w, S.acrescentar(eventos, evento),
        S.resposta_erro(S.Dados{}), esquema)

law fidelidade_de_todos_os_prefixos:
  for n: Nat
  for programa: S.Programa
  for contexto: D.Contexto
  for argumentos: D.Valor
  for +esquema: D.Esquema
  for inicial: D.Estado
  {percorrer(n, iniciar(programa, contexto, argumentos, inicial), esquema) ==
    S.executar(n, programa, esquema, inicial, contexto, argumentos) : S.Percurso}
def fidelidade_de_todos_os_prefixos(n, programa, contexto, argumentos, esquema, inicial):
  match n:
    case 0n:
      {==}
    case 1n+m:
      passo_corresponde_a_referencia(m,
        S.passo(S.iniciar(programa, contexto, argumentos), esquema, inicial),
        esquema, Nil{})

law certificado_cobre_maquina_incremental:
  for configuracao: S.Configuracao
  for -codigo: String
  for programa: S.Programa
  for +contexto: D.Contexto
  for +argumentos: D.Valor
  for certificado: R.Certifica(configuracao, codigo, programa, contexto, argumentos)
  for +inicial: D.Estado
  for valido: R.Valido(configuracao, inicial)
  for identidade: {D.contexto_presente(inicial, contexto) == True{} : Bool}
  for +n: Nat
  R.SegurancaPercurso(
    percorrer(n, iniciar(programa, contexto, argumentos, inicial), S.esquema(configuracao)),
    configuracao, inicial, contexto, codigo, argumentos)
def certificado_cobre_maquina_incremental(configuracao, codigo, programa, contexto,
  argumentos, certificado, inicial, valido, identidade, n):
  %Equal.sym(S.Percurso,
    percorrer(n, iniciar(programa, contexto, argumentos, inicial), S.esquema(configuracao)),
    S.executar(n, programa, S.esquema(configuracao), inicial, contexto, argumentos),
    fidelidade_de_todos_os_prefixos(n, programa, contexto, argumentos,
      S.esquema(configuracao), inicial)) :
        R.SegurancaPercurso(_, configuracao, inicial, contexto, codigo, argumentos)
  certificado(inicial, valido, identidade, n)
