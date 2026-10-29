# JayDB — semantica dos programas e das leis da aplicacao.
# O codigo submetido produz Acao; nunca recebe Estado.
# Os estados e eventos abaixo sao objetos da especificacao, nao um log publico.
import Base
import ./Dados.bend as D
import ./Logica.bend as L

type Retorno is Data:
  Dado{observacao: D.Observacao}
  Unidade{}

type Acao is Type:
  Terminar{valor: D.Valor}
  Recusar{valor: D.Valor}
  Acessar{operacao: D.Operacao, continuar: Retorno -> Acao}

type Programa is Type:
  Programa{iniciar: D.Contexto -> D.Valor -> Acao}

type Efeito is Data:
  Leitura{observacao: D.Observacao}
  Escrita{}
  ErroDeDados{}

type Evento is Data:
  Evento{operacao: D.Operacao, efeito: Efeito}

type Status is Data:
  Entrada{}
  Autenticacao{}
  Certificado{}
  Dados{}
  Limite{}
  Falha{}
  Recusa{}
  Sucesso{}

type Resposta is Data:
  Resposta{status: Status, valor: D.Valor}

type Situacao is Data:
  Estavel{estado: D.Estado}
  Executando{inicial: D.Estado, contexto: D.Contexto, codigo: String,
    argumentos: D.Valor, trabalho: D.Estado, eventos: List<&2, Evento>}
  Encerrada{inicial: D.Estado, contexto: D.Contexto, codigo: String,
    argumentos: D.Valor, trabalho: D.Estado, eventos: List<&2, Evento>, resposta: Resposta}

type Leis is Type:
  NenhumaLei{}
  MaisUmaLei{lei: Situacao -> Type, restantes: Leis}

def Todas(leis: Leis, +h: Situacao) -> Type:
  match leis:
    case NenhumaLei{}:
      Unit
    case MaisUmaLei{lei, resto}:
      L.E<lei(h), Todas(resto, h)>

# Tamanhos e memoria em bytes; tempos em nanossegundos inteiros.
# Medicoes fisicas pertencem ao ambiente, nao ao programa do solicitante.
type Limites is Data:
  Limites{mensagem: Nat, estado: Nat, resposta: Nat,
    memoria: Nat, enquadramento: Nat, autenticacao: Nat,
    verificacao: Nat, execucao: Nat, preparacao: Nat}

type Configuracao is Type:
  Configuracao{esquema: D.Esquema, leis: Leis, limites: Limites,
    ambiente: String}

def esquema(c: Configuracao) -> D.Esquema:
  Configuracao{e, ls, lim, amb} = c
  e

def limites(c: Configuracao) -> Limites:
  Configuracao{e, ls, lim, amb} = c
  lim

def ambiente(c: Configuracao) -> String:
  Configuracao{e, ls, lim, amb} = c
  amb

def Cumpre(c: Configuracao, h: Situacao) -> Type:
  Configuracao{e, ls, lim, amb} = c
  Todas(ls, h)

def iniciar(p: Programa, c: D.Contexto, a: D.Valor) -> Acao:
  Programa{f} = p
  f(c, a)

def acrescentar(xs: List<&2, Evento>, e: Evento) -> List<&2, Evento>:
  match xs:
    case Nil{}:
      [e]
    case Con{h, t}:
      h <> acrescentar(t, e)

type Passo is Type:
  Continua{estado: D.Estado, acao: Acao, evento: Evento}
  Parou{estado: D.Estado, resposta: Resposta}
  OperacaoFalhou{estado: D.Estado, evento: Evento}

def aplicar(r: D.ResultadoOp, s: D.Estado, o: D.Operacao,
  k: Retorno -> Acao) -> Passo:
  match r:
    case D.FalhaDados{}:
      OperacaoFalhou{s, Evento{o, ErroDeDados{}}}
    case D.Observado{+v}:
      Continua{s, k(Dado{v}), Evento{o, Leitura{v}}}
    case D.Alterado{w}:
      Continua{w, k(Unidade{}), Evento{o, Escrita{}}}

def passo(a: Acao, e: D.Esquema, +s: D.Estado) -> Passo:
  match a:
    case Terminar{v}:
      Parou{s, Resposta{Sucesso{}, v}}
    case Recusar{v}:
      Parou{s, Resposta{Recusa{}, v}}
    case Acessar{+o, k}:
      aplicar(D.operar(e, s, o), s, o, k)

type Percurso is Data:
  Prefixo{trabalho: D.Estado, eventos: List<&2, Evento>}
  Final{trabalho: D.Estado, eventos: List<&2, Evento>, resposta: Resposta}

# n enumera prefixos matematicos. NAO e um limite de execucao novo.
# O tempo e a memoria continuam sendo medidos pelo ambiente real.
def continuar_percurso(n: Nat, p: Passo, +e: D.Esquema,
  ts: List<&2, Evento>) -> Percurso:
  match n p:
    case 0n Continua{s, a, ev}:
      Prefixo{s, acrescentar(ts, ev)}
    case 0n Parou{s, r}:
      Final{s, ts, r}
    case 0n OperacaoFalhou{s, ev}:
      Final{s, acrescentar(ts, ev), Resposta{Dados{}, D.VAusente{}}}
    case 1n+m Continua{s, a, ev}:
      continuar_percurso(m, passo(a, e, s), e, acrescentar(ts, ev))
    case 1n+m Parou{s, r}:
      Final{s, ts, r}
    case 1n+m OperacaoFalhou{s, ev}:
      Final{s, acrescentar(ts, ev), Resposta{Dados{}, D.VAusente{}}}

def observar(n: Nat, a: Acao, +e: D.Esquema, +s: D.Estado) -> Percurso:
  match n:
    case 0n:
      Prefixo{s, Nil{}}
    case 1n+m:
      continuar_percurso(m, passo(a, e, s), e, Nil{})

def executar(n: Nat, p: Programa, e: D.Esquema, s: D.Estado,
  c: D.Contexto, a: D.Valor) -> Percurso:
  observar(n, iniciar(p, c, a), e, s)

def estado_percurso(p: Percurso) -> D.Estado:
  match p:
    case Prefixo{s, t}:
      s
    case Final{s, t, r}:
      s

def eventos_percurso(p: Percurso) -> List<&2, Evento>:
  match p:
    case Prefixo{s, t}:
      t
    case Final{s, t, r}:
      t

def status_nome(s: Status) -> String:
  match s:
    case Entrada{}:
      "entrada"
    case Autenticacao{}:
      "autenticacao"
    case Certificado{}:
      "certificado"
    case Dados{}:
      "dados"
    case Limite{}:
      "limite"
    case Falha{}:
      "falha"
    case Recusa{}:
      "recusa"
    case Sucesso{}:
      "sucesso"

def resposta_valor(r: Resposta) -> D.Valor:
  Resposta{s, v} = r
  D.VRegistro{"status", D.VTexto{status_nome(s)},
    D.VRegistro{"valor", v, D.VRegistroVazio{}}}

def resposta_erro(s: Status) -> Resposta:
  Resposta{s, D.VAusente{}}

def eh_sucesso(s: Status) -> Bool:
  match s:
    case Sucesso{}:
      True{}
    case _:
      False{}

def publica(r: Resposta, inicial: D.Estado, trabalho: D.Estado) -> D.Estado:
  match r:
    case Resposta{Sucesso{}, v}:
      trabalho
    case _:
      inicial

# Lemas do modelo: provas completas, independentes de uma implementacao nativa.
law prefixo_inicial:
  for -p: Programa
  for -e: D.Esquema
  for -s: D.Estado
  for -c: D.Contexto
  for -a: D.Valor
  {executar(0n, p, e, s, c, a) == Prefixo{s, Nil{}} : Percurso}

def prefixo_inicial(p, e, s, c, a):
  {==}

law recusa_preserva_publicado:
  for -v: D.Valor
  for -s: D.Estado
  for -w: D.Estado
  {publica(Resposta{Recusa{}, v}, s, w) == s : D.Estado}

def recusa_preserva_publicado(v, s, w):
  {==}

law sucesso_publica_trabalho:
  for -v: D.Valor
  for -s: D.Estado
  for -w: D.Estado
  {publica(Resposta{Sucesso{}, v}, s, w) == w : D.Estado}

def sucesso_publica_trabalho(v, s, w):
  {==}

law escrita_nao_entrega_estado:
  for -s: D.Estado
  for -w: D.Estado
  for -o: D.Operacao
  for -k: Retorno -> Acao
  {aplicar(D.Alterado{w}, s, o, k) ==
    Continua{w, k(Unidade{}), Evento{o, Escrita{}}} : Passo}

def escrita_nao_entrega_estado(s, w, o, k):
  {==}

law erro_de_operacao_preserva_trabalho:
  for -s: D.Estado
  for -o: D.Operacao
  for -k: Retorno -> Acao
  {aplicar(D.FalhaDados{}, s, o, k) ==
    OperacaoFalhou{s, Evento{o, ErroDeDados{}}} : Passo}

def erro_de_operacao_preserva_trabalho(s, o, k):
  {==}
