# Ordem do nucleo: decodificar mensagem, autenticar, depois admitir codigo.
# O estado entra apenas pelo transporte privado, nunca pelos argumentos cliente.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Semantica.bend as S
import ../contrato/Requisitos.bend as R
import ./Codec.bend as C
import ./Requisicao.bend as Q
import ./Estado.bend as E
import ./Transporte.bend as T

type Analise is Data:
  Recebida{estado: D.Estado, requisicao: P.Requisicao, contexto: D.Contexto}
  Rejeitada{status: S.Status}
  TransporteInvalido{}

def identidade(ctx: Maybe<&2, D.Contexto>, estado: D.Estado,
  requisicao: P.Requisicao) -> Analise:
  match ctx:
    case None{}:
      Rejeitada{S.Autenticacao{}}
    case Some{c}:
      Recebida{estado, requisicao, c}

def autenticar(requisicao: Maybe<&2, P.Requisicao>, +estado: D.Estado) -> Analise:
  match requisicao:
    case None{}:
      Rejeitada{S.Entrada{}}
    case Some{P.Requisicao{+credencial, codigo, argumentos, prova}}:
      identidade(D.autenticar(estado, credencial), estado,
        P.Requisicao{credencial, codigo, argumentos, prova})

type PreAutenticacao is Data:
  Pronta{estado: D.Estado, requisicao: P.Requisicao}
  ErroMensagem{status: S.Status}
  ErroTransporte{}

def envelope(requisicao: Maybe<&2, P.Requisicao>, estado: D.Estado) -> PreAutenticacao:
  match requisicao:
    case None{}:
      ErroMensagem{S.Entrada{}}
    case Some{r}:
      Pronta{estado, r}

def mensagem(resultado: C.Resultado, estado: D.Estado) -> PreAutenticacao:
  match resultado:
    case C.Entrada{}:
      ErroMensagem{S.Entrada{}}
    case C.Limite{}:
      ErroMensagem{S.Entrada{}}
    case C.Decodificado{v}:
      envelope(Q.extrair(v), estado)

# S.Limite depende da quantidade REAL recebida, nunca de um comprimento
# interno declarado pelo cliente. Apos esta conferencia, Limite do codec
# significa corpo malformado e mensagem o classifica como Entrada.
def mensagem_cabe(cabe: Bool, bytes: List<&2, U32>, limite: B.Numero64,
  estado: D.Estado) -> PreAutenticacao:
  match cabe:
    case False{}:
      ErroMensagem{S.Limite{}}
    case True{}:
      mensagem(C.decodificar(bytes, limite), estado)

def mensagem_medida(medida: Maybe<&2, B.Numero64>, bytes: List<&2, U32>,
  +limite: B.Numero64, estado: D.Estado) -> PreAutenticacao:
  match medida:
    case None{}:
      ErroMensagem{S.Limite{}}
    case Some{corpo}:
      mensagem_cabe(C.menor_igual64(corpo, limite), bytes, limite, estado)

def ler_mensagem(limite: Maybe<&2, B.Numero64>, +bytes: List<&2, U32>,
  estado: D.Estado) -> PreAutenticacao:
  match limite:
    case None{}:
      ErroTransporte{}
    case Some{n}:
      mensagem_medida(B.nat64(B.comprimento(bytes)), bytes, n, estado)

def estado_lido(estado: Maybe<&2, D.Estado>, corpo: List<&2, U32>,
  limite: Maybe<&2, B.Numero64>) -> PreAutenticacao:
  match estado:
    case None{}:
      ErroTransporte{}
    case Some{s}:
      ler_mensagem(limite, corpo, s)

def estado_decodificado(resultado: C.Resultado, esquema: D.Esquema,
  corpo: List<&2, U32>, limite: Maybe<&2, B.Numero64>) -> PreAutenticacao:
  match resultado:
    case C.Decodificado{v}:
      estado_lido(E.decodificar(v, esquema), corpo, limite)
    case _:
      ErroTransporte{}

def ler_estado(limite_estado: Maybe<&2, B.Numero64>, esquema: D.Esquema,
  estado: List<&2, U32>, corpo: List<&2, U32>, limite_msg: Maybe<&2, B.Numero64>) -> PreAutenticacao:
  match limite_estado:
    case None{}:
      ErroTransporte{}
    case Some{n}:
      estado_decodificado(C.decodificar(estado, n), esquema, corpo, limite_msg)

def partes(partes: Maybe<&2, T.Partes>, esquema: D.Esquema, +limites: S.Limites) -> PreAutenticacao:
  match partes:
    case None{}:
      ErroTransporte{}
    case Some{T.Partes{estado, corpo}}:
      ler_estado(B.nat64(R.limite_estado(limites)), esquema, estado, corpo,
        B.nat64(R.limite_mensagem(limites)))

def decodificar(bytes: List<&2, U32>, esquema: D.Esquema, limites: S.Limites) -> PreAutenticacao:
  partes(T.separar(bytes), esquema, limites)

def autenticar_pre(entrada: PreAutenticacao) -> Analise:
  match entrada:
    case Pronta{estado, requisicao}:
      autenticar(Some{requisicao}, estado)
    case ErroMensagem{status}:
      Rejeitada{status}
    case ErroTransporte{}:
      TransporteInvalido{}

def analisar(bytes: List<&2, U32>, esquema: D.Esquema, limites: S.Limites) -> Analise:
  autenticar_pre(decodificar(bytes, esquema, limites))
