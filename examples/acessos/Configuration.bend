import Base
import ./Dados.bend as D
import ./Semantica.bend as S
import ./Environment.bend as E

type Ambos<-P: Data, -Q: Data> is Data:
  Ambos{esquerda: P, direita: Q}

# Cada leitura e escrita exige o id autenticado e a coluna autorizada.
def Permitida(ctx: D.Contexto, op: D.Operacao) -> Data:
  D.Contexto{id, tipo} = ctx
  match op:
    case D.LerCelula{D.Usuarios{}, chave, coluna}:
      Ambos<{chave == id : String}, {coluna == "credencial" : String}>
    case D.DefinirColuna{D.Usuarios{}, chave, coluna, valor}:
      Ambos<{chave == id : String}, {coluna == "credencial" : String}>
    case _:
      {False{} == True{} : Bool}

def Permitidos(ctx: D.Contexto, ts: List<&2, S.Evento>) -> Data:
  match ts:
    case Nil{}: Unit
    case Con{S.Evento{op, efeito}, resto}: Ambos<Permitida(ctx, op), Permitidos(ctx, resto)>

def Acessos(h: S.Situacao) -> Data:
  match h:
    case S.Estavel{s}: Unit
    case S.Executando{s, ctx, codigo, args, w, ts}: Permitidos(ctx, ts)
    case S.Encerrada{s, ctx, codigo, args, w, ts, resposta}: Permitidos(ctx, ts)

def esquema() -> D.Esquema:
  D.Esquema{Nil{}}

def limites() -> S.Limites:
  S.Limites{32768n, 65536n, 32768n}

def config() -> S.Configuracao:
  S.Configuracao{esquema(), S.MaisUmaLei{Acessos, S.NenhumaLei{}}, limites(), E.identidade()}
