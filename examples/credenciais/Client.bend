import Base
import ./Dados.bend as D
import ./Semantica.bend as S

def token(args: D.Valor) -> D.Valor:
  match args:
    case D.VTexto{s}:
      D.VTexto{s}
    case _:
      D.VTexto{"nova"}

def responder(r: S.Retorno) -> S.Acao:
  match r:
    case S.Dado{D.Celula{valor}}:
      S.Terminar{valor}
    case _:
      S.Recusar{D.VAusente{}}

def ler(id: String) -> S.Acao:
  S.Acessar{D.LerCelula{D.Usuarios{}, id, "credencial"}, responder}

def escrever(+id: String, args: D.Valor) -> S.Acao:
  S.Acessar{D.DefinirColuna{D.Usuarios{}, id, "credencial", token(args)},
    unidade => ler(id)}

def iniciar(ctx: D.Contexto, args: D.Valor) -> S.Acao:
  D.Contexto{+id, tipo} = ctx
  S.Acessar{D.DefinirColuna{D.Usuarios{}, id, "credencial", D.VTexto{""}},
    unidade => escrever(id, args)}

def programa() -> S.Programa:
  S.Programa{iniciar}
