import Base
import ./Dados.bend as D
import ./Semantica.bend as S

def responder(cancelar: Bool, r: S.Retorno) -> S.Acao:
  match cancelar:
    case True{}: S.Recusar{D.VTexto{"cancelado"}}
    case False{}:
      match r:
        case S.Dado{D.Celula{valor}}: S.Terminar{valor}
        case _: S.Recusar{D.VAusente{}}

def ler(id: String, cancelar: Bool) -> S.Acao:
  S.Acessar{D.LerCelula{D.Usuarios{}, id, "credencial"}, responder(cancelar)}

def escrever(+id: String, valor: String, cancelar: Bool) -> S.Acao:
  S.Acessar{D.DefinirColuna{D.Usuarios{}, id, "credencial", D.VTexto{valor}},
    unidade => ler(id, cancelar)}

def argumentos(id: String, args: D.Valor) -> S.Acao:
  match args:
    case D.VTexto{valor}: escrever(id, valor, False{})
    case _: escrever(id, "descartado", True{})

def iniciar(ctx: D.Contexto, args: D.Valor) -> S.Acao:
  D.Contexto{id, tipo} = ctx
  argumentos(id, args)

def programa() -> S.Programa:
  S.Programa{iniciar}
