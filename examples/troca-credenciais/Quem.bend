import Base
import ./Dados.bend as D
import ./Semantica.bend as S

def iniciar(ctx: D.Contexto, args: D.Valor) -> S.Acao:
  D.Contexto{id, tipo} = ctx
  S.Terminar{D.VTexto{id}}

def programa() -> S.Programa:
  S.Programa{iniciar}
