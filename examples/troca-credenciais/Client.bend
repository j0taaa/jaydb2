import Base
import ./Dados.bend as D
import ./Semantica.bend as S

type Credenciais is Data:
  Credenciais{alice: String, bob: String}

def argumentos(v: D.Valor) -> Credenciais:
  match v:
    case D.VLista{D.VTexto{a}, D.VLista{D.VTexto{b}, D.VListaVazia{}}}:
      Credenciais{a, b}
    case _:
      Credenciais{"bob-token", "alice-token"}

def responder(r: S.Retorno) -> S.Acao:
  match r:
    case S.Dado{D.Celula{valor}}:
      S.Terminar{valor}
    case _:
      S.Recusar{D.VAusente{}}

def ler(id: String) -> S.Acao:
  S.Acessar{D.LerCelula{D.Usuarios{}, id, "credencial"}, responder}

def escrever_bob(bob: String, id: String) -> S.Acao:
  S.Acessar{D.DefinirColuna{D.Usuarios{}, "bob", "credencial", D.VTexto{bob}},
    unidade => ler(id)}

def trocar(c: Credenciais, ctx: D.Contexto) -> S.Acao:
  Credenciais{alice, bob} = c
  D.Contexto{id, tipo} = ctx
  S.Acessar{D.DefinirColuna{D.Usuarios{}, "alice", "credencial", D.VTexto{alice}},
    unidade => escrever_bob(bob, id)}

def iniciar(ctx: D.Contexto, args: D.Valor) -> S.Acao:
  trocar(argumentos(args), ctx)

def programa() -> S.Programa:
  S.Programa{iniciar}
