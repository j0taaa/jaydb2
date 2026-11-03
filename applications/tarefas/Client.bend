import Base
import ./Dados.bend as D
import ./Semantica.bend as S

type Pedido is Data:
  Listar{}
  Ver{id: String}
  Salvar{id: String, titulo: String, concluida: Bool, cancelar: Bool}
  Remover{id: String}
  Concluir{id: String}
  Invalido{}

def com_id(+acao: String, +id: String) -> Pedido:
  Bool.pick(Pedido, String.eq(acao, "ver"), Ver{id},
    Bool.pick(Pedido, String.eq(acao, "remover"), Remover{id},
      Bool.pick(Pedido, String.eq(acao, "concluir"), Concluir{id}, Invalido{})))

def com_tarefa_casos(salvar: Bool, cancelar: Bool, id: String, titulo: String, concluida: Bool) -> Pedido:
  match salvar cancelar:
    case True{} _: Salvar{id, titulo, concluida, False{}}
    case False{} True{}: Salvar{id, titulo, concluida, True{}}
    case False{} False{}: Invalido{}

def com_tarefa(+acao: String, id: String, titulo: String, concluida: Bool) -> Pedido:
  com_tarefa_casos(String.eq(acao, "salvar"), String.eq(acao, "cancelar"), id, titulo, concluida)

def analisar(args: D.Valor) -> Pedido:
  match args:
    case D.VLista{D.VTexto{acao}, D.VListaVazia{}}:
      Bool.pick(Pedido, String.eq(acao, "listar"), Listar{}, Invalido{})
    case D.VLista{D.VTexto{acao}, D.VLista{D.VTexto{id}, D.VListaVazia{}}}:
      com_id(acao, id)
    case D.VLista{D.VTexto{acao}, D.VLista{D.VTexto{id}, D.VLista{D.VTexto{titulo}, D.VLista{D.VBool{feito}, D.VListaVazia{}}}}}:
      com_tarefa(acao, id, titulo, feito)
    case _: Invalido{}

def campos(+proprietario: String, +id: String, titulo: String, feita: Bool) -> List<&2, D.Campo>:
  [D.Campo{"concluida", D.VBool{feita}}, D.Campo{"id", D.VTexto{id}},
    D.Campo{"proprietario", D.VTexto{proprietario}}, D.Campo{"titulo", D.VTexto{titulo}}]

def chaves(xs: List<&2, String>) -> D.Valor:
  match xs:
    case Nil{}: D.VListaVazia{}
    case Con{k, resto}: D.VLista{D.VTexto{k}, chaves(resto)}

def lista_valor(r: S.Retorno) -> D.Valor:
  match r:
    case S.Dado{D.Chaves{ks}}: chaves(ks)
    case _: D.VAusente{}

def listado(r: S.Retorno) -> S.Acao:
  S.Terminar{lista_valor(r)}

def detalhe_valor(proprietario: String, id: String, titulo: String, r: S.Retorno) -> D.Valor:
  match r:
    case S.Dado{D.Celula{D.VBool{feita}}}:
      D.VRegistro{"concluida", D.VBool{feita},
        D.VRegistro{"id", D.VTexto{id}, D.VRegistro{"proprietario", D.VTexto{proprietario},
          D.VRegistro{"titulo", D.VTexto{titulo}, D.VRegistroVazio{}}}}}
    case _: D.VAusente{}

def detalhe(proprietario: String, id: String, titulo: String, r: S.Retorno) -> S.Acao:
  S.Terminar{detalhe_valor(proprietario, id, titulo, r)}

def texto_recebido(r: S.Retorno) -> Maybe<&2, String>:
  match r:
    case S.Dado{D.Celula{D.VTexto{titulo}}}: Some{titulo}
    case _: None{}

def continuar_titulo(+proprietario: String, +id: String, titulo: Maybe<&2, String>) -> S.Acao:
  match titulo:
    case Some{texto}:
      S.Acessar{D.LerCelula{D.Aplicacao{proprietario}, id, "concluida"}, detalhe(proprietario, id, texto)}
    case None{}: S.Terminar{D.VAusente{}}

def titulo_recebido(proprietario: String, id: String, r: S.Retorno) -> S.Acao:
  continuar_titulo(proprietario, id, texto_recebido(r))

def concluir_titulo(+proprietario: String, +id: String, titulo: Maybe<&2, String>) -> S.Acao:
  match titulo:
    case Some{texto}:
      S.Acessar{D.DefinirLinha{D.Aplicacao{proprietario}, id, campos(proprietario, id, texto, True{})},
        unidade => S.Terminar{D.VTexto{id}}}
    case None{}: S.Recusar{D.VTexto{"tarefa inexistente"}}

def concluir_recebido(proprietario: String, id: String, r: S.Retorno) -> S.Acao:
  concluir_titulo(proprietario, id, texto_recebido(r))

def salvo(cancelar: Bool, id: String) -> S.Acao:
  match cancelar:
    case False{}: S.Terminar{D.VTexto{id}}
    case True{}: S.Recusar{D.VTexto{"cancelado"}}

def pedido(+proprietario: String, p: Pedido) -> S.Acao:
  match p:
    case Listar{}:
      S.Acessar{D.EnumerarChaves{D.Aplicacao{proprietario}}, listado}
    case Ver{+id}:
      S.Acessar{D.LerCelula{D.Aplicacao{proprietario}, id, "titulo"}, titulo_recebido(proprietario, id)}
    case Salvar{+id, titulo, feita, cancelar}:
      S.Acessar{D.DefinirLinha{D.Aplicacao{proprietario}, id, campos(proprietario, id, titulo, feita)},
        unidade => salvo(cancelar, id)}
    case Concluir{+id}:
      S.Acessar{D.LerCelula{D.Aplicacao{proprietario}, id, "titulo"}, concluir_recebido(proprietario, id)}
    case Remover{+id}:
      S.Acessar{D.RemoverLinha{D.Aplicacao{proprietario}, id}, unidade => S.Terminar{D.VTexto{id}}}
    case Invalido{}: S.Recusar{D.VTexto{"pedido invalido"}}

def iniciar(ctx: D.Contexto, args: D.Valor) -> S.Acao:
  D.Contexto{id, tipo} = ctx
  pedido(id, analisar(args))

def programa() -> S.Programa:
  S.Programa{iniciar}
