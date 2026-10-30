# Uma inversao do mesmo sufixo, compartilhada pelas Leis6/7.
import Base
import ./PrimitivasServico.bend as M
import ./Lei5Servico.bend as Cinco
import ./Publicacao.bend as U
import ../contrato/Recursos.bend as X
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../contrato/Semantica.bend as S
import ../contrato/Protocolo.bend as P
import ../src/Nucleo.bend as N
import ./ProtocoloServico.bend as Q
import ./RotasServico.bend as R
import ./FasesServico.bend as Fases
import ./ErrosFixos.bend as Erros
import ./FonteServico.bend as Fonte
import ./ExecucaoServico.bend as Exec
import ./Fundamentos.bend as F

type Fecho is Data:
  Fecho{antes: List<&2, Q.Quadro>, conclusao: N.Conclusao, fecha: Bool,
    entrega: R.Entrega, origem: R.Caso}

def erro(q: Maybe<&2, List<&2, U32>>, antes: List<&2, Q.Quadro>, s: D.Estado,
  e: Erros.Erro, fecha: Bool, entrega: R.Entrega, origem: R.Caso) -> Maybe<&2, Fecho>:
  match q:
    case None{}: None{}
    case Some{bs}: Some{Fecho{antes, N.Conclusao{s, S.resposta_erro(Erros.status(e)), bs}, fecha, entrega, origem}}

def fechar_erro(antes: List<&2, Q.Quadro>, s: D.Estado, +e: Erros.Erro,
  fecha: Bool, entrega: R.Entrega, origem: R.Caso) -> Maybe<&2, Fecho>:
  erro(P.enquadrar(S.resposta_valor(S.resposta_erro(Erros.status(e)))), antes, s, e, fecha, entrega, origem)

def erro_da_entrada(e: R.ErroEntrada) -> Erros.Erro:
  match e:
    case R.Entrada{}: Erros.Entrada{}
    case R.Limite{}: Erros.Limite{}

def antes_autenticacao(+m: R.Micro, +r: P.Requisicao) -> List<&2, Q.Quadro>:
  Q.concatenar(R.render_recebida(m, r), Q.concatenar(R.micro_autenticacao(m), [Q.Autenticada{r, None{}}]))

def antes_gate(m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto) -> List<&2, Q.Quadro>:
  Q.concatenar(R.render_autenticada(m, r, ctx), [Q.Rejeitada{r, ctx}])

def antes_execucao(+m: R.Micro, r: P.Requisicao, ctx: D.Contexto,
  xs: List<&2, Q.QuadroExec>) -> List<&2, Q.Quadro>:
  Q.concatenar(R.render_execucao(m, r, ctx, xs), R.micro_saida(m))

def antes_falha(m: R.Micro, fase: R.FaseAntes, etapa: X.Etapa, id: String, fatal: Bool) -> List<&2, Q.Quadro>:
  Q.concatenar(R.render_fase(m, fase), [Q.Falhou{etapa, id, fatal}])


def do_caso(+m: R.Micro, +s: D.Estado, caso: R.Caso) -> Maybe<&2, Fecho>:
  match caso:
    case R.EntradaRecusa{+e, +fecha, +entrega}:
      fechar_erro(R.micro_entrada(m), s, erro_da_entrada(e), fecha, entrega, R.EntradaRecusa{e, fecha, entrega})
    case R.AutRecusa{+r, +entrega}:
      fechar_erro(antes_autenticacao(m, r), s, Erros.Autenticacao{}, False{}, entrega, R.AutRecusa{r, entrega})
    case R.GateRecusa{+r, +ctx, +entrega}:
      fechar_erro(antes_gate(m, r, ctx), s, Erros.Certificado{}, False{}, entrega, R.GateRecusa{r, ctx, entrega})
    case R.Executada{+r, +ctx, +xs, +p, +entrega}:
      Some{Fecho{antes_execucao(m, r, ctx, xs), N.concluir(p, s), False{}, entrega, R.Executada{r, ctx, xs, p, entrega}}}
    case R.FalhaAntes{+fase, +etapa, +id, fatal, +entrega}:
      match fatal:
        case True{}: None{}
        case False{}:
          fechar_erro(antes_falha(m, fase, etapa, id, False{}), s, Erros.Falha{}, False{}, entrega,
            R.FalhaAntes{fase, etapa, id, False{}, entrega})
    case _: None{}

def configurar(q: Maybe<&2, Fecho>) -> Maybe<&2, Fecho>:
  match q:
    case None{}: None{}
    case Some{Fecho{antes, c, fecha, entrega, origem}}:
      Some{Fecho{Con{Q.Configurada{}, antes}, c, fecha, entrega, origem}}

def fecho_do_caso(m: R.Micro, s: D.Estado, caso: R.Caso) -> Maybe<&2, Fecho>:
  configurar(do_caso(m, s, caso))

# Ausencia de conclusao so quando nenhum sufixo desse tipo foi executado.
# Nao afirma ausencia de preparacoes anteriores a uma falha de cleanup.
def Forma(-xs: List<&2, Q.Quadro>, -caso: R.Caso, q: Maybe<&2, Fecho>) -> Type:
  match q:
    case None{}: {Fases.ausente(Fases.Conclusao{}, xs) == True{} : Bool}
    case Some{Fecho{antes, c, fecha, entrega, origem}}:
      L.E<{origem == caso : R.Caso},
        L.E<{xs == Q.concatenar(antes, R.render_conclusao(c, fecha, entrega)) : List<&2, Q.Quadro>},
          L.E<{Fases.ausente(Fases.Publicacao{}, antes) == True{} : Bool},
            {Fases.ausente(Fases.Conclusao{}, antes) == True{} : Bool}>>>

def erro_igual_conclusao(+e: Erros.Erro, s: D.Estado, bs: List<&2, U32>, fecha: Bool, entrega: R.Entrega) ->
  {R.render_erro_enquadrado(Some{bs}, S.resposta_erro(Erros.status(e)), s, fecha, entrega) ==
    R.render_conclusao(N.Conclusao{s, S.resposta_erro(Erros.status(e)), bs}, fecha, entrega) : List<&2, Q.Quadro>}:
  match e:
    case Erros.Entrada{}: {==}
    case Erros.Autenticacao{}: {==}
    case Erros.Certificado{}: {==}
    case Erros.Dados{}: {==}
    case Erros.Limite{}: {==}
    case Erros.Falha{}: {==}

def forma_erro(q: Maybe<&2, List<&2, U32>>, +antes: List<&2, Q.Quadro>, +s: D.Estado,
  +e: Erros.Erro, +fecha: Bool, +entrega: R.Entrega, +origem: R.Caso,
  pub: {Fases.ausente(Fases.Publicacao{}, antes) == True{} : Bool},
  concl: {Fases.ausente(Fases.Conclusao{}, antes) == True{} : Bool}) ->
  Forma(Q.concatenar(antes, R.render_erro_enquadrado(q, S.resposta_erro(Erros.status(e)), s, fecha, entrega)),
    origem, erro(q, antes, s, e, fecha, entrega, origem)):
  match q:
    case None{}:
      Fases.concatenar_ausencia(Fases.Conclusao{}, antes, Nil{}, concl, {==})
    case Some{+bs}: L.Ambos{{==}, L.Ambos{
      Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, tail => Q.concatenar(antes, tail),
        R.render_erro_enquadrado(Some{bs}, S.resposta_erro(Erros.status(e)), s, fecha, entrega),
        R.render_conclusao(N.Conclusao{s, S.resposta_erro(Erros.status(e)), bs}, fecha, entrega),
        erro_igual_conclusao(e, s, bs, fecha, entrega)), L.Ambos{pub, concl}}}

def forma_do_erro(+antes: List<&2, Q.Quadro>, +s: D.Estado, +e: Erros.Erro,
  +fecha: Bool, +entrega: R.Entrega, +origem: R.Caso,
  pub: {Fases.ausente(Fases.Publicacao{}, antes) == True{} : Bool},
  concl: {Fases.ausente(Fases.Conclusao{}, antes) == True{} : Bool}) ->
  Forma(Q.concatenar(antes, R.render_erro(Erros.status(e), s, fecha, entrega)), origem,
    fechar_erro(antes, s, e, fecha, entrega, origem)):
  forma_erro(P.enquadrar(S.resposta_valor(S.resposta_erro(Erros.status(e)))), antes, s, e, fecha, entrega, origem, pub, concl)

def trocar_forma(-xs: List<&2, Q.Quadro>, -ys: List<&2, Q.Quadro>, -caso: R.Caso,
  -fecho: Maybe<&2, Fecho>, igual: {xs == ys : List<&2, Q.Quadro>}, forma: Forma(xs, caso, fecho)) -> Forma(ys, caso, fecho):
  %igual : Forma(_, caso, fecho)
  forma

def agrupar_tres(+a: List<&2, Q.Quadro>, +b: List<&2, Q.Quadro>, +c: List<&2, Q.Quadro>, +d: List<&2, Q.Quadro>) ->
  {Q.concatenar(Q.concatenar(a, Q.concatenar(b, c)), d) == Q.concatenar(a, Q.concatenar(b, Q.concatenar(c, d))) : List<&2, Q.Quadro>}:
  Equal.trans(List<&2, Q.Quadro>, Q.concatenar(Q.concatenar(a, Q.concatenar(b, c)), d),
    Q.concatenar(a, Q.concatenar(Q.concatenar(b, c), d)), Q.concatenar(a, Q.concatenar(b, Q.concatenar(c, d))),
    Q.concatenar_assoc(a, Q.concatenar(b, c), d),
    Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, tail => Q.concatenar(a, tail),
      Q.concatenar(Q.concatenar(b, c), d), Q.concatenar(b, Q.concatenar(c, d)), Q.concatenar_assoc(b, c, d)))

def antes_autenticacao_sem_macros(+tipo: Fases.Tipo, +m: R.Micro, +r: P.Requisicao) ->
  {Fases.ausente(tipo, antes_autenticacao(m, r)) == True{} : Bool}:
  Fases.concatenar_ausencia(tipo, R.render_recebida(m, r), Q.concatenar(R.micro_autenticacao(m), [Q.Autenticada{r, None{}}]),
    Fases.recebida_sem_macros(tipo, m, r),
    Fases.concatenar_ausencia(tipo, R.micro_autenticacao(m), [Q.Autenticada{r, None{}}],
      Fases.micro_autenticacao_sem_macros(tipo, m), {==}))

def antes_gate_sem_macros(+tipo: Fases.Tipo, +m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto) ->
  {Fases.ausente(tipo, antes_gate(m, r, ctx)) == True{} : Bool}:
  Fases.concatenar_ausencia(tipo, R.render_autenticada(m, r, ctx), [Q.Rejeitada{r, ctx}],
    Fases.autenticada_sem_macros(tipo, m, r, ctx), {==})

def antes_execucao_sem_macros(+tipo: Fases.Tipo, +m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto,
  +xs: List<&2, Q.QuadroExec>) -> {Fases.ausente(tipo, antes_execucao(m, r, ctx, xs)) == True{} : Bool}:
  Fases.concatenar_ausencia(tipo, R.render_execucao(m, r, ctx, xs), R.micro_saida(m),
    Fases.execucao_host_sem_macros(tipo, m, r, ctx, xs), Fases.micro_saida_sem_macros(tipo, m))

def antes_falha_sem_macros(+tipo: Fases.Tipo, +m: R.Micro, +fase: R.FaseAntes,
  +etapa: X.Etapa, +id: String, +fatal: Bool) ->
  {Fases.ausente(tipo, antes_falha(m, fase, etapa, id, fatal)) == True{} : Bool}:
  Fases.concatenar_ausencia(tipo, R.render_fase(m, fase), [Q.Falhou{etapa, id, fatal}],
    Fases.fase_anterior_sem_macros(tipo, m, fase), {==})

def inicial_sem_conclusao(q: Maybe<&2, List<&2, U32>>, s: D.Estado) ->
  {Fases.ausente(Fases.Conclusao{}, R.render_inicial(q, s)) == True{} : Bool}:
  match q:
    case None{}: {==}
    case Some{bs}: {==}

def prefixo_inicial_sem_conclusao(+m: R.Micro, aceita: Bool) ->
  {Fases.ausente(Fases.Conclusao{}, R.prefixo_inicial(m, aceita)) == True{} : Bool}:
  match aceita:
    case False{}: {==}
    case True{}: Fases.micro_saida_sem_macros(Fases.Conclusao{}, m)

def fatal_sem_conclusao(conclusao: N.Conclusao, etapa: X.Etapa, id: String) ->
  {Fases.ausente(Fases.Conclusao{}, R.render_fatal_publicada(conclusao, etapa, id)) == True{} : Bool}:
  match conclusao:
    case N.Conclusao{+s, +r, bs}:
      Fases.concatenar_ausencia(Fases.Conclusao{}, R.render_publicacao(r, s), [Q.Falhou{etapa, id, True{}}, Q.Fechada{}],
        Fases.publicacao_nao_conclui(r, s), {==})

def forma_do_caso(+m: R.Micro, +s: D.Estado, caso: R.Caso) -> Forma(R.render_caso(m, s, caso), caso, do_caso(m, s, caso)):
  match caso:
    case R.InicialOk{}:
      Fases.concatenar_ausencia(Fases.Conclusao{}, R.micro_saida(m), R.render_inicial(P.codificar(D.estado_valor(s)), s),
        Fases.micro_saida_sem_macros(Fases.Conclusao{}, m), inicial_sem_conclusao(P.codificar(D.estado_valor(s)), s))
    case R.InicialRecusa{status}: {==}
    case R.InicialFalha{+aceita, +etapa, +id, +fatal}:
      Fases.concatenar_ausencia(Fases.Conclusao{}, R.prefixo_inicial(m, aceita),
        [Q.Falhou{etapa, id, fatal}, Q.InicialRecusada{S.Falha{}}], prefixo_inicial_sem_conclusao(m, aceita), {==})
    case R.SemResposta{}: {==}
    case R.EntradaRecusa{e, +fecha, +entrega}:
      match e:
        case R.Entrada{}:
          forma_do_erro(R.micro_entrada(m), s, Erros.Entrada{}, fecha, entrega, R.EntradaRecusa{R.Entrada{}, fecha, entrega},
            Fases.micro_entrada_sem_macros(Fases.Publicacao{}, m), Fases.micro_entrada_sem_macros(Fases.Conclusao{}, m))
        case R.Limite{}:
          forma_do_erro(R.micro_entrada(m), s, Erros.Limite{}, fecha, entrega, R.EntradaRecusa{R.Limite{}, fecha, entrega},
            Fases.micro_entrada_sem_macros(Fases.Publicacao{}, m), Fases.micro_entrada_sem_macros(Fases.Conclusao{}, m))
    case R.AutRecusa{+r, +entrega}:
      trocar_forma(Q.concatenar(antes_autenticacao(m, r), R.render_erro(S.Autenticacao{}, s, False{}, entrega)),
        R.render_caso(m, s, R.AutRecusa{r, entrega}), R.AutRecusa{r, entrega}, do_caso(m, s, R.AutRecusa{r, entrega}),
        agrupar_tres(R.render_recebida(m, r), R.micro_autenticacao(m), [Q.Autenticada{r, None{}}], R.render_erro(S.Autenticacao{}, s, False{}, entrega)),
        forma_do_erro(antes_autenticacao(m, r), s, Erros.Autenticacao{}, False{}, entrega, R.AutRecusa{r, entrega},
          antes_autenticacao_sem_macros(Fases.Publicacao{}, m, r), antes_autenticacao_sem_macros(Fases.Conclusao{}, m, r)))
    case R.GateRecusa{+r, +ctx, +entrega}:
      trocar_forma(Q.concatenar(antes_gate(m, r, ctx), R.render_erro(S.Certificado{}, s, False{}, entrega)),
        R.render_caso(m, s, R.GateRecusa{r, ctx, entrega}), R.GateRecusa{r, ctx, entrega}, do_caso(m, s, R.GateRecusa{r, ctx, entrega}),
        Q.concatenar_assoc(R.render_autenticada(m, r, ctx), [Q.Rejeitada{r, ctx}], R.render_erro(S.Certificado{}, s, False{}, entrega)),
        forma_do_erro(antes_gate(m, r, ctx), s, Erros.Certificado{}, False{}, entrega, R.GateRecusa{r, ctx, entrega},
          antes_gate_sem_macros(Fases.Publicacao{}, m, r, ctx), antes_gate_sem_macros(Fases.Conclusao{}, m, r, ctx)))
    case R.Executada{+r, +ctx, +xs, +p, +entrega}:
      L.Ambos{{==}, L.Ambos{
        Equal.sym(List<&2, Q.Quadro>, Q.concatenar(antes_execucao(m, r, ctx, xs), R.render_final(p, s, False{}, entrega)),
          R.render_caso(m, s, R.Executada{r, ctx, xs, p, entrega}),
          Q.concatenar_assoc(R.render_execucao(m, r, ctx, xs), R.micro_saida(m), R.render_final(p, s, False{}, entrega))),
        L.Ambos{antes_execucao_sem_macros(Fases.Publicacao{}, m, r, ctx, xs),
          antes_execucao_sem_macros(Fases.Conclusao{}, m, r, ctx, xs)}}}
    case R.FalhaAntes{+fase, +etapa, +id, fatal, +entrega}:
      match fatal:
        case True{}:
          Fases.concatenar_ausencia(Fases.Conclusao{}, R.render_fase(m, fase),
            R.render_falha(s, etapa, id, True{}, entrega), Fases.fase_anterior_sem_macros(Fases.Conclusao{}, m, fase), {==})
        case False{}:
          trocar_forma(Q.concatenar(antes_falha(m, fase, etapa, id, False{}), R.render_erro(S.Falha{}, s, False{}, entrega)),
            R.render_caso(m, s, R.FalhaAntes{fase, etapa, id, False{}, entrega}), R.FalhaAntes{fase, etapa, id, False{}, entrega},
            do_caso(m, s, R.FalhaAntes{fase, etapa, id, False{}, entrega}),
            Q.concatenar_assoc(R.render_fase(m, fase), [Q.Falhou{etapa, id, False{}}], R.render_erro(S.Falha{}, s, False{}, entrega)),
            forma_do_erro(antes_falha(m, fase, etapa, id, False{}), s, Erros.Falha{}, False{}, entrega,
              R.FalhaAntes{fase, etapa, id, False{}, entrega}, antes_falha_sem_macros(Fases.Publicacao{}, m, fase, etapa, id, False{}),
              antes_falha_sem_macros(Fases.Conclusao{}, m, fase, etapa, id, False{})))
    case R.FatalAposPublicacao{+r, +ctx, +xs, +p, +etapa, +id}:
      Fases.concatenar_ausencia(Fases.Conclusao{}, R.render_execucao(m, r, ctx, xs),
        Q.concatenar(R.micro_saida(m), R.render_fatal_publicada(N.concluir(p, s), etapa, id)),
        Fases.execucao_host_sem_macros(Fases.Conclusao{}, m, r, ctx, xs),
        Fases.concatenar_ausencia(Fases.Conclusao{}, R.micro_saida(m), R.render_fatal_publicada(N.concluir(p, s), etapa, id),
          Fases.micro_saida_sem_macros(Fases.Conclusao{}, m), fatal_sem_conclusao(N.concluir(p, s), etapa, id)))
    case R.Pendente{fase}: Fases.fase_anterior_sem_macros(Fases.Conclusao{}, m, fase)
    case R.InicialPendente{aceita}: prefixo_inicial_sem_conclusao(m, aceita)

def configurar_forma(+xs: List<&2, Q.Quadro>, +caso: R.Caso, q: Maybe<&2, Fecho>, forma: Forma(xs, caso, q)) ->
  Forma(Con{Q.Configurada{}, xs}, caso, configurar(q)):
  match q:
    case None{}: forma
    case Some{Fecho{+antes, +c, +fecha, +entrega, +origem}}:
      match forma:
        case L.Ambos{igual, L.Ambos{traco, L.Ambos{pub, concl}}}:
          L.Ambos{igual, L.Ambos{
            Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, tail => Con{Q.Configurada{}, tail},
              xs, Q.concatenar(antes, R.render_conclusao(c, fecha, entrega)), traco), L.Ambos{pub, concl}}}

law forma_da_rota:
  for +m: R.Micro
  for +s: D.Estado
  for +caso: R.Caso
  Forma(R.render(m, s, caso), caso, fecho_do_caso(m, s, caso))
def forma_da_rota(m, s, caso):
  configurar_forma(R.render_caso(m, s, caso), caso, do_caso(m, s, caso), forma_do_caso(m, s, caso))

# A consulta real impede escolher o ramo sem conclusao.
def encontrar_fecho(+xs: List<&2, Q.Quadro>, +caso: R.Caso, q: Maybe<&2, Fecho>,
  +t: Nat, +r: S.Resposta, +s: D.Estado, +fecha: Bool, forma: Forma(xs, caso, q),
  consulta: {Q.consultar(xs, t) == Some{Q.Concluida{r, s, fecha}} : Maybe<&2, Q.Quadro>}) ->
  &fecho: Fecho -> Forma(xs, caso, Some{fecho}):
  match q:
    case None{}:
      L.ex_falso((&fecho: Fecho -> Forma(xs, caso, Some{fecho})),
        Fases.ausente_exclui_consulta(Fases.Conclusao{}, xs, t, Q.Concluida{r, s, fecha}, forma, {==}, consulta))
    case Some{+fecho}: (fecho, forma)

law inverter_conclusao:
  for +m: R.Micro
  for +s: D.Estado
  for +caso: R.Caso
  for +t: Nat
  for +r: S.Resposta
  for +w: D.Estado
  for +fecha: Bool
  for consulta: {Q.consultar(R.render(m, s, caso), t) == Some{Q.Concluida{r, w, fecha}} : Maybe<&2, Q.Quadro>}
  exs fecho: Fecho
  Forma(R.render(m, s, caso), caso, Some{fecho})
def inverter_conclusao(m, s, caso, t, r, w, fecha, consulta):
  encontrar_fecho(R.render(m, s, caso), caso, fecho_do_caso(m, s, caso), t, r, w, fecha,
    forma_da_rota(m, s, caso), consulta)

# Esta e uma conclusao das funcoes N.concluir/render_erro, nunca premissa de rollback.
def ConservaInicial(-s: D.Estado, c: N.Conclusao) -> Type:
  match c:
    case N.Conclusao{w, r, bs}:
      {U.status_sucesso(r) == False{} : Bool} -> {w == s : D.Estado}

def EstadoDoFecho(-s: D.Estado, q: Maybe<&2, Fecho>) -> Type:
  match q:
    case None{}: Unit
    case Some{Fecho{antes, c, fecha, entrega, origem}}: ConservaInicial(s, c)

def estado_do_erro(q: Maybe<&2, List<&2, U32>>, +antes: List<&2, Q.Quadro>, +s: D.Estado,
  +e: Erros.Erro, +fecha: Bool, +entrega: R.Entrega, +origem: R.Caso) ->
  EstadoDoFecho(s, erro(q, antes, s, e, fecha, entrega, origem)):
  match q:
    case None{}: Unit{}
    case Some{bs}: sem_sucesso => {==}

def estado_da_conclusao(s: D.Estado, p: N.Preparada) -> ConservaInicial(s, N.concluir(p, s)):
  match p:
    case N.Preparada{+w, eventos, +r, bs}:
      sem_sucesso => U.todo_status_sem_sucesso_preserva_publicado(r, s, w, sem_sucesso)

def estado_do_caso(+m: R.Micro, +s: D.Estado, caso: R.Caso) -> EstadoDoFecho(s, do_caso(m, s, caso)):
  match caso:
    case R.EntradaRecusa{+e, +fecha, +entrega}:
      estado_do_erro(P.enquadrar(S.resposta_valor(S.resposta_erro(Erros.status(erro_da_entrada(e))))),
        R.micro_entrada(m), s, erro_da_entrada(e), fecha, entrega, R.EntradaRecusa{e, fecha, entrega})
    case R.AutRecusa{+r, +entrega}:
      estado_do_erro(P.enquadrar(S.resposta_valor(S.resposta_erro(S.Autenticacao{}))),
        antes_autenticacao(m, r), s, Erros.Autenticacao{}, False{}, entrega, R.AutRecusa{r, entrega})
    case R.GateRecusa{+r, +ctx, +entrega}:
      estado_do_erro(P.enquadrar(S.resposta_valor(S.resposta_erro(S.Certificado{}))),
        antes_gate(m, r, ctx), s, Erros.Certificado{}, False{}, entrega, R.GateRecusa{r, ctx, entrega})
    case R.Executada{r, ctx, xs, p, entrega}: estado_da_conclusao(s, p)
    case R.FalhaAntes{+fase, +etapa, +id, fatal, +entrega}:
      match fatal:
        case True{}: Unit{}
        case False{}:
          estado_do_erro(P.enquadrar(S.resposta_valor(S.resposta_erro(S.Falha{}))),
            antes_falha(m, fase, etapa, id, False{}), s, Erros.Falha{}, False{}, entrega, R.FalhaAntes{fase, etapa, id, False{}, entrega})
    case R.InicialOk{}: Unit{}
    case R.InicialRecusa{status}: Unit{}
    case R.InicialFalha{aceita, etapa, id, fatal}: Unit{}
    case R.SemResposta{}: Unit{}
    case R.FatalAposPublicacao{r, ctx, xs, p, etapa, id}: Unit{}
    case R.Pendente{fase}: Unit{}
    case R.InicialPendente{aceita}: Unit{}

def configurar_estado(-s: D.Estado, q: Maybe<&2, Fecho>, estado: EstadoDoFecho(s, q)) -> EstadoDoFecho(s, configurar(q)):
  match q:
    case None{}: Unit{}
    case Some{Fecho{antes, c, fecha, entrega, origem}}: estado

law estado_da_rota:
  for +m: R.Micro
  for +s: D.Estado
  for +caso: R.Caso
  EstadoDoFecho(s, fecho_do_caso(m, s, caso))
def estado_da_rota(m, s, caso):
  configurar_estado(s, do_caso(m, s, caso), estado_do_caso(m, s, caso))

def encontrar_fecho_com_estado(+xs: List<&2, Q.Quadro>, +caso: R.Caso, +inicial: D.Estado,
  q: Maybe<&2, Fecho>, +t: Nat, +r: S.Resposta, +s: D.Estado, +fecha: Bool,
  forma: Forma(xs, caso, q), estado: EstadoDoFecho(inicial, q),
  consulta: {Q.consultar(xs, t) == Some{Q.Concluida{r, s, fecha}} : Maybe<&2, Q.Quadro>}) ->
  &fecho: Fecho -> L.E<Forma(xs, caso, Some{fecho}), EstadoDoFecho(inicial, Some{fecho})>:
  match q:
    case None{}:
      L.ex_falso((&fecho: Fecho -> L.E<Forma(xs, caso, Some{fecho}), EstadoDoFecho(inicial, Some{fecho})>),
        Fases.ausente_exclui_consulta(Fases.Conclusao{}, xs, t, Q.Concluida{r, s, fecha}, forma, {==}, consulta))
    case Some{+fecho}: (fecho, L.Ambos{forma, estado})

law inverter_conclusao_com_estado:
  for +m: R.Micro
  for +s: D.Estado
  for +caso: R.Caso
  for +t: Nat
  for +r: S.Resposta
  for +w: D.Estado
  for +fecha: Bool
  for consulta: {Q.consultar(R.render(m, s, caso), t) == Some{Q.Concluida{r, w, fecha}} : Maybe<&2, Q.Quadro>}
  exs fecho: Fecho
  L.E<Forma(R.render(m, s, caso), caso, Some{fecho}), EstadoDoFecho(s, Some{fecho})>
def inverter_conclusao_com_estado(m, s, caso, t, r, w, fecha, consulta):
  encontrar_fecho_com_estado(R.render(m, s, caso), caso, s, fecho_do_caso(m, s, caso), t, r, w, fecha,
    forma_da_rota(m, s, caso), estado_da_rota(m, s, caso), consulta)

def eh_seguinte(q: Q.Quadro) -> Bool:
  match q:
    case Q.Seguinte{a, b}: True{}
    case _: False{}

def sem_seguinte_na_frente(+h: Q.Quadro, -xs: List<&2, Q.Quadro>, -a: D.Estado, -b: D.Estado,
  neutra: {eh_seguinte(h) == False{} : Bool}, resto: Cinco.SemQuadro(xs, Q.Seguinte{a, b})) ->
  Cinco.SemQuadro(Con{h, xs}, Q.Seguinte{a, b}):
  Cinco.cabeca_por_tag(eh_seguinte, h, Q.Seguinte{a, b}, xs, neutra, {==}, resto)

def sem_seguinte_vazio(-a: D.Estado, -b: D.Estado) -> Cinco.SemQuadro(Nil{}, Q.Seguinte{a, b}):
  t => h => F.nenhum_nao_algum(Q.Quadro, Q.Seguinte{a, b}, h)


# Todo prefixo calculado anterior ao fecho exclui a proxima chamada.
def SemSeguinte(-xs: List<&2, Q.Quadro>) -> Type:
  @a: D.Estado -> @b: D.Estado -> Cinco.SemQuadro(xs, Q.Seguinte{a, b})

def vazio_sem_seguinte() -> SemSeguinte(Nil{}):
  +a => +b => sem_seguinte_vazio(a, b)

def prefixar_sem_seguinte(+q: Q.Quadro, -xs: List<&2, Q.Quadro>,
  neutra: {eh_seguinte(q) == False{} : Bool}, cauda: SemSeguinte(xs)) -> SemSeguinte(Con{q, xs}):
  +a => +b => sem_seguinte_na_frente(q, xs, a, b, neutra, cauda(a, b))

def concatenar_sem_seguinte(+xs: List<&2, Q.Quadro>, -ys: List<&2, Q.Quadro>,
  primeira: SemSeguinte(xs), segunda: SemSeguinte(ys)) -> SemSeguinte(Q.concatenar(xs, ys)):
  +a => +b => Cinco.concatenar_sem_quadro(xs, ys, Q.Seguinte{a, b}, primeira(a, b), segunda(a, b))

# Um unico percurso para todas as marcas que so podem ocorrer apos o fecho.
def SemPosteriores(-xs: List<&2, Q.Quadro>) -> Type:
  L.E<SemSeguinte(xs), L.E<{Fases.ausente(Fases.Completa{}, xs) == True{} : Bool},
    {Fases.ausente(Fases.Interrompida{}, xs) == True{} : Bool}>>

def quadro_anterior(+q: Q.Quadro) -> Bool:
  Bool.not(eh_seguinte(q)) && Bool.not(Fases.classificar(q, Fases.Completa{})) && Bool.not(Fases.classificar(q, Fases.Interrompida{}))

def Negativas(-q: Q.Quadro) -> Type:
  L.E<{eh_seguinte(q) == False{} : Bool}, L.E<{Fases.classificar(q, Fases.Completa{}) == False{} : Bool},
    {Fases.classificar(q, Fases.Interrompida{}) == False{} : Bool}>>

def negativas_do_quadro(+q: Q.Quadro, neutra: {quadro_anterior(q) == True{} : Bool}) -> Negativas(q):
  F.com_par(Negativas(q), {Bool.not(eh_seguinte(q)) && Bool.not(Fases.classificar(q, Fases.Completa{})) == True{} : Bool},
    {Bool.not(Fases.classificar(q, Fases.Interrompida{})) == True{} : Bool},
    F.e_booleano_separar(Bool.not(eh_seguinte(q)) && Bool.not(Fases.classificar(q, Fases.Completa{})), Bool.not(Fases.classificar(q, Fases.Interrompida{})), neutra), ab => ci =>
      F.com_par(Negativas(q), {Bool.not(eh_seguinte(q)) == True{} : Bool}, {Bool.not(Fases.classificar(q, Fases.Completa{})) == True{} : Bool},
        F.e_booleano_separar(Bool.not(eh_seguinte(q)), Bool.not(Fases.classificar(q, Fases.Completa{})), ab), a => b =>
          L.Ambos{F.negacao_verdadeira(eh_seguinte(q), a), L.Ambos{F.negacao_verdadeira(Fases.classificar(q, Fases.Completa{}), b), F.negacao_verdadeira(Fases.classificar(q, Fases.Interrompida{}), ci)}}))

def prefixar_ausencia(+tipo: Fases.Tipo, +q: Q.Quadro, -xs: List<&2, Q.Quadro>,
  neutra: {Fases.classificar(q, tipo) == False{} : Bool}, resto: {Fases.ausente(tipo, xs) == True{} : Bool}) ->
  {Fases.ausente(tipo, Con{q, xs}) == True{} : Bool}:
  %Equal.sym(Bool, Fases.classificar(q, tipo), False{}, neutra) : {Bool.not(_) && Fases.ausente(tipo, xs) == True{} : Bool}
  resto

def prefixar_pacote(+q: Q.Quadro, -xs: List<&2, Q.Quadro>, negativas: Negativas(q), cauda: SemPosteriores(xs)) -> SemPosteriores(Con{q, xs}):
  match negativas cauda:
    case L.Ambos{n, L.Ambos{c, i}} L.Ambos{sn, L.Ambos{sc, si}}:
      L.Ambos{prefixar_sem_seguinte(q, xs, n, sn), L.Ambos{prefixar_ausencia(Fases.Completa{}, q, xs, c, sc), prefixar_ausencia(Fases.Interrompida{}, q, xs, i, si)}}

def vazio_sem_posteriores() -> SemPosteriores(Nil{}):
  L.Ambos{vazio_sem_seguinte(), L.Ambos{{==}, {==}}}

def prefixar_sem_posteriores(+q: Q.Quadro, -xs: List<&2, Q.Quadro>, neutra: {quadro_anterior(q) == True{} : Bool}, cauda: SemPosteriores(xs)) -> SemPosteriores(Con{q, xs}):
  prefixar_pacote(q, xs, negativas_do_quadro(q, neutra), cauda)

def concatenar_sem_posteriores(+xs: List<&2, Q.Quadro>, +ys: List<&2, Q.Quadro>, primeira: SemPosteriores(xs), segunda: SemPosteriores(ys)) -> SemPosteriores(Q.concatenar(xs, ys)):
  match primeira segunda:
    case L.Ambos{sn1, L.Ambos{sc1, si1}} L.Ambos{sn2, L.Ambos{sc2, si2}}:
      L.Ambos{concatenar_sem_seguinte(xs, ys, sn1, sn2), L.Ambos{Fases.concatenar_ausencia(Fases.Completa{}, xs, ys, sc1, sc2), Fases.concatenar_ausencia(Fases.Interrompida{}, xs, ys, si1, si2)}}

def primitivas_sem_seguinte(+ps: List<&2, M.Primitiva>) -> SemSeguinte(M.expandir_primitivas(ps)):
  +a => +b => Cinco.internas_nao_contem(M.expandir_primitivas(ps), Q.Seguinte{a, b}, M.primitivas_so_geram_internas(ps), {==})

def primitivas_sem_posteriores(+ps: List<&2, M.Primitiva>) -> SemPosteriores(M.expandir_primitivas(ps)):
  L.Ambos{primitivas_sem_seguinte(ps), L.Ambos{Fases.primitivas_sem_macros(Fases.Completa{}, ps), Fases.primitivas_sem_macros(Fases.Interrompida{}, ps)}}

def entrada_sem_posteriores(m: R.Micro) -> SemPosteriores(R.micro_entrada(m)):
  match m:
    case R.Micro{a, b, c, d}: primitivas_sem_posteriores(a)

def autenticacao_sem_posteriores(m: R.Micro) -> SemPosteriores(R.micro_autenticacao(m)):
  match m:
    case R.Micro{a, b, c, d}: primitivas_sem_posteriores(b)

def execucao_micro_sem_posteriores(m: R.Micro) -> SemPosteriores(R.micro_execucao(m)):
  match m:
    case R.Micro{a, b, c, d}: primitivas_sem_posteriores(c)

def saida_sem_posteriores(m: R.Micro) -> SemPosteriores(R.micro_saida(m)):
  match m:
    case R.Micro{a, b, c, d}: primitivas_sem_posteriores(d)

def recebida_sem_posteriores(+m: R.Micro, +r: P.Requisicao) -> SemPosteriores(R.render_recebida(m, r)):
  concatenar_sem_posteriores(R.micro_entrada(m), [Q.Recebida{r}], entrada_sem_posteriores(m),
    prefixar_sem_posteriores(Q.Recebida{r}, Nil{}, {==}, vazio_sem_posteriores()))

def autenticada_sem_posteriores(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto) -> SemPosteriores(R.render_autenticada(m, r, ctx)):
  concatenar_sem_posteriores(R.render_recebida(m, r), Q.concatenar(R.micro_autenticacao(m), [Q.Autenticada{r, Some{ctx}}]),
    recebida_sem_posteriores(m, r),
    concatenar_sem_posteriores(R.micro_autenticacao(m), [Q.Autenticada{r, Some{ctx}}], autenticacao_sem_posteriores(m),
      prefixar_sem_posteriores(Q.Autenticada{r, Some{ctx}}, Nil{}, {==}, vazio_sem_posteriores())))

def verificada_sem_posteriores(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto) -> SemPosteriores(R.render_verificada(m, r, ctx)):
  concatenar_sem_posteriores(R.render_autenticada(m, r, ctx), [Q.Aceita{r, ctx}], autenticada_sem_posteriores(m, r, ctx),
    prefixar_sem_posteriores(Q.Aceita{r, ctx}, Nil{}, {==}, vazio_sem_posteriores()))

def comecada_sem_posteriores(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto) -> SemPosteriores(R.render_comecada(m, r, ctx)):
  concatenar_sem_posteriores(R.render_verificada(m, r, ctx), Q.concatenar(R.micro_execucao(m), [Q.Comecada{r, ctx}]),
    verificada_sem_posteriores(m, r, ctx),
    concatenar_sem_posteriores(R.micro_execucao(m), [Q.Comecada{r, ctx}], execucao_micro_sem_posteriores(m),
      prefixar_sem_posteriores(Q.Comecada{r, ctx}, Nil{}, {==}, vazio_sem_posteriores())))

def passos_sem_posteriores(+r: P.Requisicao, +ctx: D.Contexto, xs: List<&2, Q.QuadroExec>) -> SemPosteriores(Q.expandir_exec(r, ctx, xs)):
  match xs:
    case Nil{}: vazio_sem_posteriores()
    case Con{Q.Avaliacao{+p}, t}:
      prefixar_sem_posteriores(Q.Avaliada{r, ctx, p}, Q.expandir_exec(r, ctx, t), {==}, passos_sem_posteriores(r, ctx, t))
    case Con{Q.Operacao{+e, +s, +o, +res}, t}:
      prefixar_sem_posteriores(Q.Operada{e, s, o, res}, Q.expandir_exec(r, ctx, t), {==}, passos_sem_posteriores(r, ctx, t))

def execucao_sem_posteriores(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>) ->
  SemPosteriores(R.render_execucao(m, r, ctx, xs)):
  concatenar_sem_posteriores(R.render_comecada(m, r, ctx), Q.expandir_exec(r, ctx, xs),
    comecada_sem_posteriores(m, r, ctx), passos_sem_posteriores(r, ctx, xs))

def preparada_sem_posteriores(p: N.Preparada) -> SemPosteriores([R.quadro_preparada(p)]):
  match p:
    case N.Preparada{w, ts, +r, +bs}: prefixar_sem_posteriores(Q.Preparada{r, bs}, Nil{}, {==}, vazio_sem_posteriores())

def fase_sem_posteriores(+m: R.Micro, fase: R.FaseAntes) -> SemPosteriores(R.render_fase(m, fase)):
  match fase:
    case R.AntesEntrada{}: entrada_sem_posteriores(m)
    case R.AposReceber{r}: recebida_sem_posteriores(m, r)
    case R.AposAutenticar{r, ctx}: autenticada_sem_posteriores(m, r, ctx)
    case R.AposVerificar{r, ctx}: verificada_sem_posteriores(m, r, ctx)
    case R.Executando{r, ctx, xs}: execucao_sem_posteriores(m, r, ctx, xs)
    case R.AposPreparar{+r, +ctx, +xs, +p}:
      concatenar_sem_posteriores(R.render_execucao(m, r, ctx, xs), Q.concatenar(R.micro_saida(m), [R.quadro_preparada(p)]),
        execucao_sem_posteriores(m, r, ctx, xs),
        concatenar_sem_posteriores(R.micro_saida(m), [R.quadro_preparada(p)], saida_sem_posteriores(m),
          preparada_sem_posteriores(p)))


def AntesSemPosteriores(q: Maybe<&2, Fecho>) -> Type:
  match q:
    case None{}: Unit
    case Some{Fecho{antes, c, fecha, entrega, origem}}: SemPosteriores(antes)

def erro_sem_posteriores(q: Maybe<&2, List<&2, U32>>, +antes: List<&2, Q.Quadro>, +s: D.Estado,
  +e: Erros.Erro, +fecha: Bool, +entrega: R.Entrega, +origem: R.Caso, prova: SemPosteriores(antes)) ->
  AntesSemPosteriores(erro(q, antes, s, e, fecha, entrega, origem)):
  match q:
    case None{}: Unit{}
    case Some{bs}: prova

def antes_aut_sem_posteriores(+m: R.Micro, +r: P.Requisicao) -> SemPosteriores(antes_autenticacao(m, r)):
  concatenar_sem_posteriores(R.render_recebida(m, r), Q.concatenar(R.micro_autenticacao(m), [Q.Autenticada{r, None{}}]),
    recebida_sem_posteriores(m, r),
    concatenar_sem_posteriores(R.micro_autenticacao(m), [Q.Autenticada{r, None{}}], autenticacao_sem_posteriores(m),
      prefixar_sem_posteriores(Q.Autenticada{r, None{}}, Nil{}, {==}, vazio_sem_posteriores())))

def caso_fecho_sem_posteriores(+m: R.Micro, +s: D.Estado, caso: R.Caso) -> AntesSemPosteriores(do_caso(m, s, caso)):
  match caso:
    case R.EntradaRecusa{+e, +fecha, +entrega}:
      erro_sem_posteriores(P.enquadrar(S.resposta_valor(S.resposta_erro(Erros.status(erro_da_entrada(e))))),
        R.micro_entrada(m), s, erro_da_entrada(e), fecha, entrega, R.EntradaRecusa{e, fecha, entrega}, entrada_sem_posteriores(m))
    case R.AutRecusa{+r, +entrega}:
      erro_sem_posteriores(P.enquadrar(S.resposta_valor(S.resposta_erro(S.Autenticacao{}))), antes_autenticacao(m, r), s,
        Erros.Autenticacao{}, False{}, entrega, R.AutRecusa{r, entrega}, antes_aut_sem_posteriores(m, r))
    case R.GateRecusa{+r, +ctx, +entrega}:
      erro_sem_posteriores(P.enquadrar(S.resposta_valor(S.resposta_erro(S.Certificado{}))), antes_gate(m, r, ctx), s,
        Erros.Certificado{}, False{}, entrega, R.GateRecusa{r, ctx, entrega},
        concatenar_sem_posteriores(R.render_autenticada(m, r, ctx), [Q.Rejeitada{r, ctx}], autenticada_sem_posteriores(m, r, ctx),
          prefixar_sem_posteriores(Q.Rejeitada{r, ctx}, Nil{}, {==}, vazio_sem_posteriores())))
    case R.Executada{+r, +ctx, +xs, p, entrega}:
      concatenar_sem_posteriores(R.render_execucao(m, r, ctx, xs), R.micro_saida(m),
        execucao_sem_posteriores(m, r, ctx, xs), saida_sem_posteriores(m))
    case R.FalhaAntes{+fase, +etapa, +id, fatal, +entrega}:
      match fatal:
        case True{}: Unit{}
        case False{}:
          erro_sem_posteriores(P.enquadrar(S.resposta_valor(S.resposta_erro(S.Falha{}))),
            antes_falha(m, fase, etapa, id, False{}), s, Erros.Falha{}, False{}, entrega, R.FalhaAntes{fase, etapa, id, False{}, entrega},
            concatenar_sem_posteriores(R.render_fase(m, fase), [Q.Falhou{etapa, id, False{}}], fase_sem_posteriores(m, fase),
              prefixar_sem_posteriores(Q.Falhou{etapa, id, False{}}, Nil{}, {==}, vazio_sem_posteriores())))
    case R.InicialOk{}: Unit{}
    case R.InicialRecusa{status}: Unit{}
    case R.InicialFalha{aceita, etapa, id, fatal}: Unit{}
    case R.SemResposta{}: Unit{}
    case R.FatalAposPublicacao{r, ctx, xs, p, etapa, id}: Unit{}
    case R.Pendente{fase}: Unit{}
    case R.InicialPendente{aceita}: Unit{}

def configurar_sem_posteriores(q: Maybe<&2, Fecho>, prova: AntesSemPosteriores(q)) -> AntesSemPosteriores(configurar(q)):
  match q:
    case None{}: Unit{}
    case Some{Fecho{+antes, c, fecha, entrega, origem}}:
      prefixar_sem_posteriores(Q.Configurada{}, antes, {==}, prova)

law antes_do_fecho_sem_posteriores:
  for +m: R.Micro
  for +s: D.Estado
  for +caso: R.Caso
  AntesSemPosteriores(fecho_do_caso(m, s, caso))
def antes_do_fecho_sem_posteriores(m, s, caso):
  configurar_sem_posteriores(do_caso(m, s, caso), caso_fecho_sem_posteriores(m, s, caso))

def erro_tem_fecho(+antes: List<&2, Q.Quadro>, +s: D.Estado, +e: Erros.Erro,
  +fecha: Bool, +entrega: R.Entrega, +origem: R.Caso) ->
  &h: Fecho -> {fechar_erro(antes, s, e, fecha, entrega, origem) == Some{h} : Maybe<&2, Fecho>}:
  (Fecho{antes, N.Conclusao{s, S.resposta_erro(Erros.status(e)), Erros.bytes(e)}, fecha, entrega, origem},
    Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, Fecho>, q => erro(q, antes, s, e, fecha, entrega, origem),
      P.enquadrar(S.resposta_valor(S.resposta_erro(Erros.status(e)))), Some{Erros.bytes(e)},
      Erros.todos_os_erros_preparados_sao_exatamente_mensagens_originais(e)))

def algum_fecho_contradiz_ausencia(-T: Type, +q: Maybe<&2, Fecho>,
  existe: &h: Fecho -> {q == Some{h} : Maybe<&2, Fecho>},
  ausente: {q == None{} : Maybe<&2, Fecho>}) -> T:
  match existe:
    case (+h, presente):
      L.ex_falso(T, F.nenhum_nao_algum(Fecho, h,
        Equal.trans(Maybe<&2, Fecho>, None{}, q, Some{h}, Equal.sym(Maybe<&2, Fecho>, q, None{}, ausente), presente)))

def inicial_sem_posteriores(q: Maybe<&2, List<&2, U32>>, +s: D.Estado) -> SemPosteriores(R.render_inicial(q, s)):
  match q:
    case None{}: prefixar_sem_posteriores(Q.Codificada{D.estado_valor(s), None{}}, Nil{}, {==}, vazio_sem_posteriores())
    case Some{+bs}:
      prefixar_sem_posteriores(Q.Codificada{D.estado_valor(s), Some{bs}}, [Q.Guardada{s, bs, s}, Q.Iniciada{s}], {==},
        prefixar_sem_posteriores(Q.Guardada{s, bs, s}, [Q.Iniciada{s}], {==},
          prefixar_sem_posteriores(Q.Iniciada{s}, Nil{}, {==}, vazio_sem_posteriores())))

def prefixo_inicial_sem_posteriores(+m: R.Micro, aceita: Bool) -> SemPosteriores(R.prefixo_inicial(m, aceita)):
  match aceita:
    case False{}: vazio_sem_posteriores()
    case True{}: prefixar_sem_posteriores(Q.InicialAceita{}, R.micro_saida(m), {==}, saida_sem_posteriores(m))

def publicacao_sem_posteriores(r: S.Resposta, +s: D.Estado) -> SemPosteriores(R.render_publicacao(r, s)):
  match r:
    case S.Resposta{S.Sucesso{}, v}: prefixar_sem_posteriores(Q.Publicada{s}, Nil{}, {==}, vazio_sem_posteriores())
    case S.Resposta{S.Recusa{}, v}: vazio_sem_posteriores()
    case S.Resposta{S.Entrada{}, v}: vazio_sem_posteriores()
    case S.Resposta{S.Autenticacao{}, v}: vazio_sem_posteriores()
    case S.Resposta{S.Certificado{}, v}: vazio_sem_posteriores()
    case S.Resposta{S.Dados{}, v}: vazio_sem_posteriores()
    case S.Resposta{S.Limite{}, v}: vazio_sem_posteriores()
    case S.Resposta{S.Falha{}, v}: vazio_sem_posteriores()

def fatal_sem_posteriores(c: N.Conclusao, +etapa: X.Etapa, +id: String) -> SemPosteriores(R.render_fatal_publicada(c, etapa, id)):
  match c:
    case N.Conclusao{+s, +r, +bs}:
      prefixar_sem_posteriores(Q.Preparada{r, bs}, Q.concatenar(R.render_publicacao(r, s), [Q.Falhou{etapa, id, True{}}, Q.Fechada{}]), {==},
        concatenar_sem_posteriores(R.render_publicacao(r, s), [Q.Falhou{etapa, id, True{}}, Q.Fechada{}],
          publicacao_sem_posteriores(r, s),
          prefixar_sem_posteriores(Q.Falhou{etapa, id, True{}}, [Q.Fechada{}], {==},
            prefixar_sem_posteriores(Q.Fechada{}, Nil{}, {==}, vazio_sem_posteriores()))))

def ausencia_do_caso_exclui_posteriores(+m: R.Micro, +s: D.Estado, +caso: R.Caso,
  ausente: {do_caso(m, s, caso) == None{} : Maybe<&2, Fecho>}) -> SemPosteriores(R.render_caso(m, s, caso)):
  match caso:
    case R.InicialOk{}:
      prefixar_sem_posteriores(Q.InicialAceita{}, Q.concatenar(R.micro_saida(m), R.render_inicial(P.codificar(D.estado_valor(s)), s)), {==},
        concatenar_sem_posteriores(R.micro_saida(m), R.render_inicial(P.codificar(D.estado_valor(s)), s),
          saida_sem_posteriores(m), inicial_sem_posteriores(P.codificar(D.estado_valor(s)), s)))
    case R.InicialRecusa{+status}: prefixar_sem_posteriores(Q.InicialRecusada{status}, Nil{}, {==}, vazio_sem_posteriores())
    case R.InicialFalha{+aceita, +etapa, +id, +fatal}:
      concatenar_sem_posteriores(R.prefixo_inicial(m, aceita), [Q.Falhou{etapa, id, fatal}, Q.InicialRecusada{S.Falha{}}],
        prefixo_inicial_sem_posteriores(m, aceita),
        prefixar_sem_posteriores(Q.Falhou{etapa, id, fatal}, [Q.InicialRecusada{S.Falha{}}], {==},
          prefixar_sem_posteriores(Q.InicialRecusada{S.Falha{}}, Nil{}, {==}, vazio_sem_posteriores())))
    case R.SemResposta{}: prefixar_sem_posteriores(Q.Fechada{}, Nil{}, {==}, vazio_sem_posteriores())
    case R.EntradaRecusa{+e, +fecha, +entrega}:
      algum_fecho_contradiz_ausencia(SemPosteriores(R.render_caso(m, s, R.EntradaRecusa{e, fecha, entrega})),
        do_caso(m, s, R.EntradaRecusa{e, fecha, entrega}),
        erro_tem_fecho(R.micro_entrada(m), s, erro_da_entrada(e), fecha, entrega, R.EntradaRecusa{e, fecha, entrega}), ausente)
    case R.AutRecusa{+r, +entrega}:
      algum_fecho_contradiz_ausencia(SemPosteriores(R.render_caso(m, s, R.AutRecusa{r, entrega})), do_caso(m, s, R.AutRecusa{r, entrega}),
        erro_tem_fecho(antes_autenticacao(m, r), s, Erros.Autenticacao{}, False{}, entrega, R.AutRecusa{r, entrega}), ausente)
    case R.GateRecusa{+r, +ctx, +entrega}:
      algum_fecho_contradiz_ausencia(SemPosteriores(R.render_caso(m, s, R.GateRecusa{r, ctx, entrega})), do_caso(m, s, R.GateRecusa{r, ctx, entrega}),
        erro_tem_fecho(antes_gate(m, r, ctx), s, Erros.Certificado{}, False{}, entrega, R.GateRecusa{r, ctx, entrega}), ausente)
    case R.Executada{+r, +ctx, +xs, +p, +entrega}:
      algum_fecho_contradiz_ausencia(SemPosteriores(R.render_caso(m, s, R.Executada{r, ctx, xs, p, entrega})), do_caso(m, s, R.Executada{r, ctx, xs, p, entrega}),
        (Fecho{antes_execucao(m, r, ctx, xs), N.concluir(p, s), False{}, entrega, R.Executada{r, ctx, xs, p, entrega}}, {==}), ausente)
    case R.FalhaAntes{+fase, +etapa, +id, fatal, +entrega}:
      match fatal:
        case True{}:
          concatenar_sem_posteriores(R.render_fase(m, fase), R.render_falha(s, etapa, id, True{}, entrega), fase_sem_posteriores(m, fase),
            prefixar_sem_posteriores(Q.Falhou{etapa, id, True{}}, [Q.Fechada{}], {==}, prefixar_sem_posteriores(Q.Fechada{}, Nil{}, {==}, vazio_sem_posteriores())))
        case False{}:
          algum_fecho_contradiz_ausencia(SemPosteriores(R.render_caso(m, s, R.FalhaAntes{fase, etapa, id, False{}, entrega})),
            do_caso(m, s, R.FalhaAntes{fase, etapa, id, False{}, entrega}),
            erro_tem_fecho(antes_falha(m, fase, etapa, id, False{}), s, Erros.Falha{}, False{}, entrega, R.FalhaAntes{fase, etapa, id, False{}, entrega}), ausente)
    case R.FatalAposPublicacao{+r, +ctx, +xs, +p, +etapa, +id}:
      concatenar_sem_posteriores(R.render_execucao(m, r, ctx, xs), Q.concatenar(R.micro_saida(m), R.render_fatal_publicada(N.concluir(p, s), etapa, id)),
        execucao_sem_posteriores(m, r, ctx, xs),
        concatenar_sem_posteriores(R.micro_saida(m), R.render_fatal_publicada(N.concluir(p, s), etapa, id),
          saida_sem_posteriores(m), fatal_sem_posteriores(N.concluir(p, s), etapa, id)))
    case R.Pendente{fase}: fase_sem_posteriores(m, fase)
    case R.InicialPendente{aceita}: prefixo_inicial_sem_posteriores(m, aceita)

def retirar_configuracao_vazia(q: Maybe<&2, Fecho>, ausente: {configurar(q) == None{} : Maybe<&2, Fecho>}) ->
  {q == None{} : Maybe<&2, Fecho>}:
  match q:
    case None{}: {==}
    case Some{Fecho{+antes, +c, +fecha, +entrega, +origem}}:
      L.ex_falso({Some{Fecho{antes, c, fecha, entrega, origem}} == None{} : Maybe<&2, Fecho>},
        F.nenhum_nao_algum(Fecho, Fecho{Con{Q.Configurada{}, antes}, c, fecha, entrega, origem},
          Equal.sym(Maybe<&2, Fecho>, Some{Fecho{Con{Q.Configurada{}, antes}, c, fecha, entrega, origem}}, None{}, ausente)))

law ausencia_do_fecho_exclui_posteriores:
  for +m: R.Micro
  for +s: D.Estado
  for +caso: R.Caso
  for ausente: {fecho_do_caso(m, s, caso) == None{} : Maybe<&2, Fecho>}
  SemPosteriores(R.render(m, s, caso))
def ausencia_do_fecho_exclui_posteriores(m, s, caso, ausente):
  prefixar_sem_posteriores(Q.Configurada{}, R.render_caso(m, s, caso), {==},
    ausencia_do_caso_exclui_posteriores(m, s, caso, retirar_configuracao_vazia(do_caso(m, s, caso), ausente)))

# Adaptadores das APIs consumidas pela Lei6, sem outro percurso.
def AntesSemSeguinte(q: Maybe<&2, Fecho>) -> Type:
  match q:
    case None{}: Unit
    case Some{Fecho{antes, c, fecha, entrega, origem}}: SemSeguinte(antes)

def extrair_antes_seguinte(q: Maybe<&2, Fecho>, prova: AntesSemPosteriores(q)) -> AntesSemSeguinte(q):
  match q:
    case None{}: Unit{}
    case Some{Fecho{antes, c, fecha, entrega, origem}}:
      L.e_esquerda(SemSeguinte(antes), L.E<{Fases.ausente(Fases.Completa{}, antes) == True{} : Bool}, {Fases.ausente(Fases.Interrompida{}, antes) == True{} : Bool}>, prova)

def antes_do_fecho_sem_seguinte(+m: R.Micro, +s: D.Estado, +caso: R.Caso) -> AntesSemSeguinte(fecho_do_caso(m, s, caso)):
  extrair_antes_seguinte(fecho_do_caso(m, s, caso), antes_do_fecho_sem_posteriores(m, s, caso))

def ausencia_do_fecho_exclui_seguinte(+m: R.Micro, +s: D.Estado, +caso: R.Caso, ausente: {fecho_do_caso(m, s, caso) == None{} : Maybe<&2, Fecho>}) -> SemSeguinte(R.render(m, s, caso)):
  L.e_esquerda(SemSeguinte(R.render(m, s, caso)), L.E<{Fases.ausente(Fases.Completa{}, R.render(m, s, caso)) == True{} : Bool}, {Fases.ausente(Fases.Interrompida{}, R.render(m, s, caso)) == True{} : Bool}>, ausencia_do_fecho_exclui_posteriores(m, s, caso, ausente))

def publicacao_sem_seguinte(r: S.Resposta, +s: D.Estado) -> SemSeguinte(R.render_publicacao(r, s)):
  L.e_esquerda(SemSeguinte(R.render_publicacao(r, s)), L.E<{Fases.ausente(Fases.Completa{}, R.render_publicacao(r, s)) == True{} : Bool}, {Fases.ausente(Fases.Interrompida{}, R.render_publicacao(r, s)) == True{} : Bool}>, publicacao_sem_posteriores(r, s))

def EntregasDaForma(-xs: List<&2, Q.Quadro>, q: Maybe<&2, Fecho>) -> Type:
  match q:
    case None{}: L.E<{Fases.ausente(Fases.Completa{}, xs) == True{} : Bool}, {Fases.ausente(Fases.Interrompida{}, xs) == True{} : Bool}>
    case Some{Fecho{antes, c, fecha, entrega, origem}}:
      L.E<{Fases.ausente(Fases.Completa{}, antes) == True{} : Bool}, {Fases.ausente(Fases.Interrompida{}, antes) == True{} : Bool}>

def entregas_das_provas(+xs: List<&2, Q.Quadro>, q: Maybe<&2, Fecho>, antes: AntesSemPosteriores(q),
  nenhuma: {q == None{} : Maybe<&2, Fecho>} -> SemPosteriores(xs)) -> EntregasDaForma(xs, q):
  match q:
    case None{}:
      L.e_direita(SemSeguinte(xs), L.E<{Fases.ausente(Fases.Completa{}, xs) == True{} : Bool}, {Fases.ausente(Fases.Interrompida{}, xs) == True{} : Bool}>, nenhuma({==}))
    case Some{Fecho{prefixo, c, fecha, entrega, origem}}:
      L.e_direita(SemSeguinte(prefixo), L.E<{Fases.ausente(Fases.Completa{}, prefixo) == True{} : Bool}, {Fases.ausente(Fases.Interrompida{}, prefixo) == True{} : Bool}>, antes)

law entregas_da_forma:
  for +m: R.Micro
  for +s: D.Estado
  for +caso: R.Caso
  EntregasDaForma(R.render(m, s, caso), fecho_do_caso(m, s, caso))
def entregas_da_forma(m, s, caso):
  entregas_das_provas(R.render(m, s, caso), fecho_do_caso(m, s, caso), antes_do_fecho_sem_posteriores(m, s, caso), ausencia_do_fecho_exclui_posteriores(m, s, caso))

def encontrar_fecho_seguinte(+xs: List<&2, Q.Quadro>, +caso: R.Caso, q: Maybe<&2, Fecho>,
  +t: Nat, +a: D.Estado, +b: D.Estado, forma: Forma(xs, caso, q),
  antes: AntesSemSeguinte(q), sem_fecho: {q == None{} : Maybe<&2, Fecho>} -> SemSeguinte(xs),
  consulta: {Q.consultar(xs, t) == Some{Q.Seguinte{a, b}} : Maybe<&2, Q.Quadro>}) ->
  &h: Fecho -> L.E<Forma(xs, caso, Some{h}), AntesSemSeguinte(Some{h})>:
  match q:
    case None{}:
      L.ex_falso((&h: Fecho -> L.E<Forma(xs, caso, Some{h}), AntesSemSeguinte(Some{h})>),
        sem_fecho({==})(a, b, t, consulta))
    case Some{+h}: (h, L.Ambos{forma, antes})

law inverter_seguinte:
  for +m: R.Micro
  for +s: D.Estado
  for +caso: R.Caso
  for +t: Nat
  for +a: D.Estado
  for +b: D.Estado
  for consulta: {Q.consultar(R.render(m, s, caso), t) == Some{Q.Seguinte{a, b}} : Maybe<&2, Q.Quadro>}
  exs h: Fecho
  L.E<Forma(R.render(m, s, caso), caso, Some{h}), AntesSemSeguinte(Some{h})>
def inverter_seguinte(m, s, caso, t, a, b, consulta):
  encontrar_fecho_seguinte(R.render(m, s, caso), caso, fecho_do_caso(m, s, caso), t, a, b,
    forma_da_rota(m, s, caso), antes_do_fecho_sem_seguinte(m, s, caso),
    ausencia_do_fecho_exclui_seguinte(m, s, caso), consulta)

# Uma preparacao nativa e distinta do erro fixo que pode vir depois dela.
type OrigemPreparo is Data:
  Nativo{requisicao: P.Requisicao, contexto: D.Contexto, quadros: List<&2, Q.QuadroExec>, preparada: N.Preparada}
  Fixo{erro: Erros.Erro}

def marco_preparo(origem: OrigemPreparo) -> Q.Quadro:
  match origem:
    case Nativo{r, ctx, xs, p}: R.quadro_preparada(p)
    case Fixo{+e}: Q.Preparada{S.resposta_erro(Erros.status(e)), Erros.bytes(e)}

def FixoDoCaso(-e: Erros.Erro, caso: R.Caso) -> Type:
  match caso:
    case R.EntradaRecusa{erro, fecha, entrega}: {e == erro_da_entrada(erro) : Erros.Erro}
    case R.AutRecusa{r, entrega}: {e == Erros.Autenticacao{} : Erros.Erro}
    case R.GateRecusa{r, ctx, entrega}: {e == Erros.Certificado{} : Erros.Erro}
    case R.FalhaAntes{fase, etapa, id, fatal, entrega}: L.E<{e == Erros.Falha{} : Erros.Erro}, {fatal == False{} : Bool}>
    case _: Empty

def PrefixoFixo(+m: R.Micro, caso: R.Caso, +antes: List<&2, Q.Quadro>) -> Type:
  match caso:
    case R.EntradaRecusa{e, fecha, entrega}: {antes == Con{Q.Configurada{}, R.micro_entrada(m)} : List<&2, Q.Quadro>}
    case R.AutRecusa{r, entrega}: {antes == Con{Q.Configurada{}, antes_autenticacao(m, r)} : List<&2, Q.Quadro>}
    case R.GateRecusa{r, ctx, entrega}: {antes == Con{Q.Configurada{}, antes_gate(m, r, ctx)} : List<&2, Q.Quadro>}
    case R.FalhaAntes{fase, etapa, id, fatal, entrega}: {antes == Con{Q.Configurada{}, antes_falha(m, fase, etapa, id, fatal)} : List<&2, Q.Quadro>}
    case _: Empty

def PreparoDaOrigem(~fonte: Fonte.Fonte, ~c: S.Configuracao, +m: R.Micro, -s: D.Estado,
  +codigo: Fonte.JuizoSintatico, +caso: R.Caso, +antes: List<&2, Q.Quadro>, origem: OrigemPreparo) -> Type:
  match origem:
    case Nativo{r, ctx, xs, p}:
      L.E<{antes == Con{Q.Configurada{}, antes_execucao(m, r, ctx, xs)} : List<&2, Q.Quadro>}, Fonte.FinalReal(fonte, c, s, r, ctx, codigo, xs, p)>
    case Fixo{e}: L.E<FixoDoCaso(e, caso), PrefixoFixo(m, caso, antes)>

def PreparoNoTraco(~fonte: Fonte.Fonte, ~c: S.Configuracao, +m: R.Micro, -s: D.Estado,
  +codigo: Fonte.JuizoSintatico, +caso: R.Caso, -qs: List<&2, Q.Quadro>, -t: Nat, +r: S.Resposta, +bs: List<&2, U32>) -> Type:
  &antes: List<&2, Q.Quadro> -> &depois: List<&2, Q.Quadro> -> &origem: OrigemPreparo ->
    L.E<{qs == Q.concatenar(antes, Con{Q.Preparada{r, bs}, depois}) : List<&2, Q.Quadro>},
      L.E<{t == Nat.add(Q.tamanho(antes), 0n) : Nat},
        L.E<{Q.Preparada{r, bs} == marco_preparo(origem) : Q.Quadro}, PreparoDaOrigem(fonte, c, m, s, codigo, caso, antes, origem)>>>

def eh_preparo(q: Q.Quadro) -> Bool:
  match q:
    case Q.Preparada{r, bs}: True{}
    case _: False{}

def SemPreparo(-qs: List<&2, Q.Quadro>) -> Type:
  @r: S.Resposta -> @bs: List<&2, U32> -> Cinco.SemQuadro(qs, Q.Preparada{r, bs})

def sem_preparo_vazio() -> SemPreparo(Nil{}):
  +r => +bs => Cinco.vazio_sem_quadro(Q.Preparada{r, bs})

def prefixar_sem_preparo(+q: Q.Quadro, -qs: List<&2, Q.Quadro>, neutra: {eh_preparo(q) == False{} : Bool}, resto: SemPreparo(qs)) -> SemPreparo(Con{q, qs}):
  +r => +bs => Cinco.cabeca_por_tag(eh_preparo, q, Q.Preparada{r, bs}, qs, neutra, {==}, resto(r, bs))

def concatenar_sem_preparo(+xs: List<&2, Q.Quadro>, -ys: List<&2, Q.Quadro>, a: SemPreparo(xs), b: SemPreparo(ys)) -> SemPreparo(Q.concatenar(xs, ys)):
  +r => +bs => Cinco.concatenar_sem_quadro(xs, ys, Q.Preparada{r, bs}, a(r, bs), b(r, bs))

def primitivas_sem_preparo(+ps: List<&2, M.Primitiva>) -> SemPreparo(M.expandir_primitivas(ps)):
  +r => +bs => Cinco.internas_nao_contem(M.expandir_primitivas(ps), Q.Preparada{r, bs}, M.primitivas_so_geram_internas(ps), {==})

def entrada_sem_preparo(m: R.Micro) -> SemPreparo(R.micro_entrada(m)):
  match m:
    case R.Micro{a, b, c, d}: primitivas_sem_preparo(a)

def autenticacao_sem_preparo(m: R.Micro) -> SemPreparo(R.micro_autenticacao(m)):
  match m:
    case R.Micro{a, b, c, d}: primitivas_sem_preparo(b)

def execucao_micro_sem_preparo(m: R.Micro) -> SemPreparo(R.micro_execucao(m)):
  match m:
    case R.Micro{a, b, c, d}: primitivas_sem_preparo(c)

def saida_sem_preparo(m: R.Micro) -> SemPreparo(R.micro_saida(m)):
  match m:
    case R.Micro{a, b, c, d}: primitivas_sem_preparo(d)

def recebida_sem_preparo(+m: R.Micro, +r: P.Requisicao) -> SemPreparo(R.render_recebida(m, r)):
  concatenar_sem_preparo(R.micro_entrada(m), [Q.Recebida{r}], entrada_sem_preparo(m), prefixar_sem_preparo(Q.Recebida{r}, Nil{}, {==}, sem_preparo_vazio()))

def autenticada_sem_preparo(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto) -> SemPreparo(R.render_autenticada(m, r, ctx)):
  concatenar_sem_preparo(R.render_recebida(m, r), Q.concatenar(R.micro_autenticacao(m), [Q.Autenticada{r, Some{ctx}}]), recebida_sem_preparo(m, r),
    concatenar_sem_preparo(R.micro_autenticacao(m), [Q.Autenticada{r, Some{ctx}}], autenticacao_sem_preparo(m), prefixar_sem_preparo(Q.Autenticada{r, Some{ctx}}, Nil{}, {==}, sem_preparo_vazio())))

def verificada_sem_preparo(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto) -> SemPreparo(R.render_verificada(m, r, ctx)):
  concatenar_sem_preparo(R.render_autenticada(m, r, ctx), [Q.Aceita{r, ctx}], autenticada_sem_preparo(m, r, ctx), prefixar_sem_preparo(Q.Aceita{r, ctx}, Nil{}, {==}, sem_preparo_vazio()))

def comecada_sem_preparo(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto) -> SemPreparo(R.render_comecada(m, r, ctx)):
  concatenar_sem_preparo(R.render_verificada(m, r, ctx), Q.concatenar(R.micro_execucao(m), [Q.Comecada{r, ctx}]), verificada_sem_preparo(m, r, ctx),
    concatenar_sem_preparo(R.micro_execucao(m), [Q.Comecada{r, ctx}], execucao_micro_sem_preparo(m), prefixar_sem_preparo(Q.Comecada{r, ctx}, Nil{}, {==}, sem_preparo_vazio())))

def passos_sem_preparo(+r: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>) -> SemPreparo(Q.expandir_exec(r, ctx, xs)):
  +resposta => +bs => +t => consulta => Exec.expandir_reflete_consulta(r, ctx, xs, t, Q.Preparada{resposta, bs}, consulta)

def execucao_sem_preparo(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>) -> SemPreparo(R.render_execucao(m, r, ctx, xs)):
  concatenar_sem_preparo(R.render_comecada(m, r, ctx), Q.expandir_exec(r, ctx, xs), comecada_sem_preparo(m, r, ctx), passos_sem_preparo(r, ctx, xs))

def antes_execucao_sem_preparo(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>) ->
  SemPreparo(Con{Q.Configurada{}, antes_execucao(m, r, ctx, xs)}):
  prefixar_sem_preparo(Q.Configurada{}, antes_execucao(m, r, ctx, xs), {==}, concatenar_sem_preparo(R.render_execucao(m, r, ctx, xs), R.micro_saida(m), execucao_sem_preparo(m, r, ctx, xs), saida_sem_preparo(m)))

# Inversao de uma marca. Prefixos podem conter outras preparacoes apenas no
# combinador de duas marcas abaixo; nao se afirma unicidade global de preparo.
def devolver_preparo(~fonte: Fonte.Fonte, ~c: S.Configuracao, +m: R.Micro, -s: D.Estado, +codigo: Fonte.JuizoSintatico,
  +caso: R.Caso, +antes: List<&2, Q.Quadro>, +depois: List<&2, Q.Quadro>, +origem: OrigemPreparo, +t: Nat, +r: S.Resposta, +bs: List<&2, U32>,
  posicao: {t == Nat.add(Q.tamanho(antes), 0n) : Nat}, +quadro: {Q.Preparada{r, bs} == marco_preparo(origem) : Q.Quadro},
  fonte_real: PreparoDaOrigem(fonte, c, m, s, codigo, caso, antes, origem)) ->
  PreparoNoTraco(fonte, c, m, s, codigo, caso, Q.concatenar(antes, Con{marco_preparo(origem), depois}), t, r, bs):
  (antes, depois, origem, L.Ambos{
    Equal.cong(Q.Quadro, List<&2, Q.Quadro>, q => Q.concatenar(antes, Con{q, depois}), marco_preparo(origem), Q.Preparada{r, bs}, Equal.sym(Q.Quadro, Q.Preparada{r, bs}, marco_preparo(origem), quadro)),
    L.Ambos{posicao, L.Ambos{quadro, fonte_real}}})

def inverter_marca_de_preparo(~fonte: Fonte.Fonte, ~c: S.Configuracao, +m: R.Micro, -s: D.Estado, +codigo: Fonte.JuizoSintatico,
  +caso: R.Caso, +antes: List<&2, Q.Quadro>, +depois: List<&2, Q.Quadro>, +origem: OrigemPreparo, +t: Nat, +r: S.Resposta, +bs: List<&2, U32>,
  sem_antes: SemPreparo(antes), sem_depois: SemPreparo(depois), fonte_real: PreparoDaOrigem(fonte, c, m, s, codigo, caso, antes, origem),
  consulta: {Q.consultar(Q.concatenar(antes, Con{marco_preparo(origem), depois}), t) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>}) ->
  PreparoNoTraco(fonte, c, m, s, codigo, caso, Q.concatenar(antes, Con{marco_preparo(origem), depois}), t, r, bs):
  F.com_par(PreparoNoTraco(fonte, c, m, s, codigo, caso, Q.concatenar(antes, Con{marco_preparo(origem), depois}), t, r, bs),
    {t == Nat.add(Q.tamanho(antes), 0n) : Nat}, {Q.Preparada{r, bs} == marco_preparo(origem) : Q.Quadro},
    Cinco.marcador_unico(antes, marco_preparo(origem), depois, Q.Preparada{r, bs}, t, sem_antes(r, bs), sem_depois(r, bs), consulta),
    posicao => quadro => devolver_preparo(fonte, c, m, s, codigo, caso, antes, depois, origem, t, r, bs, posicao, quadro, fonte_real))

def preparo_por_equacoes(~fonte: Fonte.Fonte, ~c: S.Configuracao, +m: R.Micro, -s: D.Estado, +codigo: Fonte.JuizoSintatico,
  +caso: R.Caso, +qs: List<&2, Q.Quadro>, +antes: List<&2, Q.Quadro>, +depois: List<&2, Q.Quadro>, +origem: OrigemPreparo, +t: Nat, +r: S.Resposta, +bs: List<&2, U32>,
  traco: {qs == Q.concatenar(antes, Con{marco_preparo(origem), depois}) : List<&2, Q.Quadro>},
  posicao: {t == Nat.add(Q.tamanho(antes), 0n) : Nat}, +quadro: {Q.Preparada{r, bs} == marco_preparo(origem) : Q.Quadro},
  fonte_real: PreparoDaOrigem(fonte, c, m, s, codigo, caso, antes, origem)) -> PreparoNoTraco(fonte, c, m, s, codigo, caso, qs, t, r, bs):
  (antes, depois, origem, L.Ambos{Equal.trans(List<&2, Q.Quadro>, qs, Q.concatenar(antes, Con{marco_preparo(origem), depois}), Q.concatenar(antes, Con{Q.Preparada{r, bs}, depois}),
    traco, Equal.cong(Q.Quadro, List<&2, Q.Quadro>, q => Q.concatenar(antes, Con{q, depois}), marco_preparo(origem), Q.Preparada{r, bs}, Equal.sym(Q.Quadro, Q.Preparada{r, bs}, marco_preparo(origem), quadro))),
    L.Ambos{posicao, L.Ambos{quadro, fonte_real}}})

law tamanho_somado:
  for xs: List<&2, Q.Quadro>
  for -ys: List<&2, Q.Quadro>
  for -n: Nat
  {Nat.add(Q.tamanho(xs), Nat.add(Q.tamanho(ys), n)) == Nat.add(Q.tamanho(Q.concatenar(xs, ys)), n) : Nat}
def tamanho_somado(xs, ys, n):
  match xs:
    case Nil{}: {==}
    case Con{h, +t}: Equal.cong(Nat, Nat, z => Succ{z}, Nat.add(Q.tamanho(t), Nat.add(Q.tamanho(ys), n)), Nat.add(Q.tamanho(Q.concatenar(t, ys)), n), tamanho_somado(t, ys, n))

def duas_marcas_pela_parte(~fonte: Fonte.Fonte, ~c: S.Configuracao, +m: R.Micro, -s: D.Estado, +codigo: Fonte.JuizoSintatico,
  +caso: R.Caso, +antes: List<&2, Q.Quadro>, +meio: List<&2, Q.Quadro>, +depois: List<&2, Q.Quadro>,
  +nativa: OrigemPreparo, +fixa: OrigemPreparo, +t: Nat, +r: S.Resposta, +bs: List<&2, U32>,
  sem_antes: SemPreparo(antes), sem_meio: SemPreparo(meio), sem_depois: SemPreparo(depois),
  origem_nativa: PreparoDaOrigem(fonte, c, m, s, codigo, caso, antes, nativa),
  origem_fixa: PreparoDaOrigem(fonte, c, m, s, codigo, caso, Q.concatenar(Q.concatenar(antes, [marco_preparo(nativa)]), meio), fixa),
  parte: Q.Parte(Q.concatenar(antes, [marco_preparo(nativa)]), Q.concatenar(meio, Con{marco_preparo(fixa), depois}), t, Q.Preparada{r, bs})) ->
  PreparoNoTraco(fonte, c, m, s, codigo, caso,
    Q.concatenar(Q.concatenar(antes, [marco_preparo(nativa)]), Q.concatenar(meio, Con{marco_preparo(fixa), depois})), t, r, bs):
  match parte:
    case L.Esquerda{(+i, L.Ambos{pos, consulta})}:
      F.com_par(PreparoNoTraco(fonte, c, m, s, codigo, caso, Q.concatenar(Q.concatenar(antes, [marco_preparo(nativa)]), Q.concatenar(meio, Con{marco_preparo(fixa), depois})), t, r, bs),
        {i == Nat.add(Q.tamanho(antes), 0n) : Nat}, {Q.Preparada{r, bs} == marco_preparo(nativa) : Q.Quadro},
        Cinco.marcador_unico(antes, marco_preparo(nativa), Nil{}, Q.Preparada{r, bs}, i, sem_antes(r, bs), Cinco.vazio_sem_quadro(Q.Preparada{r, bs}), consulta), tamanho => quadro =>
          preparo_por_equacoes(fonte, c, m, s, codigo, caso,
            Q.concatenar(Q.concatenar(antes, [marco_preparo(nativa)]), Q.concatenar(meio, Con{marco_preparo(fixa), depois})), antes, Q.concatenar(meio, Con{marco_preparo(fixa), depois}), nativa, t, r, bs,
            Q.concatenar_assoc(antes, [marco_preparo(nativa)], Q.concatenar(meio, Con{marco_preparo(fixa), depois})),
            Equal.trans(Nat, t, i, Nat.add(Q.tamanho(antes), 0n), pos, tamanho), quadro, origem_nativa))
    case L.Direita{(+i, L.Ambos{pos, consulta})}:
      F.com_par(PreparoNoTraco(fonte, c, m, s, codigo, caso, Q.concatenar(Q.concatenar(antes, [marco_preparo(nativa)]), Q.concatenar(meio, Con{marco_preparo(fixa), depois})), t, r, bs),
        {i == Nat.add(Q.tamanho(meio), 0n) : Nat}, {Q.Preparada{r, bs} == marco_preparo(fixa) : Q.Quadro},
        Cinco.marcador_unico(meio, marco_preparo(fixa), depois, Q.Preparada{r, bs}, i, sem_meio(r, bs), sem_depois(r, bs), consulta), tamanho => quadro =>
          preparo_por_equacoes(fonte, c, m, s, codigo, caso,
            Q.concatenar(Q.concatenar(antes, [marco_preparo(nativa)]), Q.concatenar(meio, Con{marco_preparo(fixa), depois})), Q.concatenar(Q.concatenar(antes, [marco_preparo(nativa)]), meio), depois, fixa, t, r, bs,
            Equal.sym(List<&2, Q.Quadro>, Q.concatenar(Q.concatenar(Q.concatenar(antes, [marco_preparo(nativa)]), meio), Con{marco_preparo(fixa), depois}),
              Q.concatenar(Q.concatenar(antes, [marco_preparo(nativa)]), Q.concatenar(meio, Con{marco_preparo(fixa), depois})),
              Q.concatenar_assoc(Q.concatenar(antes, [marco_preparo(nativa)]), meio, Con{marco_preparo(fixa), depois})),
            Equal.trans(Nat, t, Nat.add(Q.tamanho(Q.concatenar(antes, [marco_preparo(nativa)])), i), Nat.add(Q.tamanho(Q.concatenar(Q.concatenar(antes, [marco_preparo(nativa)]), meio)), 0n), pos,
              Equal.trans(Nat, Nat.add(Q.tamanho(Q.concatenar(antes, [marco_preparo(nativa)])), i), Nat.add(Q.tamanho(Q.concatenar(antes, [marco_preparo(nativa)])), Nat.add(Q.tamanho(meio), 0n)),
                Nat.add(Q.tamanho(Q.concatenar(Q.concatenar(antes, [marco_preparo(nativa)]), meio)), 0n),
                Equal.cong(Nat, Nat, z => Nat.add(Q.tamanho(Q.concatenar(antes, [marco_preparo(nativa)])), z), i, Nat.add(Q.tamanho(meio), 0n), tamanho),
                tamanho_somado(Q.concatenar(antes, [marco_preparo(nativa)]), meio, 0n))), quadro, origem_fixa))

def inverter_duas_marcas(~fonte: Fonte.Fonte, ~c: S.Configuracao, +m: R.Micro, -s: D.Estado, +codigo: Fonte.JuizoSintatico,
  +caso: R.Caso, +antes: List<&2, Q.Quadro>, +meio: List<&2, Q.Quadro>, +depois: List<&2, Q.Quadro>,
  +nativa: OrigemPreparo, +fixa: OrigemPreparo, +t: Nat, +r: S.Resposta, +bs: List<&2, U32>,
  sem_antes: SemPreparo(antes), sem_meio: SemPreparo(meio), sem_depois: SemPreparo(depois),
  origem_nativa: PreparoDaOrigem(fonte, c, m, s, codigo, caso, antes, nativa),
  origem_fixa: PreparoDaOrigem(fonte, c, m, s, codigo, caso, Q.concatenar(Q.concatenar(antes, [marco_preparo(nativa)]), meio), fixa),
  consulta: {Q.consultar(Q.concatenar(Q.concatenar(antes, [marco_preparo(nativa)]), Q.concatenar(meio, Con{marco_preparo(fixa), depois})), t) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>}) ->
  PreparoNoTraco(fonte, c, m, s, codigo, caso, Q.concatenar(Q.concatenar(antes, [marco_preparo(nativa)]), Q.concatenar(meio, Con{marco_preparo(fixa), depois})), t, r, bs):
  duas_marcas_pela_parte(fonte, c, m, s, codigo, caso, antes, meio, depois, nativa, fixa, t, r, bs, sem_antes, sem_meio, sem_depois, origem_nativa, origem_fixa,
    Q.dividir_consulta(Q.concatenar(antes, [marco_preparo(nativa)]), Q.concatenar(meio, Con{marco_preparo(fixa), depois}), t, Q.Preparada{r, bs}, consulta))

def depois_entrega_sem_preparo(fecha: Bool, +s: D.Estado, proxima: Bool) -> SemPreparo(R.depois_entrega(fecha, s, proxima)):
  match fecha proxima:
    case True{} _: prefixar_sem_preparo(Q.Fechada{}, Nil{}, {==}, sem_preparo_vazio())
    case False{} True{}: prefixar_sem_preparo(Q.Seguinte{s, s}, Nil{}, {==}, sem_preparo_vazio())
    case False{} False{}: sem_preparo_vazio()

def entrega_sem_preparo(+s: D.Estado, +bs: List<&2, U32>, +fecha: Bool, entrega: R.Entrega) -> SemPreparo(R.render_entrega(s, bs, fecha, entrega)):
  match entrega:
    case R.Completa{proxima}: prefixar_sem_preparo(Q.Entregue{bs}, R.depois_entrega(fecha, s, proxima), {==}, depois_entrega_sem_preparo(fecha, s, proxima))
    case R.Quebrada{+prefixo}: prefixar_sem_preparo(Q.Interrompida{prefixo}, [Q.Fechada{}], {==}, prefixar_sem_preparo(Q.Fechada{}, Nil{}, {==}, sem_preparo_vazio()))
    case R.PendenteEntrega{}: sem_preparo_vazio()

def publicacao_sem_preparo(r: S.Resposta, +s: D.Estado) -> SemPreparo(R.render_publicacao(r, s)):
  match r:
    case S.Resposta{S.Sucesso{}, v}: prefixar_sem_preparo(Q.Publicada{s}, Nil{}, {==}, sem_preparo_vazio())
    case S.Resposta{S.Recusa{}, v}: sem_preparo_vazio()
    case S.Resposta{S.Entrada{}, v}: sem_preparo_vazio()
    case S.Resposta{S.Autenticacao{}, v}: sem_preparo_vazio()
    case S.Resposta{S.Certificado{}, v}: sem_preparo_vazio()
    case S.Resposta{S.Dados{}, v}: sem_preparo_vazio()
    case S.Resposta{S.Limite{}, v}: sem_preparo_vazio()
    case S.Resposta{S.Falha{}, v}: sem_preparo_vazio()

def cauda_da_conclusao(conclusao: N.Conclusao, +fecha: Bool, entrega: R.Entrega) -> List<&2, Q.Quadro>:
  match conclusao:
    case N.Conclusao{+s, +r, +bs}: Q.concatenar(R.render_publicacao(r, s), Con{Q.Concluida{r, s, fecha}, R.render_entrega(s, bs, fecha, entrega)})

def cauda_da_conclusao_sem_preparo(conclusao: N.Conclusao, +fecha: Bool, entrega: R.Entrega) -> SemPreparo(cauda_da_conclusao(conclusao, fecha, entrega)):
  match conclusao:
    case N.Conclusao{+s, +r, +bs}:
      concatenar_sem_preparo(R.render_publicacao(r, s), Con{Q.Concluida{r, s, fecha}, R.render_entrega(s, bs, fecha, entrega)}, publicacao_sem_preparo(r, s),
        prefixar_sem_preparo(Q.Concluida{r, s, fecha}, R.render_entrega(s, bs, fecha, entrega), {==}, entrega_sem_preparo(s, bs, fecha, entrega)))

def inicial_sem_preparo(q: Maybe<&2, List<&2, U32>>, +s: D.Estado) -> SemPreparo(R.render_inicial(q, s)):
  match q:
    case None{}: prefixar_sem_preparo(Q.Codificada{D.estado_valor(s), None{}}, Nil{}, {==}, sem_preparo_vazio())
    case Some{+bs}: prefixar_sem_preparo(Q.Codificada{D.estado_valor(s), Some{bs}}, [Q.Guardada{s, bs, s}, Q.Iniciada{s}], {==},
      prefixar_sem_preparo(Q.Guardada{s, bs, s}, [Q.Iniciada{s}], {==}, prefixar_sem_preparo(Q.Iniciada{s}, Nil{}, {==}, sem_preparo_vazio())))

def prefixo_inicial_sem_preparo(+m: R.Micro, aceita: Bool) -> SemPreparo(R.prefixo_inicial(m, aceita)):
  match aceita:
    case True{}: prefixar_sem_preparo(Q.InicialAceita{}, R.micro_saida(m), {==}, saida_sem_preparo(m))
    case False{}: sem_preparo_vazio()

def fase_sem_preparo_ou_nativa(~fonte: Fonte.Fonte, ~c: S.Configuracao, +m: R.Micro, -s: D.Estado, +codigo: Fonte.JuizoSintatico,
  +fase: R.FaseAntes, real: Cinco.FaseReal(fonte, c, s, codigo, fase)) ->
  L.Ou<SemPreparo(R.render_fase(m, fase)),
    &r: P.Requisicao -> &ctx: D.Contexto -> &xs: List<&2, Q.QuadroExec> -> &p: N.Preparada ->
      L.E<{fase == R.AposPreparar{r, ctx, xs, p} : R.FaseAntes}, Fonte.FinalReal(fonte, c, s, r, ctx, codigo, xs, p)>>:
  match fase:
    case R.AntesEntrada{}: L.Esquerda{entrada_sem_preparo(m)}
    case R.AposReceber{r}: L.Esquerda{recebida_sem_preparo(m, r)}
    case R.AposAutenticar{r, ctx}: L.Esquerda{autenticada_sem_preparo(m, r, ctx)}
    case R.AposVerificar{r, ctx}: L.Esquerda{verificada_sem_preparo(m, r, ctx)}
    case R.Executando{r, ctx, xs}: L.Esquerda{execucao_sem_preparo(m, r, ctx, xs)}
    case R.AposPreparar{r, ctx, xs, p}: L.Direita{(r, ctx, xs, p, L.Ambos{{==}, real})}

def agrupar_preparo_nativo(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>, +marca: Q.Quadro, +depois: List<&2, Q.Quadro>) ->
  {Con{Q.Configurada{}, Q.concatenar(R.render_execucao(m, r, ctx, xs), Q.concatenar(R.micro_saida(m), Con{marca, depois}))} ==
    Q.concatenar(Con{Q.Configurada{}, antes_execucao(m, r, ctx, xs)}, Con{marca, depois}) : List<&2, Q.Quadro>}:
  Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, qs => Con{Q.Configurada{}, qs},
    Q.concatenar(R.render_execucao(m, r, ctx, xs), Q.concatenar(R.micro_saida(m), Con{marca, depois})),
    Q.concatenar(antes_execucao(m, r, ctx, xs), Con{marca, depois}),
    Equal.sym(List<&2, Q.Quadro>, Q.concatenar(antes_execucao(m, r, ctx, xs), Con{marca, depois}),
      Q.concatenar(R.render_execucao(m, r, ctx, xs), Q.concatenar(R.micro_saida(m), Con{marca, depois})),
      Q.concatenar_assoc(R.render_execucao(m, r, ctx, xs), R.micro_saida(m), Con{marca, depois})))

def refletir_inversao_preparo(~fonte: Fonte.Fonte, ~c: S.Configuracao, +m: R.Micro, -s: D.Estado, +codigo: Fonte.JuizoSintatico,
  +caso: R.Caso, +qs: List<&2, Q.Quadro>, +normal: List<&2, Q.Quadro>, +t: Nat, +r: S.Resposta, +bs: List<&2, U32>,
  +igual: {qs == normal : List<&2, Q.Quadro>}, consulta: {Q.consultar(qs, t) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>},
  resolver: {Q.consultar(normal, t) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>} -> PreparoNoTraco(fonte, c, m, s, codigo, caso, normal, t, r, bs)) ->
  PreparoNoTraco(fonte, c, m, s, codigo, caso, qs, t, r, bs):
  %Equal.sym(List<&2, Q.Quadro>, qs, normal, igual) : PreparoNoTraco(fonte, c, m, s, codigo, caso, _, t, r, bs)
  resolver(%igual : {Q.consultar(_, t) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>} consulta)
def inverter_preparo_nativo(~fonte: Fonte.Fonte, ~c: S.Configuracao, +m: R.Micro, +s: D.Estado, +codigo: Fonte.JuizoSintatico,
  +caso: R.Caso, +qs: List<&2, Q.Quadro>, +req: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>, +p: N.Preparada,
  +depois: List<&2, Q.Quadro>, +t: Nat, +r: S.Resposta, +bs: List<&2, U32>,
  real: Fonte.FinalReal(fonte, c, s, req, ctx, codigo, xs, p),
  igual: {qs == Q.concatenar(Con{Q.Configurada{}, antes_execucao(m, req, ctx, xs)}, Con{R.quadro_preparada(p), depois}) : List<&2, Q.Quadro>},
  sem_depois: SemPreparo(depois), consulta: {Q.consultar(qs, t) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>}) ->
  PreparoNoTraco(fonte, c, m, s, codigo, caso, qs, t, r, bs):
  refletir_inversao_preparo(fonte, c, m, s, codigo, caso, qs,
    Q.concatenar(Con{Q.Configurada{}, antes_execucao(m, req, ctx, xs)}, Con{R.quadro_preparada(p), depois}), t, r, bs, igual, consulta,
    normal => inverter_marca_de_preparo(fonte, c, m, s, codigo, caso, Con{Q.Configurada{}, antes_execucao(m, req, ctx, xs)}, depois,
      Nativo{req, ctx, xs, p}, t, r, bs, antes_execucao_sem_preparo(m, req, ctx, xs), sem_depois, L.Ambos{{==}, real}, normal))

def cauda_do_erro(+s: D.Estado, +e: Erros.Erro, +fecha: Bool, entrega: R.Entrega) -> List<&2, Q.Quadro>:
  Con{Q.Concluida{S.resposta_erro(Erros.status(e)), s, fecha}, R.render_entrega(s, Erros.bytes(e), fecha, entrega)}

def cauda_do_erro_sem_preparo(+s: D.Estado, +e: Erros.Erro, +fecha: Bool, entrega: R.Entrega) -> SemPreparo(cauda_do_erro(s, e, fecha, entrega)):
  prefixar_sem_preparo(Q.Concluida{S.resposta_erro(Erros.status(e)), s, fecha}, R.render_entrega(s, Erros.bytes(e), fecha, entrega), {==}, entrega_sem_preparo(s, Erros.bytes(e), fecha, entrega))

def normalizar_erro_preparo(+antes: List<&2, Q.Quadro>, +s: D.Estado, +e: Erros.Erro, +fecha: Bool, +entrega: R.Entrega) ->
  {Q.concatenar(antes, R.render_erro(Erros.status(e), s, fecha, entrega)) == Q.concatenar(antes, Con{marco_preparo(Fixo{e}), cauda_do_erro(s, e, fecha, entrega)}) : List<&2, Q.Quadro>}:
  Equal.cong(Maybe<&2, List<&2, U32>>, List<&2, Q.Quadro>, q => Q.concatenar(antes, R.render_erro_enquadrado(q, S.resposta_erro(Erros.status(e)), s, fecha, entrega)),
    P.enquadrar(S.resposta_valor(S.resposta_erro(Erros.status(e)))), Some{Erros.bytes(e)}, Erros.todos_os_erros_preparados_sao_exatamente_mensagens_originais(e))

def inverter_preparo_fixo(~fonte: Fonte.Fonte, ~c: S.Configuracao, +m: R.Micro, +s: D.Estado, +codigo: Fonte.JuizoSintatico,
  +caso: R.Caso, +qs: List<&2, Q.Quadro>, +antes: List<&2, Q.Quadro>, +e: Erros.Erro, +fecha: Bool, +entrega: R.Entrega, +t: Nat, +r: S.Resposta, +bs: List<&2, U32>,
  causa: FixoDoCaso(e, caso), prefixo: PrefixoFixo(m, caso, antes), sem_antes: SemPreparo(antes),
  igual: {qs == Q.concatenar(antes, R.render_erro(Erros.status(e), s, fecha, entrega)) : List<&2, Q.Quadro>},
  consulta: {Q.consultar(qs, t) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>}) -> PreparoNoTraco(fonte, c, m, s, codigo, caso, qs, t, r, bs):
  refletir_inversao_preparo(fonte, c, m, s, codigo, caso, qs, Q.concatenar(antes, Con{marco_preparo(Fixo{e}), cauda_do_erro(s, e, fecha, entrega)}), t, r, bs,
    Equal.trans(List<&2, Q.Quadro>, qs, Q.concatenar(antes, R.render_erro(Erros.status(e), s, fecha, entrega)),
      Q.concatenar(antes, Con{marco_preparo(Fixo{e}), cauda_do_erro(s, e, fecha, entrega)}), igual, normalizar_erro_preparo(antes, s, e, fecha, entrega)), consulta,
    normal => inverter_marca_de_preparo(fonte, c, m, s, codigo, caso, antes, cauda_do_erro(s, e, fecha, entrega), Fixo{e}, t, r, bs,
      sem_antes, cauda_do_erro_sem_preparo(s, e, fecha, entrega), L.Ambos{causa, prefixo}, normal))

def agrupar_fase_preparada(+m: R.Micro, +req: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>, +p: N.Preparada, +depois: List<&2, Q.Quadro>) ->
  {Con{Q.Configurada{}, Q.concatenar(R.render_fase(m, R.AposPreparar{req, ctx, xs, p}), depois)} ==
    Q.concatenar(Con{Q.Configurada{}, antes_execucao(m, req, ctx, xs)}, Con{R.quadro_preparada(p), depois}) : List<&2, Q.Quadro>}:
  Equal.trans(List<&2, Q.Quadro>, Con{Q.Configurada{}, Q.concatenar(R.render_fase(m, R.AposPreparar{req, ctx, xs, p}), depois)},
    Con{Q.Configurada{}, Q.concatenar(R.render_execucao(m, req, ctx, xs), Q.concatenar(R.micro_saida(m), Con{R.quadro_preparada(p), depois}))},
    Q.concatenar(Con{Q.Configurada{}, antes_execucao(m, req, ctx, xs)}, Con{R.quadro_preparada(p), depois}),
    Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, qs => Con{Q.Configurada{}, qs},
      Q.concatenar(R.render_fase(m, R.AposPreparar{req, ctx, xs, p}), depois),
      Q.concatenar(R.render_execucao(m, req, ctx, xs), Q.concatenar(R.micro_saida(m), Con{R.quadro_preparada(p), depois})),
      agrupar_tres(R.render_execucao(m, req, ctx, xs), R.micro_saida(m), [R.quadro_preparada(p)], depois)),
    agrupar_preparo_nativo(m, req, ctx, xs, R.quadro_preparada(p), depois))

def inverter_fase_pela_origem(~fonte: Fonte.Fonte, ~c: S.Configuracao, +m: R.Micro, +s: D.Estado, +codigo: Fonte.JuizoSintatico,
  +caso: R.Caso, +fase: R.FaseAntes, +depois: List<&2, Q.Quadro>, +t: Nat, +r: S.Resposta, +bs: List<&2, U32>, sem_depois: SemPreparo(depois),
  origem: L.Ou<SemPreparo(R.render_fase(m, fase)),
    &req: P.Requisicao -> &ctx: D.Contexto -> &xs: List<&2, Q.QuadroExec> -> &p: N.Preparada -> L.E<{fase == R.AposPreparar{req, ctx, xs, p} : R.FaseAntes}, Fonte.FinalReal(fonte, c, s, req, ctx, codigo, xs, p)>>,
  consulta: {Q.consultar(Con{Q.Configurada{}, Q.concatenar(R.render_fase(m, fase), depois)}, t) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>}) ->
  PreparoNoTraco(fonte, c, m, s, codigo, caso, Con{Q.Configurada{}, Q.concatenar(R.render_fase(m, fase), depois)}, t, r, bs):
  match origem:
    case L.Esquerda{sem_fase}:
      L.ex_falso(PreparoNoTraco(fonte, c, m, s, codigo, caso, Con{Q.Configurada{}, Q.concatenar(R.render_fase(m, fase), depois)}, t, r, bs),
        prefixar_sem_preparo(Q.Configurada{}, Q.concatenar(R.render_fase(m, fase), depois), {==}, concatenar_sem_preparo(R.render_fase(m, fase), depois, sem_fase, sem_depois))(r, bs, t, consulta))
    case L.Direita{(+req, +ctx, +xs, +p, L.Ambos{igual, real})}:
      inverter_preparo_nativo(fonte, c, m, s, codigo, caso, Con{Q.Configurada{}, Q.concatenar(R.render_fase(m, fase), depois)}, req, ctx, xs, p, depois, t, r, bs, real,
        Equal.trans(List<&2, Q.Quadro>, Con{Q.Configurada{}, Q.concatenar(R.render_fase(m, fase), depois)},
          Con{Q.Configurada{}, Q.concatenar(R.render_fase(m, R.AposPreparar{req, ctx, xs, p}), depois)},
          Q.concatenar(Con{Q.Configurada{}, antes_execucao(m, req, ctx, xs)}, Con{R.quadro_preparada(p), depois}),
          Equal.cong(R.FaseAntes, List<&2, Q.Quadro>, f => Con{Q.Configurada{}, Q.concatenar(R.render_fase(m, f), depois)}, fase, R.AposPreparar{req, ctx, xs, p}, igual),
          agrupar_fase_preparada(m, req, ctx, xs, p, depois)), sem_depois, consulta)

def inverter_preparo_da_fase(~fonte: Fonte.Fonte, ~c: S.Configuracao, +m: R.Micro, +s: D.Estado, +codigo: Fonte.JuizoSintatico,
  +caso: R.Caso, +fase: R.FaseAntes, +depois: List<&2, Q.Quadro>, +t: Nat, +r: S.Resposta, +bs: List<&2, U32>,
  real: Cinco.FaseReal(fonte, c, s, codigo, fase), sem_depois: SemPreparo(depois),
  consulta: {Q.consultar(Con{Q.Configurada{}, Q.concatenar(R.render_fase(m, fase), depois)}, t) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>}) ->
  PreparoNoTraco(fonte, c, m, s, codigo, caso, Con{Q.Configurada{}, Q.concatenar(R.render_fase(m, fase), depois)}, t, r, bs):
  inverter_fase_pela_origem(fonte, c, m, s, codigo, caso, fase, depois, t, r, bs, sem_depois, fase_sem_preparo_ou_nativa(fonte, c, m, s, codigo, fase, real), consulta)

def antes_auth_sem_preparo(+m: R.Micro, +req: P.Requisicao) -> SemPreparo(Con{Q.Configurada{}, antes_autenticacao(m, req)}):
  prefixar_sem_preparo(Q.Configurada{}, antes_autenticacao(m, req), {==},
    concatenar_sem_preparo(R.render_recebida(m, req), Q.concatenar(R.micro_autenticacao(m), [Q.Autenticada{req, None{}}]), recebida_sem_preparo(m, req),
      concatenar_sem_preparo(R.micro_autenticacao(m), [Q.Autenticada{req, None{}}], autenticacao_sem_preparo(m), prefixar_sem_preparo(Q.Autenticada{req, None{}}, Nil{}, {==}, sem_preparo_vazio()))))

def antes_gate_sem_preparo(+m: R.Micro, +req: P.Requisicao, +ctx: D.Contexto) -> SemPreparo(Con{Q.Configurada{}, antes_gate(m, req, ctx)}):
  prefixar_sem_preparo(Q.Configurada{}, antes_gate(m, req, ctx), {==},
    concatenar_sem_preparo(R.render_autenticada(m, req, ctx), [Q.Rejeitada{req, ctx}], autenticada_sem_preparo(m, req, ctx), prefixar_sem_preparo(Q.Rejeitada{req, ctx}, Nil{}, {==}, sem_preparo_vazio())))

def inverter_preparo_executado(~fonte: Fonte.Fonte, ~c: S.Configuracao, +m: R.Micro, +s: D.Estado, +codigo: Fonte.JuizoSintatico,
  +req: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>, p: N.Preparada, +entrega: R.Entrega, +t: Nat, +r: S.Resposta, +bs: List<&2, U32>,
  real: Fonte.FinalReal(fonte, c, s, req, ctx, codigo, xs, p),
  consulta: {Q.consultar(R.render(m, s, R.Executada{req, ctx, xs, p, entrega}), t) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>}) ->
  PreparoNoTraco(fonte, c, m, s, codigo, R.Executada{req, ctx, xs, p, entrega}, R.render(m, s, R.Executada{req, ctx, xs, p, entrega}), t, r, bs):
  match p:
    case N.Preparada{+w, +ts, +resp, +bytes}:
      inverter_preparo_nativo(fonte, c, m, s, codigo, R.Executada{req, ctx, xs, N.Preparada{w, ts, resp, bytes}, entrega},
        R.render(m, s, R.Executada{req, ctx, xs, N.Preparada{w, ts, resp, bytes}, entrega}), req, ctx, xs, N.Preparada{w, ts, resp, bytes},
        cauda_da_conclusao(N.concluir(N.Preparada{w, ts, resp, bytes}, s), False{}, entrega), t, r, bs, real,
        agrupar_preparo_nativo(m, req, ctx, xs, Q.Preparada{resp, bytes}, cauda_da_conclusao(N.concluir(N.Preparada{w, ts, resp, bytes}, s), False{}, entrega)),
        cauda_da_conclusao_sem_preparo(N.concluir(N.Preparada{w, ts, resp, bytes}, s), False{}, entrega), consulta)

def cauda_fatal(conclusao: N.Conclusao, +etapa: X.Etapa, +id: String) -> List<&2, Q.Quadro>:
  match conclusao:
    case N.Conclusao{+s, r, bs}: Q.concatenar(R.render_publicacao(r, s), [Q.Falhou{etapa, id, True{}}, Q.Fechada{}])

def cauda_fatal_sem_preparo(conclusao: N.Conclusao, +etapa: X.Etapa, +id: String) -> SemPreparo(cauda_fatal(conclusao, etapa, id)):
  match conclusao:
    case N.Conclusao{+s, +r, bs}:
      concatenar_sem_preparo(R.render_publicacao(r, s), [Q.Falhou{etapa, id, True{}}, Q.Fechada{}], publicacao_sem_preparo(r, s),
        prefixar_sem_preparo(Q.Falhou{etapa, id, True{}}, [Q.Fechada{}], {==}, prefixar_sem_preparo(Q.Fechada{}, Nil{}, {==}, sem_preparo_vazio())))

def inverter_preparo_fatal_publicada(~fonte: Fonte.Fonte, ~c: S.Configuracao, +m: R.Micro, +s: D.Estado, +codigo: Fonte.JuizoSintatico,
  +req: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>, p: N.Preparada, +etapa: X.Etapa, +id: String, +t: Nat, +r: S.Resposta, +bs: List<&2, U32>,
  real: Fonte.FinalReal(fonte, c, s, req, ctx, codigo, xs, p),
  consulta: {Q.consultar(R.render(m, s, R.FatalAposPublicacao{req, ctx, xs, p, etapa, id}), t) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>}) ->
  PreparoNoTraco(fonte, c, m, s, codigo, R.FatalAposPublicacao{req, ctx, xs, p, etapa, id}, R.render(m, s, R.FatalAposPublicacao{req, ctx, xs, p, etapa, id}), t, r, bs):
  match p:
    case N.Preparada{+w, +ts, +resp, +bytes}:
      inverter_preparo_nativo(fonte, c, m, s, codigo, R.FatalAposPublicacao{req, ctx, xs, N.Preparada{w, ts, resp, bytes}, etapa, id},
        R.render(m, s, R.FatalAposPublicacao{req, ctx, xs, N.Preparada{w, ts, resp, bytes}, etapa, id}), req, ctx, xs, N.Preparada{w, ts, resp, bytes},
        cauda_fatal(N.concluir(N.Preparada{w, ts, resp, bytes}, s), etapa, id), t, r, bs, real,
        agrupar_preparo_nativo(m, req, ctx, xs, Q.Preparada{resp, bytes}, cauda_fatal(N.concluir(N.Preparada{w, ts, resp, bytes}, s), etapa, id)),
        cauda_fatal_sem_preparo(N.concluir(N.Preparada{w, ts, resp, bytes}, s), etapa, id), consulta)

def status_erro_da_entrada(e: R.ErroEntrada) -> {R.status_entrada(e) == Erros.status(erro_da_entrada(e)) : S.Status}:
  match e:
    case R.Entrada{}: {==}
    case R.Limite{}: {==}

def inverter_preparo_entrada(~fonte: Fonte.Fonte, ~c: S.Configuracao, +m: R.Micro, +s: D.Estado, +codigo: Fonte.JuizoSintatico,
  +e: R.ErroEntrada, +fecha: Bool, +entrega: R.Entrega, +t: Nat, +r: S.Resposta, +bs: List<&2, U32>,
  consulta: {Q.consultar(R.render(m, s, R.EntradaRecusa{e, fecha, entrega}), t) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>}) ->
  PreparoNoTraco(fonte, c, m, s, codigo, R.EntradaRecusa{e, fecha, entrega}, R.render(m, s, R.EntradaRecusa{e, fecha, entrega}), t, r, bs):
  inverter_preparo_fixo(fonte, c, m, s, codigo, R.EntradaRecusa{e, fecha, entrega}, R.render(m, s, R.EntradaRecusa{e, fecha, entrega}),
    Con{Q.Configurada{}, R.micro_entrada(m)}, erro_da_entrada(e), fecha, entrega, t, r, bs, {==}, {==}, prefixar_sem_preparo(Q.Configurada{}, R.micro_entrada(m), {==}, entrada_sem_preparo(m)),
    Equal.cong(S.Status, List<&2, Q.Quadro>, status => Con{Q.Configurada{}, Q.concatenar(R.micro_entrada(m), R.render_erro(status, s, fecha, entrega))}, R.status_entrada(e), Erros.status(erro_da_entrada(e)), status_erro_da_entrada(e)), consulta)

def inverter_preparo_aut(~fonte: Fonte.Fonte, ~c: S.Configuracao, +m: R.Micro, +s: D.Estado, +codigo: Fonte.JuizoSintatico,
  +req: P.Requisicao, +entrega: R.Entrega, +t: Nat, +r: S.Resposta, +bs: List<&2, U32>,
  consulta: {Q.consultar(R.render(m, s, R.AutRecusa{req, entrega}), t) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>}) ->
  PreparoNoTraco(fonte, c, m, s, codigo, R.AutRecusa{req, entrega}, R.render(m, s, R.AutRecusa{req, entrega}), t, r, bs):
  inverter_preparo_fixo(fonte, c, m, s, codigo, R.AutRecusa{req, entrega}, R.render(m, s, R.AutRecusa{req, entrega}), Con{Q.Configurada{}, antes_autenticacao(m, req)},
    Erros.Autenticacao{}, False{}, entrega, t, r, bs, {==}, {==}, antes_auth_sem_preparo(m, req),
    Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, qs => Con{Q.Configurada{}, qs},
      R.render_caso(m, s, R.AutRecusa{req, entrega}), Q.concatenar(antes_autenticacao(m, req), R.render_erro(S.Autenticacao{}, s, False{}, entrega)),
      Equal.sym(List<&2, Q.Quadro>, Q.concatenar(antes_autenticacao(m, req), R.render_erro(S.Autenticacao{}, s, False{}, entrega)), R.render_caso(m, s, R.AutRecusa{req, entrega}),
        agrupar_tres(R.render_recebida(m, req), R.micro_autenticacao(m), [Q.Autenticada{req, None{}}], R.render_erro(S.Autenticacao{}, s, False{}, entrega)))), consulta)

def inverter_preparo_gate(~fonte: Fonte.Fonte, ~c: S.Configuracao, +m: R.Micro, +s: D.Estado, +codigo: Fonte.JuizoSintatico,
  +req: P.Requisicao, +ctx: D.Contexto, +entrega: R.Entrega, +t: Nat, +r: S.Resposta, +bs: List<&2, U32>,
  consulta: {Q.consultar(R.render(m, s, R.GateRecusa{req, ctx, entrega}), t) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>}) ->
  PreparoNoTraco(fonte, c, m, s, codigo, R.GateRecusa{req, ctx, entrega}, R.render(m, s, R.GateRecusa{req, ctx, entrega}), t, r, bs):
  inverter_preparo_fixo(fonte, c, m, s, codigo, R.GateRecusa{req, ctx, entrega}, R.render(m, s, R.GateRecusa{req, ctx, entrega}), Con{Q.Configurada{}, antes_gate(m, req, ctx)},
    Erros.Certificado{}, False{}, entrega, t, r, bs, {==}, {==}, antes_gate_sem_preparo(m, req, ctx),
    Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, qs => Con{Q.Configurada{}, qs},
      R.render_caso(m, s, R.GateRecusa{req, ctx, entrega}), Q.concatenar(antes_gate(m, req, ctx), R.render_erro(S.Certificado{}, s, False{}, entrega)),
      Equal.sym(List<&2, Q.Quadro>, Q.concatenar(antes_gate(m, req, ctx), R.render_erro(S.Certificado{}, s, False{}, entrega)), R.render_caso(m, s, R.GateRecusa{req, ctx, entrega}),
        Q.concatenar_assoc(R.render_autenticada(m, req, ctx), [Q.Rejeitada{req, ctx}], R.render_erro(S.Certificado{}, s, False{}, entrega)))), consulta)

def prefixo_fixo_da_falha_dupla(+m: R.Micro, +fase: R.FaseAntes, +req: P.Requisicao, +ctx: D.Contexto,
  +xs: List<&2, Q.QuadroExec>, +p: N.Preparada, +etapa: X.Etapa, +id: String, +entrega: R.Entrega,
  fase_igual: {fase == R.AposPreparar{req, ctx, xs, p} : R.FaseAntes}) ->
  PrefixoFixo(m, R.FalhaAntes{fase, etapa, id, False{}, entrega},
    Q.concatenar(Q.concatenar(Con{Q.Configurada{}, antes_execucao(m, req, ctx, xs)}, [R.quadro_preparada(p)]), [Q.Falhou{etapa, id, False{}}])):
  Equal.trans(List<&2, Q.Quadro>,
    Q.concatenar(Q.concatenar(Con{Q.Configurada{}, antes_execucao(m, req, ctx, xs)}, [R.quadro_preparada(p)]), [Q.Falhou{etapa, id, False{}}]),
    Q.concatenar(Con{Q.Configurada{}, antes_execucao(m, req, ctx, xs)}, [R.quadro_preparada(p), Q.Falhou{etapa, id, False{}}]),
    Con{Q.Configurada{}, antes_falha(m, fase, etapa, id, False{})},
    Q.concatenar_assoc(Con{Q.Configurada{}, antes_execucao(m, req, ctx, xs)}, [R.quadro_preparada(p)], [Q.Falhou{etapa, id, False{}}]),
    Equal.sym(List<&2, Q.Quadro>, Con{Q.Configurada{}, antes_falha(m, fase, etapa, id, False{})},
      Q.concatenar(Con{Q.Configurada{}, antes_execucao(m, req, ctx, xs)}, [R.quadro_preparada(p), Q.Falhou{etapa, id, False{}}]),
      Equal.trans(List<&2, Q.Quadro>, Con{Q.Configurada{}, antes_falha(m, fase, etapa, id, False{})},
        Con{Q.Configurada{}, antes_falha(m, R.AposPreparar{req, ctx, xs, p}, etapa, id, False{})},
        Q.concatenar(Con{Q.Configurada{}, antes_execucao(m, req, ctx, xs)}, [R.quadro_preparada(p), Q.Falhou{etapa, id, False{}}]),
        Equal.cong(R.FaseAntes, List<&2, Q.Quadro>, f => Con{Q.Configurada{}, antes_falha(m, f, etapa, id, False{})}, fase, R.AposPreparar{req, ctx, xs, p}, fase_igual),
        agrupar_fase_preparada(m, req, ctx, xs, p, [Q.Falhou{etapa, id, False{}}]))))

def normalizar_falha_dupla(+m: R.Micro, +s: D.Estado, +req: P.Requisicao, +ctx: D.Contexto,
  +xs: List<&2, Q.QuadroExec>, +p: N.Preparada, +etapa: X.Etapa, +id: String, +entrega: R.Entrega) ->
  {R.render(m, s, R.FalhaAntes{R.AposPreparar{req, ctx, xs, p}, etapa, id, False{}, entrega}) ==
    Q.concatenar(Q.concatenar(Con{Q.Configurada{}, antes_execucao(m, req, ctx, xs)}, [R.quadro_preparada(p)]),
      Con{Q.Falhou{etapa, id, False{}}, Con{marco_preparo(Fixo{Erros.Falha{}}), cauda_do_erro(s, Erros.Falha{}, False{}, entrega)}}) : List<&2, Q.Quadro>}:
  Equal.trans(List<&2, Q.Quadro>, R.render(m, s, R.FalhaAntes{R.AposPreparar{req, ctx, xs, p}, etapa, id, False{}, entrega}),
    Con{Q.Configurada{}, Q.concatenar(R.render_fase(m, R.AposPreparar{req, ctx, xs, p}),
      Con{Q.Falhou{etapa, id, False{}}, Con{marco_preparo(Fixo{Erros.Falha{}}), cauda_do_erro(s, Erros.Falha{}, False{}, entrega)}})},
    Q.concatenar(Q.concatenar(Con{Q.Configurada{}, antes_execucao(m, req, ctx, xs)}, [R.quadro_preparada(p)]),
      Con{Q.Falhou{etapa, id, False{}}, Con{marco_preparo(Fixo{Erros.Falha{}}), cauda_do_erro(s, Erros.Falha{}, False{}, entrega)}}),
    Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, tail => Con{Q.Configurada{}, Q.concatenar(R.render_fase(m, R.AposPreparar{req, ctx, xs, p}), Con{Q.Falhou{etapa, id, False{}}, tail})},
      R.render_erro(S.Falha{}, s, False{}, entrega), Con{marco_preparo(Fixo{Erros.Falha{}}), cauda_do_erro(s, Erros.Falha{}, False{}, entrega)}, normalizar_erro_preparo(Nil{}, s, Erros.Falha{}, False{}, entrega)),
    Equal.trans(List<&2, Q.Quadro>, Con{Q.Configurada{}, Q.concatenar(R.render_fase(m, R.AposPreparar{req, ctx, xs, p}), Con{Q.Falhou{etapa, id, False{}}, Con{marco_preparo(Fixo{Erros.Falha{}}), cauda_do_erro(s, Erros.Falha{}, False{}, entrega)}})},
      Q.concatenar(Con{Q.Configurada{}, antes_execucao(m, req, ctx, xs)}, Con{R.quadro_preparada(p), Con{Q.Falhou{etapa, id, False{}}, Con{marco_preparo(Fixo{Erros.Falha{}}), cauda_do_erro(s, Erros.Falha{}, False{}, entrega)}}}),
      Q.concatenar(Q.concatenar(Con{Q.Configurada{}, antes_execucao(m, req, ctx, xs)}, [R.quadro_preparada(p)]), Con{Q.Falhou{etapa, id, False{}}, Con{marco_preparo(Fixo{Erros.Falha{}}), cauda_do_erro(s, Erros.Falha{}, False{}, entrega)}}),
      agrupar_fase_preparada(m, req, ctx, xs, p, Con{Q.Falhou{etapa, id, False{}}, Con{marco_preparo(Fixo{Erros.Falha{}}), cauda_do_erro(s, Erros.Falha{}, False{}, entrega)}}),
      Equal.sym(List<&2, Q.Quadro>, Q.concatenar(Q.concatenar(Con{Q.Configurada{}, antes_execucao(m, req, ctx, xs)}, [R.quadro_preparada(p)]), Con{Q.Falhou{etapa, id, False{}}, Con{marco_preparo(Fixo{Erros.Falha{}}), cauda_do_erro(s, Erros.Falha{}, False{}, entrega)}}),
        Q.concatenar(Con{Q.Configurada{}, antes_execucao(m, req, ctx, xs)}, Con{R.quadro_preparada(p), Con{Q.Falhou{etapa, id, False{}}, Con{marco_preparo(Fixo{Erros.Falha{}}), cauda_do_erro(s, Erros.Falha{}, False{}, entrega)}}}),
        Q.concatenar_assoc(Con{Q.Configurada{}, antes_execucao(m, req, ctx, xs)}, [R.quadro_preparada(p)], Con{Q.Falhou{etapa, id, False{}}, Con{marco_preparo(Fixo{Erros.Falha{}}), cauda_do_erro(s, Erros.Falha{}, False{}, entrega)}}))))

def inverter_falha_dupla(~fonte: Fonte.Fonte, ~c: S.Configuracao, +m: R.Micro, +s: D.Estado, +codigo: Fonte.JuizoSintatico,
  +fase: R.FaseAntes, +req: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>, +p: N.Preparada,
  +etapa: X.Etapa, +id: String, +entrega: R.Entrega, +t: Nat, +r: S.Resposta, +bs: List<&2, U32>,
  +fase_igual: {fase == R.AposPreparar{req, ctx, xs, p} : R.FaseAntes}, real: Fonte.FinalReal(fonte, c, s, req, ctx, codigo, xs, p),
  consulta: {Q.consultar(R.render(m, s, R.FalhaAntes{fase, etapa, id, False{}, entrega}), t) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>}) ->
  PreparoNoTraco(fonte, c, m, s, codigo, R.FalhaAntes{fase, etapa, id, False{}, entrega}, R.render(m, s, R.FalhaAntes{fase, etapa, id, False{}, entrega}), t, r, bs):
  refletir_inversao_preparo(fonte, c, m, s, codigo, R.FalhaAntes{fase, etapa, id, False{}, entrega}, R.render(m, s, R.FalhaAntes{fase, etapa, id, False{}, entrega}),
    Q.concatenar(Q.concatenar(Con{Q.Configurada{}, antes_execucao(m, req, ctx, xs)}, [R.quadro_preparada(p)]),
      Con{Q.Falhou{etapa, id, False{}}, Con{marco_preparo(Fixo{Erros.Falha{}}), cauda_do_erro(s, Erros.Falha{}, False{}, entrega)}}), t, r, bs,
    Equal.trans(List<&2, Q.Quadro>, R.render(m, s, R.FalhaAntes{fase, etapa, id, False{}, entrega}),
      R.render(m, s, R.FalhaAntes{R.AposPreparar{req, ctx, xs, p}, etapa, id, False{}, entrega}),
      Q.concatenar(Q.concatenar(Con{Q.Configurada{}, antes_execucao(m, req, ctx, xs)}, [R.quadro_preparada(p)]), Con{Q.Falhou{etapa, id, False{}}, Con{marco_preparo(Fixo{Erros.Falha{}}), cauda_do_erro(s, Erros.Falha{}, False{}, entrega)}}),
      Equal.cong(R.FaseAntes, List<&2, Q.Quadro>, f => R.render(m, s, R.FalhaAntes{f, etapa, id, False{}, entrega}), fase, R.AposPreparar{req, ctx, xs, p}, fase_igual),
      normalizar_falha_dupla(m, s, req, ctx, xs, p, etapa, id, entrega)), consulta,
    normal => inverter_duas_marcas(fonte, c, m, s, codigo, R.FalhaAntes{fase, etapa, id, False{}, entrega}, Con{Q.Configurada{}, antes_execucao(m, req, ctx, xs)},
      [Q.Falhou{etapa, id, False{}}], cauda_do_erro(s, Erros.Falha{}, False{}, entrega), Nativo{req, ctx, xs, p}, Fixo{Erros.Falha{}}, t, r, bs,
      antes_execucao_sem_preparo(m, req, ctx, xs), prefixar_sem_preparo(Q.Falhou{etapa, id, False{}}, Nil{}, {==}, sem_preparo_vazio()), cauda_do_erro_sem_preparo(s, Erros.Falha{}, False{}, entrega),
      L.Ambos{{==}, real}, L.Ambos{L.Ambos{{==}, {==}}, prefixo_fixo_da_falha_dupla(m, fase, req, ctx, xs, p, etapa, id, entrega, fase_igual)}, normal))

def inverter_falha_pela_origem(~fonte: Fonte.Fonte, ~c: S.Configuracao, +m: R.Micro, +s: D.Estado, +codigo: Fonte.JuizoSintatico,
  +fase: R.FaseAntes, +etapa: X.Etapa, +id: String, +entrega: R.Entrega, +t: Nat, +r: S.Resposta, +bs: List<&2, U32>,
  origem: L.Ou<SemPreparo(R.render_fase(m, fase)), &req: P.Requisicao -> &ctx: D.Contexto -> &xs: List<&2, Q.QuadroExec> -> &p: N.Preparada ->
    L.E<{fase == R.AposPreparar{req, ctx, xs, p} : R.FaseAntes}, Fonte.FinalReal(fonte, c, s, req, ctx, codigo, xs, p)>>,
  consulta: {Q.consultar(R.render(m, s, R.FalhaAntes{fase, etapa, id, False{}, entrega}), t) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>}) ->
  PreparoNoTraco(fonte, c, m, s, codigo, R.FalhaAntes{fase, etapa, id, False{}, entrega}, R.render(m, s, R.FalhaAntes{fase, etapa, id, False{}, entrega}), t, r, bs):
  match origem:
    case L.Esquerda{sem_fase}:
      inverter_preparo_fixo(fonte, c, m, s, codigo, R.FalhaAntes{fase, etapa, id, False{}, entrega}, R.render(m, s, R.FalhaAntes{fase, etapa, id, False{}, entrega}),
        Con{Q.Configurada{}, antes_falha(m, fase, etapa, id, False{})}, Erros.Falha{}, False{}, entrega, t, r, bs, L.Ambos{{==}, {==}}, {==},
        prefixar_sem_preparo(Q.Configurada{}, antes_falha(m, fase, etapa, id, False{}), {==},
          concatenar_sem_preparo(R.render_fase(m, fase), [Q.Falhou{etapa, id, False{}}], sem_fase, prefixar_sem_preparo(Q.Falhou{etapa, id, False{}}, Nil{}, {==}, sem_preparo_vazio()))),
        Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, qs => Con{Q.Configurada{}, qs},
          R.render_caso(m, s, R.FalhaAntes{fase, etapa, id, False{}, entrega}), Q.concatenar(antes_falha(m, fase, etapa, id, False{}), R.render_erro(S.Falha{}, s, False{}, entrega)),
          Equal.sym(List<&2, Q.Quadro>, Q.concatenar(antes_falha(m, fase, etapa, id, False{}), R.render_erro(S.Falha{}, s, False{}, entrega)),
            R.render_caso(m, s, R.FalhaAntes{fase, etapa, id, False{}, entrega}), Q.concatenar_assoc(R.render_fase(m, fase), [Q.Falhou{etapa, id, False{}}], R.render_erro(S.Falha{}, s, False{}, entrega)))), consulta)
    case L.Direita{(+req, +ctx, +xs, +p, L.Ambos{fase_igual, real})}:
      inverter_falha_dupla(fonte, c, m, s, codigo, fase, req, ctx, xs, p, etapa, id, entrega, t, r, bs, fase_igual, real, consulta)

def inverter_preparo_falha(~fonte: Fonte.Fonte, ~c: S.Configuracao, +m: R.Micro, +s: D.Estado, +codigo: Fonte.JuizoSintatico,
  +fase: R.FaseAntes, +etapa: X.Etapa, +id: String, fatal: Bool, +entrega: R.Entrega, +t: Nat, +r: S.Resposta, +bs: List<&2, U32>,
  real: Cinco.FaseReal(fonte, c, s, codigo, fase),
  consulta: {Q.consultar(R.render(m, s, R.FalhaAntes{fase, etapa, id, fatal, entrega}), t) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>}) ->
  PreparoNoTraco(fonte, c, m, s, codigo, R.FalhaAntes{fase, etapa, id, fatal, entrega}, R.render(m, s, R.FalhaAntes{fase, etapa, id, fatal, entrega}), t, r, bs):
  match fatal:
    case True{}:
      inverter_preparo_da_fase(fonte, c, m, s, codigo, R.FalhaAntes{fase, etapa, id, True{}, entrega}, fase, [Q.Falhou{etapa, id, True{}}, Q.Fechada{}], t, r, bs, real,
        prefixar_sem_preparo(Q.Falhou{etapa, id, True{}}, [Q.Fechada{}], {==}, prefixar_sem_preparo(Q.Fechada{}, Nil{}, {==}, sem_preparo_vazio())), consulta)
    case False{}:
      inverter_falha_pela_origem(fonte, c, m, s, codigo, fase, etapa, id, entrega, t, r, bs, fase_sem_preparo_ou_nativa(fonte, c, m, s, codigo, fase, real), consulta)

def inverter_preparo_pendente(~fonte: Fonte.Fonte, ~c: S.Configuracao, +m: R.Micro, +s: D.Estado, +codigo: Fonte.JuizoSintatico,
  +fase: R.FaseAntes, +t: Nat, +r: S.Resposta, +bs: List<&2, U32>, real: Cinco.FaseReal(fonte, c, s, codigo, fase),
  consulta: {Q.consultar(R.render(m, s, R.Pendente{fase}), t) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>}) ->
  PreparoNoTraco(fonte, c, m, s, codigo, R.Pendente{fase}, R.render(m, s, R.Pendente{fase}), t, r, bs):
  refletir_inversao_preparo(fonte, c, m, s, codigo, R.Pendente{fase}, R.render(m, s, R.Pendente{fase}), Con{Q.Configurada{}, Q.concatenar(R.render_fase(m, fase), Nil{})}, t, r, bs,
    Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, qs => Con{Q.Configurada{}, qs}, R.render_fase(m, fase), Q.concatenar(R.render_fase(m, fase), Nil{}),
      Equal.sym(List<&2, Q.Quadro>, Q.concatenar(R.render_fase(m, fase), Nil{}), R.render_fase(m, fase), Cinco.concatenar_vazio_direita(R.render_fase(m, fase)))), consulta,
    normal => inverter_preparo_da_fase(fonte, c, m, s, codigo, R.Pendente{fase}, fase, Nil{}, t, r, bs, real, sem_preparo_vazio(), normal))

def excluir_preparo_sem_marca(~fonte: Fonte.Fonte, ~c: S.Configuracao, +m: R.Micro, -s: D.Estado, +codigo: Fonte.JuizoSintatico,
  +caso: R.Caso, +qs: List<&2, Q.Quadro>, +t: Nat, +r: S.Resposta, +bs: List<&2, U32>, sem: SemPreparo(qs),
  consulta: {Q.consultar(qs, t) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>}) -> PreparoNoTraco(fonte, c, m, s, codigo, caso, qs, t, r, bs):
  L.ex_falso(PreparoNoTraco(fonte, c, m, s, codigo, caso, qs, t, r, bs), sem(r, bs, t, consulta))

# As inicializacoes reutilizam as mesmas exclusoes do inversor abaixo.
def inicial_ok_sem_preparo(+m: R.Micro, +s: D.Estado) -> SemPreparo(R.render(m, s, R.InicialOk{})):
  prefixar_sem_preparo(Q.Configurada{}, R.render_caso(m, s, R.InicialOk{}), {==},
    prefixar_sem_preparo(Q.InicialAceita{}, Q.concatenar(R.micro_saida(m), R.render_inicial(P.codificar(D.estado_valor(s)), s)), {==},
      concatenar_sem_preparo(R.micro_saida(m), R.render_inicial(P.codificar(D.estado_valor(s)), s), saida_sem_preparo(m), inicial_sem_preparo(P.codificar(D.estado_valor(s)), s))))

def inicial_recusa_sem_preparo(+m: R.Micro, +s: D.Estado, +status: S.Status) -> SemPreparo(R.render(m, s, R.InicialRecusa{status})):
  prefixar_sem_preparo(Q.Configurada{}, [Q.InicialRecusada{status}], {==}, prefixar_sem_preparo(Q.InicialRecusada{status}, Nil{}, {==}, sem_preparo_vazio()))

def inicial_falha_sem_preparo(+m: R.Micro, +s: D.Estado, +aceita: Bool, +etapa: X.Etapa, +id: String, +fatal: Bool) ->
  SemPreparo(R.render(m, s, R.InicialFalha{aceita, etapa, id, fatal})):
  prefixar_sem_preparo(Q.Configurada{}, R.render_caso(m, s, R.InicialFalha{aceita, etapa, id, fatal}), {==},
    concatenar_sem_preparo(R.prefixo_inicial(m, aceita), [Q.Falhou{etapa, id, fatal}, Q.InicialRecusada{S.Falha{}}], prefixo_inicial_sem_preparo(m, aceita),
      prefixar_sem_preparo(Q.Falhou{etapa, id, fatal}, [Q.InicialRecusada{S.Falha{}}], {==}, prefixar_sem_preparo(Q.InicialRecusada{S.Falha{}}, Nil{}, {==}, sem_preparo_vazio()))))

def inicial_pendente_sem_preparo(+m: R.Micro, +s: D.Estado, +aceita: Bool) -> SemPreparo(R.render(m, s, R.InicialPendente{aceita})):
  prefixar_sem_preparo(Q.Configurada{}, R.prefixo_inicial(m, aceita), {==}, prefixo_inicial_sem_preparo(m, aceita))

# Cada ocorrencia e originada do caso real, inclusive a preparacao nativa
# anterior ao erro de cleanup. Nao se supoe que a preparacao seja unica.
law inverter_preparo:
  for ~fonte: Fonte.Fonte
  for ~c: S.Configuracao
  for +m: R.Micro
  for +s: D.Estado
  for +codigo: Fonte.JuizoSintatico
  for +caso: R.Caso
  for +t: Nat
  for +r: S.Resposta
  for +bs: List<&2, U32>
  for real: Cinco.CasoReal(fonte, c, s, codigo, caso)
  for consulta: {Q.consultar(R.render(m, s, caso), t) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>}
  PreparoNoTraco(fonte, c, m, s, codigo, caso, R.render(m, s, caso), t, r, bs)
def inverter_preparo(fonte, c, m, s, codigo, caso, t, r, bs, real, consulta):
  match caso:
    case R.InicialOk{}:
      excluir_preparo_sem_marca(fonte, c, m, s, codigo, R.InicialOk{}, R.render(m, s, R.InicialOk{}), t, r, bs,
        inicial_ok_sem_preparo(m, s), consulta)
    case R.InicialRecusa{+status}:
      excluir_preparo_sem_marca(fonte, c, m, s, codigo, R.InicialRecusa{status}, R.render(m, s, R.InicialRecusa{status}), t, r, bs,
        inicial_recusa_sem_preparo(m, s, status), consulta)
    case R.InicialFalha{+aceita, +etapa, +id, +fatal}:
      excluir_preparo_sem_marca(fonte, c, m, s, codigo, R.InicialFalha{aceita, etapa, id, fatal}, R.render(m, s, R.InicialFalha{aceita, etapa, id, fatal}), t, r, bs,
        inicial_falha_sem_preparo(m, s, aceita, etapa, id, fatal), consulta)
    case R.SemResposta{}:
      excluir_preparo_sem_marca(fonte, c, m, s, codigo, R.SemResposta{}, R.render(m, s, R.SemResposta{}), t, r, bs,
        prefixar_sem_preparo(Q.Configurada{}, [Q.Fechada{}], {==}, prefixar_sem_preparo(Q.Fechada{}, Nil{}, {==}, sem_preparo_vazio())), consulta)
    case R.EntradaRecusa{e, fecha, entrega}: inverter_preparo_entrada(fonte, c, m, s, codigo, e, fecha, entrega, t, r, bs, consulta)
    case R.AutRecusa{req, entrega}: inverter_preparo_aut(fonte, c, m, s, codigo, req, entrega, t, r, bs, consulta)
    case R.GateRecusa{req, ctx, entrega}: inverter_preparo_gate(fonte, c, m, s, codigo, req, ctx, entrega, t, r, bs, consulta)
    case R.Executada{req, ctx, xs, p, entrega}: inverter_preparo_executado(fonte, c, m, s, codigo, req, ctx, xs, p, entrega, t, r, bs, real, consulta)
    case R.FalhaAntes{fase, etapa, id, fatal, entrega}: inverter_preparo_falha(fonte, c, m, s, codigo, fase, etapa, id, fatal, entrega, t, r, bs, real, consulta)
    case R.FatalAposPublicacao{req, ctx, xs, p, etapa, id}: inverter_preparo_fatal_publicada(fonte, c, m, s, codigo, req, ctx, xs, p, etapa, id, t, r, bs, real, consulta)
    case R.Pendente{fase}: inverter_preparo_pendente(fonte, c, m, s, codigo, fase, t, r, bs, real, consulta)
    case R.InicialPendente{+aceita}:
      excluir_preparo_sem_marca(fonte, c, m, s, codigo, R.InicialPendente{aceita}, R.render(m, s, R.InicialPendente{aceita}), t, r, bs,
        inicial_pendente_sem_preparo(m, s, aceita), consulta)

def resultado_inicial_sem_preparo(+m: R.Micro, +s: D.Estado, resultado: R.ResultadoInicial, valida: Bool) ->
  SemPreparo(R.render(m, s, R.decidir_aceitou_inicial(resultado, valida))):
  match resultado:
    case R.Finalizada{}:
      match valida:
        case False{}: inicial_recusa_sem_preparo(m, s, S.Dados{})
        case True{}: inicial_ok_sem_preparo(m, s)
    case R.FalhouInicial{aceita, etapa, id, fatal}: inicial_falha_sem_preparo(m, s, aceita && valida, etapa, id, fatal)
    case R.PendenteInicial{aceita}: inicial_pendente_sem_preparo(m, s, aceita && valida)

def inicializacao_sem_preparo(+m: R.Micro, +s: D.Estado, juizo: R.Juizo, +resultado: R.ResultadoInicial, +valida: Bool) ->
  SemPreparo(R.render(m, s, R.decidir_juizo_inicial(juizo, resultado, valida))):
  match juizo:
    case R.Aceitou{}: resultado_inicial_sem_preparo(m, s, resultado, valida)
    case R.Recusou{}: inicial_recusa_sem_preparo(m, s, S.Certificado{})
    case R.ErroJuizo{id, fatal}: inicial_falha_sem_preparo(m, s, False{}, X.Verificar{}, id, fatal)
    case R.PendenteJuizo{}: inicial_pendente_sem_preparo(m, s, False{})

# Compartilhados com a Lei6: a inicializacao nao emite conclusao transacional.
def resultado_inicial_sem_fecho(+m: R.Micro, +s: D.Estado, resultado: R.ResultadoInicial, valida: Bool) ->
  {fecho_do_caso(m, s, R.decidir_aceitou_inicial(resultado, valida)) == None{} : Maybe<&2, Fecho>}:
  match resultado:
    case R.Finalizada{}:
      match valida:
        case False{}: {==}
        case True{}: {==}
    case R.FalhouInicial{aceita, etapa, id, fatal}: {==}
    case R.PendenteInicial{aceita}: {==}

def juizo_inicial_sem_fecho(+m: R.Micro, +s: D.Estado, j: R.Juizo, +resultado: R.ResultadoInicial, +valida: Bool) ->
  {fecho_do_caso(m, s, R.decidir_juizo_inicial(j, resultado, valida)) == None{} : Maybe<&2, Fecho>}:
  match j:
    case R.Aceitou{}: resultado_inicial_sem_fecho(m, s, resultado, valida)
    case R.Recusou{}: {==}
    case R.ErroJuizo{id, fatal}: {==}
    case R.PendenteJuizo{}: {==}

def exclusoes_do_inicio(+m: R.Micro, +s: D.Estado, +j: R.Juizo, +resultado: R.ResultadoInicial, +valida: Bool) ->
  L.E<{Fases.ausente(Fases.Conclusao{}, R.render(m, s, R.decidir_juizo_inicial(j, resultado, valida))) == True{} : Bool},
    SemSeguinte(R.render(m, s, R.decidir_juizo_inicial(j, resultado, valida)))>:
  L.Ambos{
    (%juizo_inicial_sem_fecho(m, s, j, resultado, valida) :
      Forma(R.render(m, s, R.decidir_juizo_inicial(j, resultado, valida)), R.decidir_juizo_inicial(j, resultado, valida), _)
      forma_da_rota(m, s, R.decidir_juizo_inicial(j, resultado, valida))),
    ausencia_do_fecho_exclui_seguinte(m, s, R.decidir_juizo_inicial(j, resultado, valida),
      juizo_inicial_sem_fecho(m, s, j, resultado, valida))}

def inicializacao_sem_conclusao_entrega(+m: R.Micro, +s: D.Estado, +j: R.Juizo, +resultado: R.ResultadoInicial, +valida: Bool) ->
  L.E<{Fases.ausente(Fases.Conclusao{}, R.render(m, s, R.decidir_juizo_inicial(j, resultado, valida))) == True{} : Bool},
    L.E<{Fases.ausente(Fases.Completa{}, R.render(m, s, R.decidir_juizo_inicial(j, resultado, valida))) == True{} : Bool},
      {Fases.ausente(Fases.Interrompida{}, R.render(m, s, R.decidir_juizo_inicial(j, resultado, valida))) == True{} : Bool}>>:
  L.Ambos{
    L.e_esquerda({Fases.ausente(Fases.Conclusao{}, R.render(m, s, R.decidir_juizo_inicial(j, resultado, valida))) == True{} : Bool},
      SemSeguinte(R.render(m, s, R.decidir_juizo_inicial(j, resultado, valida))), exclusoes_do_inicio(m, s, j, resultado, valida)),
    (%juizo_inicial_sem_fecho(m, s, j, resultado, valida) :
      EntregasDaForma(R.render(m, s, R.decidir_juizo_inicial(j, resultado, valida)), _)
      entregas_da_forma(m, s, R.decidir_juizo_inicial(j, resultado, valida)))}
