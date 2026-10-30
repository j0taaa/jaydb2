# Geracao determinista do fim do protocolo; nao e um servidor alternativo.
import Base
import ./ProtocoloServico.bend as Q
import ./PrimitivasServico.bend as M
import ../contrato/Dados.bend as D
import ../contrato/Semantica.bend as S
import ../contrato/Protocolo.bend as P
import ../contrato/Recursos.bend as X
import ../contrato/Logica.bend as L
import ../src/Nucleo.bend as N
import ../src/Entrada.bend as E
import ../contrato/Interface.bend as I
import ../src/Transporte.bend as T
import ../src/Configuracao.bend as C

type Entrega is Data:
  Completa{proxima: Bool}
  Quebrada{prefixo: List<&2, U32>}
  PendenteEntrega{}

def depois_entrega(fecha: Bool, +estado: D.Estado, proxima: Bool) -> List<&2, Q.Quadro>:
  match fecha proxima:
    case True{} _: [Q.Fechada{}]
    case False{} True{}: [Q.Seguinte{estado, estado}]
    case False{} False{}: Nil{}

def render_entrega(+estado: D.Estado, bytes: List<&2, U32>, fecha: Bool, entrega: Entrega) -> List<&2, Q.Quadro>:
  match entrega:
    case Completa{proxima}: Con{Q.Entregue{bytes}, depois_entrega(fecha, estado, proxima)}
    case Quebrada{prefixo}: [Q.Interrompida{prefixo}, Q.Fechada{}]
    case PendenteEntrega{}: Nil{}

def render_publicacao(resposta: S.Resposta, estado: D.Estado) -> List<&2, Q.Quadro>:
  match resposta:
    case S.Resposta{S.Sucesso{}, v}: [Q.Publicada{estado}]
    case _: Nil{}

def render_conclusao(conclusao: N.Conclusao, +fecha: Bool, entrega: Entrega) -> List<&2, Q.Quadro>:
  match conclusao:
    case N.Conclusao{+estado, +resposta, +bytes}:
      Con{Q.Preparada{resposta, bytes},
        Q.concatenar(render_publicacao(resposta, estado),
          Con{Q.Concluida{resposta, estado, fecha}, render_entrega(estado, bytes, fecha, entrega)})}

def render_final(preparada: N.Preparada, inicial: D.Estado, fecha: Bool, entrega: Entrega) -> List<&2, Q.Quadro>:
  render_conclusao(N.concluir(preparada, inicial), fecha, entrega)

# Os ramos de erro nunca passam por render_publicacao, mesmo sem estado valido.
def render_erro_enquadrado(resultado: Maybe<&2, List<&2, U32>>, +resposta: S.Resposta,
  +inicial: D.Estado, +fecha: Bool, entrega: Entrega) -> List<&2, Q.Quadro>:
  match resultado:
    case None{}: Nil{}
    case Some{+bytes}:
      Q.concatenar([Q.Preparada{resposta, bytes}, Q.Concluida{resposta, inicial, fecha}],
        render_entrega(inicial, bytes, fecha, entrega))

def render_erro(status: S.Status, inicial: D.Estado, fecha: Bool, entrega: Entrega) -> List<&2, Q.Quadro>:
  +resposta = S.resposta_erro(status)
  render_erro_enquadrado(P.enquadrar(S.resposta_valor(resposta)), resposta, inicial, fecha, entrega)

# Fontes de micro-operacoes; nunca quadros arbitrarios com publicacoes.

type Micro is Data:
  Micro{entrada: List<&2, M.Primitiva>, autenticacao: List<&2, M.Primitiva>,
    execucao: List<&2, M.Primitiva>, saida: List<&2, M.Primitiva>}

def micro_entrada(m: Micro) -> List<&2, Q.Quadro>:
  Micro{a, b, c, d} = m
  M.expandir_primitivas(a)
def micro_autenticacao(m: Micro) -> List<&2, Q.Quadro>:
  Micro{a, b, c, d} = m
  M.expandir_primitivas(b)
def micro_execucao(m: Micro) -> List<&2, Q.Quadro>:
  Micro{a, b, c, d} = m
  M.expandir_primitivas(c)
def micro_saida(m: Micro) -> List<&2, Q.Quadro>:
  Micro{a, b, c, d} = m
  M.expandir_primitivas(d)

def render_recebida(m: Micro, +r: P.Requisicao) -> List<&2, Q.Quadro>:
  Q.concatenar(micro_entrada(m), [Q.Recebida{r}])
def render_autenticada(+m: Micro, +r: P.Requisicao, ctx: D.Contexto) -> List<&2, Q.Quadro>:
  Q.concatenar(render_recebida(m, r), Q.concatenar(micro_autenticacao(m), [Q.Autenticada{r, Some{ctx}}]))
def render_verificada(m: Micro, +r: P.Requisicao, +ctx: D.Contexto) -> List<&2, Q.Quadro>:
  Q.concatenar(render_autenticada(m, r, ctx), [Q.Aceita{r, ctx}])
def render_comecada(+m: Micro, +r: P.Requisicao, +ctx: D.Contexto) -> List<&2, Q.Quadro>:
  Q.concatenar(render_verificada(m, r, ctx), Q.concatenar(micro_execucao(m), [Q.Comecada{r, ctx}]))
def render_execucao(m: Micro, +r: P.Requisicao, +ctx: D.Contexto, execucao: List<&2, Q.QuadroExec>) -> List<&2, Q.Quadro>:
  Q.concatenar(render_comecada(m, r, ctx), Q.expandir_exec(r, ctx, execucao))

def quadro_preparada(p: N.Preparada) -> Q.Quadro:
  N.Preparada{w, ts, r, bs} = p
  Q.Preparada{r, bs}

# Nenhuma dessas fases pode publicar ou concluir por conta propria.
type FaseAntes is Data:
  AntesEntrada{}
  AposReceber{requisicao: P.Requisicao}
  AposAutenticar{requisicao: P.Requisicao, contexto: D.Contexto}
  AposVerificar{requisicao: P.Requisicao, contexto: D.Contexto}
  Executando{requisicao: P.Requisicao, contexto: D.Contexto, execucao: List<&2, Q.QuadroExec>}
  AposPreparar{requisicao: P.Requisicao, contexto: D.Contexto, execucao: List<&2, Q.QuadroExec>, preparada: N.Preparada}

def render_fase(+m: Micro, fase: FaseAntes) -> List<&2, Q.Quadro>:
  match fase:
    case AntesEntrada{}: micro_entrada(m)
    case AposReceber{r}: render_recebida(m, r)
    case AposAutenticar{r, ctx}: render_autenticada(m, r, ctx)
    case AposVerificar{r, ctx}: render_verificada(m, r, ctx)
    case Executando{r, ctx, exec}: render_execucao(m, r, ctx, exec)
    case AposPreparar{r, ctx, exec, p}:
      Q.concatenar(render_execucao(m, r, ctx, exec), Q.concatenar(micro_saida(m), [quadro_preparada(p)]))

type ErroEntrada is Data:
  Entrada{}
  Limite{}
def status_entrada(erro: ErroEntrada) -> S.Status:
  match erro:
    case Entrada{}: S.Entrada{}
    case Limite{}: S.Limite{}

type Caso is Data:
  InicialOk{}
  InicialRecusa{status: S.Status}
  InicialFalha{aceita: Bool, etapa: X.Etapa, identificador: String, fatal: Bool}
  SemResposta{}
  EntradaRecusa{erro: ErroEntrada, fecha: Bool, entrega: Entrega}
  AutRecusa{requisicao: P.Requisicao, entrega: Entrega}
  GateRecusa{requisicao: P.Requisicao, contexto: D.Contexto, entrega: Entrega}
  Executada{requisicao: P.Requisicao, contexto: D.Contexto,
    execucao: List<&2, Q.QuadroExec>, preparada: N.Preparada, entrega: Entrega}
  FalhaAntes{fase: FaseAntes, etapa: X.Etapa, identificador: String, fatal: Bool, entrega: Entrega}
  FatalAposPublicacao{requisicao: P.Requisicao, contexto: D.Contexto,
    execucao: List<&2, Q.QuadroExec>, preparada: N.Preparada, etapa: X.Etapa, identificador: String}
  Pendente{fase: FaseAntes}
  InicialPendente{prova_aceita: Bool}

def render_inicial(resultado: Maybe<&2, List<&2, U32>>, +inicial: D.Estado) -> List<&2, Q.Quadro>:
  match resultado:
    case None{}: [Q.Codificada{D.estado_valor(inicial), None{}}]
    case Some{+bs}: [Q.Codificada{D.estado_valor(inicial), Some{bs}}, Q.Guardada{inicial, bs, inicial}, Q.Iniciada{inicial}]

def render_falha_fim(inicial: D.Estado, fatal: Bool, entrega: Entrega) -> List<&2, Q.Quadro>:
  match fatal:
    case True{}: [Q.Fechada{}]
    case False{}: render_erro(S.Falha{}, inicial, False{}, entrega)
def render_falha(inicial: D.Estado, etapa: X.Etapa, id: String, +fatal: Bool, entrega: Entrega) -> List<&2, Q.Quadro>:
  Con{Q.Falhou{etapa, id, fatal}, render_falha_fim(inicial, fatal, entrega)}

def render_fatal_publicada(conclusao: N.Conclusao, etapa: X.Etapa, id: String) -> List<&2, Q.Quadro>:
  match conclusao:
    case N.Conclusao{estado, +r, bs}:
      Con{Q.Preparada{r, bs}, Q.concatenar(render_publicacao(r, estado), [Q.Falhou{etapa, id, True{}}, Q.Fechada{}])}

def prefixo_inicial(+m: Micro, aceita: Bool) -> List<&2, Q.Quadro>:
  match aceita:
    case True{}: Con{Q.InicialAceita{}, micro_saida(m)}
    case False{}: Nil{}

def render_caso(+m: Micro, +inicial: D.Estado, caso: Caso) -> List<&2, Q.Quadro>:
  match caso:
    case InicialOk{}:
      Con{Q.InicialAceita{}, Q.concatenar(micro_saida(m), render_inicial(P.codificar(D.estado_valor(inicial)), inicial))}
    case InicialRecusa{s}: [Q.InicialRecusada{s}]
    case InicialFalha{aceita, etapa, id, fatal}:
      Q.concatenar(prefixo_inicial(m, aceita), [Q.Falhou{etapa, id, fatal}, Q.InicialRecusada{S.Falha{}}])
    case SemResposta{}: [Q.Fechada{}]
    case EntradaRecusa{erro, fecha, entrega}:
      Q.concatenar(micro_entrada(m), render_erro(status_entrada(erro), inicial, fecha, entrega))
    case AutRecusa{+r, entrega}:
      Q.concatenar(render_recebida(m, r), Q.concatenar(micro_autenticacao(m),
        Con{Q.Autenticada{r, None{}}, render_erro(S.Autenticacao{}, inicial, False{}, entrega)}))
    case GateRecusa{+r, +ctx, entrega}:
      Q.concatenar(render_autenticada(m, r, ctx), Con{Q.Rejeitada{r, ctx}, render_erro(S.Certificado{}, inicial, False{}, entrega)})
    case Executada{r, ctx, exec, p, entrega}:
      Q.concatenar(render_execucao(m, r, ctx, exec), Q.concatenar(micro_saida(m), render_final(p, inicial, False{}, entrega)))
    case FalhaAntes{fase, etapa, id, fatal, entrega}:
      Q.concatenar(render_fase(m, fase), render_falha(inicial, etapa, id, fatal, entrega))
    case FatalAposPublicacao{r, ctx, exec, p, etapa, id}:
      Q.concatenar(render_execucao(m, r, ctx, exec), Q.concatenar(micro_saida(m), render_fatal_publicada(N.concluir(p, inicial), etapa, id)))
    case Pendente{fase}: render_fase(m, fase)
    case InicialPendente{aceita}: prefixo_inicial(m, aceita)

def render(m: Micro, +inicial: D.Estado, caso: Caso) -> List<&2, Q.Quadro>:
  Con{Q.Configurada{}, render_caso(m, inicial, caso)}


# Resultados das ferramentas e do processo; nenhum campo e uma lei do banco.
type Juizo is Data:
  Aceitou{}
  Recusou{}
  ErroJuizo{identificador: String, fatal: Bool}
  PendenteJuizo{}

type PontoExec is Data:
  AntesDeComecar{}
  Durante{quadros: List<&2, Q.QuadroExec>}
  Preparou{quadros: List<&2, Q.QuadroExec>, preparada: N.Preparada}

type SaidaExecucao is Data:
  Finalizou{quadros: List<&2, Q.QuadroExec>, preparada: N.Preparada}
  ErroExecucao{ponto: PontoExec, etapa: X.Etapa, identificador: String, fatal: Bool}
  PendenteExecucao{ponto: PontoExec}

# Resultado das acoes do host apos o executor: cleanup e a troca da raiz.
type Limpeza is Data:
  Limpa{}
  ErroLimpeza{identificador: String, fatal: Bool}
  FatalAposStore{etapa: X.Etapa, identificador: String}
  PendenteLimpeza{}

# Falha de IO/processo so aparece quando sua etapa foi realmente alcancada.
type Preprocessamento is Data:
  Normal{}
  FalhaEnquadramento{identificador: String, fatal: Bool}
  FalhaDecode{identificador: String, fatal: Bool}
  FalhaAuth{identificador: String, fatal: Bool}
  PendenteEnquadramento{}
  PendenteDecode{}
  PendenteAuth{}

type DadosFerramentas is Data:
  DadosFerramentas{juizo: Juizo, execucao: SaidaExecucao, limpeza: Limpeza,
    entrega: Entrega, preprocessamento: Preprocessamento}

def preprocessamento(d: DadosFerramentas) -> Preprocessamento:
  DadosFerramentas{j, ex, li, en, pre} = d
  pre

def entrega_de(d: DadosFerramentas) -> Entrega:
  DadosFerramentas{j, ex, li, en, pre} = d
  en

def juizo_de(d: DadosFerramentas) -> Juizo:
  DadosFerramentas{j, ex, li, en, pre} = d
  j

def erro_de_mensagem(status: S.Status) -> ErroEntrada:
  match status:
    case S.Limite{}: Limite{}
    case _: Entrada{}

def fase_do_erro(ponto: PontoExec, r: P.Requisicao, ctx: D.Contexto) -> FaseAntes:
  match ponto:
    case AntesDeComecar{}: AposVerificar{r, ctx}
    case Durante{quadros}: Executando{r, ctx, quadros}
    case Preparou{quadros, preparada}: AposPreparar{r, ctx, quadros, preparada}

def decidir_limpeza(r: P.Requisicao, ctx: D.Contexto, quadros: List<&2, Q.QuadroExec>,
  preparada: N.Preparada, limpeza: Limpeza, entrega: Entrega) -> Caso:
  match limpeza:
    case Limpa{}: Executada{r, ctx, quadros, preparada, entrega}
    case ErroLimpeza{id, fatal}:
      FalhaAntes{AposPreparar{r, ctx, quadros, preparada}, X.Preparar{}, id, fatal, entrega}
    case FatalAposStore{etapa, id}: FatalAposPublicacao{r, ctx, quadros, preparada, etapa, id}
    case PendenteLimpeza{}: Pendente{AposPreparar{r, ctx, quadros, preparada}}

def decidir_execucao(r: P.Requisicao, ctx: D.Contexto, saida: SaidaExecucao,
  limpeza: Limpeza, entrega: Entrega) -> Caso:
  match saida:
    case Finalizou{quadros, preparada}: decidir_limpeza(r, ctx, quadros, preparada, limpeza, entrega)
    case ErroExecucao{ponto, etapa, id, fatal}:
      FalhaAntes{fase_do_erro(ponto, r, ctx), etapa, id, fatal, entrega}
    case PendenteExecucao{ponto}: Pendente{fase_do_erro(ponto, r, ctx)}

def decidir_juizo(r: P.Requisicao, ctx: D.Contexto, dados: DadosFerramentas) -> Caso:
  DadosFerramentas{juizo, execucao, limpeza, entrega, pre} = dados
  match juizo:
    case Aceitou{}: decidir_execucao(r, ctx, execucao, limpeza, entrega)
    case Recusou{}: GateRecusa{r, ctx, entrega}
    case ErroJuizo{id, fatal}: FalhaAntes{AposAutenticar{r, ctx}, X.Verificar{}, id, fatal, entrega}
    case PendenteJuizo{}: Pendente{AposAutenticar{r, ctx}}

def decidir_identidade(ctx: Maybe<&2, D.Contexto>, r: P.Requisicao, dados: DadosFerramentas) -> Caso:
  match ctx:
    case None{}:
      DadosFerramentas{juizo, execucao, limpeza, entrega, pre} = dados
      AutRecusa{r, entrega}
    case Some{c}: decidir_juizo(r, c, dados)

def decidir_autenticacao(pre: Preprocessamento, estado: D.Estado, +r: P.Requisicao, dados: DadosFerramentas) -> Caso:
  match pre:
    case FalhaAuth{id, fatal}: FalhaAntes{AposReceber{r}, X.Autenticar{}, id, fatal, entrega_de(dados)}
    case PendenteAuth{}: Pendente{AposReceber{r}}
    case _: decidir_identidade(D.autenticar(estado, I.credencial(r)), r, dados)

def decidir_pre(entrada: E.PreAutenticacao, +dados: DadosFerramentas) -> Caso:
  match entrada:
    case E.Pronta{estado, +r}:
      decidir_autenticacao(preprocessamento(dados), estado, r, dados)
    case E.ErroMensagem{status}:
      DadosFerramentas{juizo, execucao, limpeza, entrega, pre} = dados
      EntradaRecusa{erro_de_mensagem(status), False{}, entrega}
    case E.ErroTransporte{}:
      DadosFerramentas{juizo, execucao, limpeza, entrega, pre} = dados
      FalhaAntes{AntesEntrada{}, X.Enquadrar{}, "internal_transport", False{}, entrega}

def decidir_decode(pre: Preprocessamento, bytes: List<&2, U32>, e: D.Esquema,
  lim: S.Limites, dados: DadosFerramentas) -> Caso:
  match pre:
    case FalhaDecode{id, fatal}: FalhaAntes{AntesEntrada{}, X.Enquadrar{}, id, fatal, entrega_de(dados)}
    case PendenteDecode{}: Pendente{AntesEntrada{}}
    case _: decidir_pre(E.decodificar(bytes, e, lim), dados)

# O pacote privado e construido, nao recebido como resultado arbitrario.
def decidir_pacote(pacote: Maybe<&2, List<&2, U32>>, e: D.Esquema,
  lim: S.Limites, +dados: DadosFerramentas) -> Caso:
  match pacote:
    case None{}:
      DadosFerramentas{juizo, execucao, limpeza, entrega, pre} = dados
      FalhaAntes{AntesEntrada{}, X.Enquadrar{}, "internal_transport", False{}, entrega}
    case Some{bytes}: decidir_decode(preprocessamento(dados), bytes, e, lim, dados)

# A recepcao externa decide fechamento antes de analisar o pacote privado.
def decidir_disposicao(d: X.Disposicao, estado: List<&2, U32>, e: D.Esquema,
  lim: S.Limites, dados: DadosFerramentas) -> Caso:
  match d:
    case X.EncerrarSemResposta{}: SemResposta{}
    case X.RecusarEncerrar{s}:
      DadosFerramentas{juizo, execucao, limpeza, entrega, pre} = dados
      EntradaRecusa{erro_de_mensagem(s), True{}, entrega}
    case X.RecusarContinuar{s}:
      DadosFerramentas{juizo, execucao, limpeza, entrega, pre} = dados
      EntradaRecusa{erro_de_mensagem(s), False{}, entrega}
    case X.ProcessarCorpo{corpo}: decidir_pacote(T.juntar(estado, corpo), e, lim, dados)

def decidir_enquadramento(pre: Preprocessamento, d: X.Disposicao, estado: List<&2, U32>,
  e: D.Esquema, lim: S.Limites, dados: DadosFerramentas) -> Caso:
  match pre:
    case FalhaEnquadramento{id, fatal}: FalhaAntes{AntesEntrada{}, X.Enquadrar{}, id, fatal, entrega_de(dados)}
    case PendenteEnquadramento{}: Pendente{AntesEntrada{}}
    case _: decidir_disposicao(d, estado, e, lim, dados)

def decidir(c: S.Configuracao, recepcao: X.Recepcao, estado: List<&2, U32>, +dados: DadosFerramentas) -> Caso:
  match c:
    case S.Configuracao{+e, leis, +lim, amb}:
      decidir_enquadramento(preprocessamento(dados), X.decidir_recepcao_em(lim, recepcao), estado, e, lim, dados)


# Resultado real do worker inicial e das acoes do host antes de Database.
# A marca so e verdadeira depois do ramo CheckedConfiguration valido.
type ResultadoInicial is Data:
  Finalizada{}
  FalhouInicial{prova_aceita: Bool, etapa: X.Etapa, identificador: String, fatal: Bool}
  PendenteInicial{prova_aceita: Bool}

def decidir_aceitou_inicial(resultado: ResultadoInicial, valida: Bool) -> Caso:
  match resultado:
    case Finalizada{}:
      match valida:
        case False{}: InicialRecusa{S.Dados{}}
        case True{}: InicialOk{}
    case FalhouInicial{aceita, etapa, id, fatal}: InicialFalha{aceita && valida, etapa, id, fatal}
    case PendenteInicial{aceita}: InicialPendente{aceita && valida}

# O checker precede o worker. Um worker que nao retornou nao comprova que a
# validacao nativa da configuracao foi executada, mesmo se ela seria True.
def decidir_juizo_inicial(juizo: Juizo, resultado: ResultadoInicial, valida: Bool) -> Caso:
  match juizo:
    case Aceitou{}: decidir_aceitou_inicial(resultado, valida)
    case Recusou{}: InicialRecusa{S.Certificado{}}
    case ErroJuizo{id, fatal}: InicialFalha{False{}, X.Verificar{}, id, fatal}
    case PendenteJuizo{}: InicialPendente{False{}}

def decidir_inicial_casos(valida: Bool, juizo: Juizo) -> Caso:
  decidir_juizo_inicial(juizo, Finalizada{}, valida)

def decidir_resultado_inicial(c: S.Configuracao, identidade: String,
  juizo: Juizo, resultado: ResultadoInicial) -> Caso:
  decidir_juizo_inicial(juizo, resultado, C.valida(c, identidade))

def decidir_inicial(c: S.Configuracao, identidade: String, juizo: Juizo) -> Caso:
  decidir_resultado_inicial(c, identidade, juizo, Finalizada{})

# A lista observada e resultado desta geracao, nao entrada fornecida pelo cliente.
def gerar(c: S.Configuracao, recepcao: X.Recepcao, estado: List<&2, U32>,
  inicial: D.Estado, dados: DadosFerramentas, micro: Micro) -> List<&2, Q.Quadro>:
  render(micro, inicial, decidir(c, recepcao, estado, dados))

def gerar_resultado_inicial(c: S.Configuracao, identidade: String, inicial: D.Estado,
  juizo: Juizo, resultado: ResultadoInicial, micro: Micro) -> List<&2, Q.Quadro>:
  render(micro, inicial, decidir_resultado_inicial(c, identidade, juizo, resultado))

# Especializacao de sucesso usada pelos lemas do caminho concluido.
def gerar_inicial(c: S.Configuracao, identidade: String, inicial: D.Estado,
  juizo: Juizo, micro: Micro) -> List<&2, Q.Quadro>:
  gerar_resultado_inicial(c, identidade, inicial, juizo, Finalizada{}, micro)

# A decisao de atendimento nunca e uma inicializacao.
def inicia(caso: Caso) -> Bool:
  match caso:
    case InicialOk{}: True{}
    case InicialFalha{aceita, etapa, id, fatal}: aceita
    case InicialPendente{aceita}: aceita
    case _: False{}

def limpeza_nao_inicia(r: P.Requisicao, ctx: D.Contexto, qs: List<&2, Q.QuadroExec>,
  p: N.Preparada, l: Limpeza, entrega: Entrega) ->
  {inicia(decidir_limpeza(r, ctx, qs, p, l, entrega)) == False{} : Bool}:
  match l:
    case Limpa{}: {==}
    case ErroLimpeza{id, fatal}: {==}
    case FatalAposStore{etapa, id}: {==}
    case PendenteLimpeza{}: {==}

def execucao_nao_inicia(r: P.Requisicao, ctx: D.Contexto, saida: SaidaExecucao,
  l: Limpeza, entrega: Entrega) ->
  {inicia(decidir_execucao(r, ctx, saida, l, entrega)) == False{} : Bool}:
  match saida:
    case Finalizou{qs, p}: limpeza_nao_inicia(r, ctx, qs, p, l, entrega)
    case ErroExecucao{ponto, etapa, id, fatal}: {==}
    case PendenteExecucao{ponto}: {==}

def juizo_nao_inicia(r: P.Requisicao, ctx: D.Contexto, d: DadosFerramentas) ->
  {inicia(decidir_juizo(r, ctx, d)) == False{} : Bool}:
  match d:
    case DadosFerramentas{j, ex, li, en, pre}:
      match j:
        case Aceitou{}: execucao_nao_inicia(r, ctx, ex, li, en)
        case Recusou{}: {==}
        case ErroJuizo{id, fatal}: {==}
        case PendenteJuizo{}: {==}

def identidade_nao_inicia(ctx: Maybe<&2, D.Contexto>, r: P.Requisicao, d: DadosFerramentas) ->
  {inicia(decidir_identidade(ctx, r, d)) == False{} : Bool}:
  match ctx:
    case None{}:
      DadosFerramentas{ju, ex, li, en, pre} = d
      {==}
    case Some{c}: juizo_nao_inicia(r, c, d)

def autenticacao_nao_inicia(pre: Preprocessamento, estado: D.Estado, +r: P.Requisicao, d: DadosFerramentas) ->
  {inicia(decidir_autenticacao(pre, estado, r, d)) == False{} : Bool}:
  match pre:
    case FalhaAuth{id, fatal}: {==}
    case Normal{}: identidade_nao_inicia(D.autenticar(estado, I.credencial(r)), r, d)
    case FalhaEnquadramento{id, fatal}: identidade_nao_inicia(D.autenticar(estado, I.credencial(r)), r, d)
    case FalhaDecode{id, fatal}: identidade_nao_inicia(D.autenticar(estado, I.credencial(r)), r, d)

    case PendenteEnquadramento{}: identidade_nao_inicia(D.autenticar(estado, I.credencial(r)), r, d)
    case PendenteDecode{}: identidade_nao_inicia(D.autenticar(estado, I.credencial(r)), r, d)
    case PendenteAuth{}: {==}

def pre_nao_inicia(p: E.PreAutenticacao, +d: DadosFerramentas) ->
  {inicia(decidir_pre(p, d)) == False{} : Bool}:
  match p:
    case E.Pronta{s, +r}: autenticacao_nao_inicia(preprocessamento(d), s, r, d)
    case E.ErroMensagem{status}:
      DadosFerramentas{ju, ex, li, en, pre} = d
      {==}
    case E.ErroTransporte{}:
      DadosFerramentas{ju, ex, li, en, pre} = d
      {==}

def decode_nao_inicia(pre: Preprocessamento, bs: List<&2, U32>, e: D.Esquema,
  l: S.Limites, d: DadosFerramentas) ->
  {inicia(decidir_decode(pre, bs, e, l, d)) == False{} : Bool}:
  match pre:
    case FalhaDecode{id, fatal}: {==}
    case Normal{}: pre_nao_inicia(E.decodificar(bs, e, l), d)
    case FalhaEnquadramento{id, fatal}: pre_nao_inicia(E.decodificar(bs, e, l), d)
    case FalhaAuth{id, fatal}: pre_nao_inicia(E.decodificar(bs, e, l), d)

    case PendenteEnquadramento{}: pre_nao_inicia(E.decodificar(bs, e, l), d)
    case PendenteDecode{}: {==}
    case PendenteAuth{}: pre_nao_inicia(E.decodificar(bs, e, l), d)

def pacote_nao_inicia(p: Maybe<&2, List<&2, U32>>, e: D.Esquema,
  l: S.Limites, +d: DadosFerramentas) ->
  {inicia(decidir_pacote(p, e, l, d)) == False{} : Bool}:
  match p:
    case None{}:
      DadosFerramentas{ju, ex, li, en, pre} = d
      {==}
    case Some{bs}: decode_nao_inicia(preprocessamento(d), bs, e, l, d)

def disposicao_nao_inicia(x: X.Disposicao, s: List<&2, U32>, e: D.Esquema,
  l: S.Limites, d: DadosFerramentas) ->
  {inicia(decidir_disposicao(x, s, e, l, d)) == False{} : Bool}:
  match x:
    case X.EncerrarSemResposta{}: {==}
    case X.RecusarEncerrar{status}:
      DadosFerramentas{ju, ex, li, en, pre} = d
      {==}
    case X.RecusarContinuar{status}:
      DadosFerramentas{ju, ex, li, en, pre} = d
      {==}
    case X.ProcessarCorpo{bs}: pacote_nao_inicia(T.juntar(s, bs), e, l, d)

def enquadramento_nao_inicia(pre: Preprocessamento, x: X.Disposicao, s: List<&2, U32>,
  e: D.Esquema, l: S.Limites, d: DadosFerramentas) ->
  {inicia(decidir_enquadramento(pre, x, s, e, l, d)) == False{} : Bool}:
  match pre:
    case FalhaEnquadramento{id, fatal}: {==}
    case Normal{}: disposicao_nao_inicia(x, s, e, l, d)
    case FalhaDecode{id, fatal}: disposicao_nao_inicia(x, s, e, l, d)
    case FalhaAuth{id, fatal}: disposicao_nao_inicia(x, s, e, l, d)

    case PendenteEnquadramento{}: {==}
    case PendenteDecode{}: disposicao_nao_inicia(x, s, e, l, d)
    case PendenteAuth{}: disposicao_nao_inicia(x, s, e, l, d)

law atendimento_nao_inicia:
  for c: S.Configuracao
  for r: X.Recepcao
  for s: List<&2, U32>
  for +d: DadosFerramentas
  {inicia(decidir(c, r, s, d)) == False{} : Bool}
def atendimento_nao_inicia(c, r, s, d):
  match c:
    case S.Configuracao{+e, leis, +l, amb}:
      enquadramento_nao_inicia(preprocessamento(d), X.decidir_recepcao_em(l, r), s, e, l, d)
