# Ligacao aos adaptadores puros usados pelo controlador/runtime nativo.
# Nao pressupoe que o host/ABI ja realizem esta semantica.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Semantica.bend as S
import ../contrato/Protocolo.bend as P
import ../contrato/Interface.bend as I
import ../contrato/Logica.bend as L
import ../src/Nucleo.bend as N
import ../src/Entrada.bend as E
import ../src/Execucao.bend as X

def AutenticacaoFiel(resultado: E.Analise, -r: P.Requisicao, -s: D.Estado) -> Type:
  match resultado:
    case E.Recebida{estado, requisicao, contexto}:
      L.E<{estado == s : D.Estado}, L.E<{requisicao == r : P.Requisicao},
        {D.autenticar(s, I.credencial(r)) == Some{contexto} : Maybe<&2, D.Contexto>}>>
    case E.Rejeitada{S.Autenticacao{}}:
      {D.autenticar(s, I.credencial(r)) == None{} : Maybe<&2, D.Contexto>}
    case _:
      Empty

def identidade_fiel(q: Maybe<&2, D.Contexto>, -r: P.Requisicao, -s: D.Estado,
  aut: {D.autenticar(s, I.credencial(r)) == q : Maybe<&2, D.Contexto>}) ->
  AutenticacaoFiel(E.identidade(q, s, r), r, s):
  match q:
    case None{}:
      aut
    case Some{c}:
      L.Ambos{{==}, L.Ambos{{==}, aut}}

law adaptador_autentica_estado_e_credencial_reais:
  for +r: P.Requisicao
  for +s: D.Estado
  AutenticacaoFiel(E.autenticar(Some{r}, s), r, s)
def adaptador_autentica_estado_e_credencial_reais(r, s):
  match r:
    case P.Requisicao{cred, cod, args, pi}:
      identidade_fiel(D.autenticar(s, cred), P.Requisicao{cred, cod, args, pi}, s, {==})

law entrada_recebida_tem_identidade_autentica:
  for +r: P.Requisicao
  for +s: D.Estado
  for -r2: P.Requisicao
  for -s2: D.Estado
  for -ctx: D.Contexto
  for recebida: {E.autenticar(Some{r}, s) == E.Recebida{s2, r2, ctx} : E.Analise}
  L.E<{s2 == s : D.Estado}, L.E<{r2 == r : P.Requisicao},
    {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>}>>
def entrada_recebida_tem_identidade_autentica(r, s, r2, s2, ctx, recebida):
  %recebida : AutenticacaoFiel(_, r, s)
  adaptador_autentica_estado_e_credencial_reais(r, s)

law adaptador_inicia_maquina_correta:
  for -p: S.Programa
  for -ctx: D.Contexto
  for -args: D.Valor
  for -s: D.Estado
  {X.iniciar(p, ctx, args, s) ==
    X.EstadoExecucao{s, N.EmCurso{s, S.iniciar(p, ctx, args), Nil{}}} : X.EstadoExecucao}
def adaptador_inicia_maquina_correta(p, ctx, args, s):
  {==}

def instantaneo_da_iteracao(i: X.Iteracao) -> Maybe<&2, S.Percurso>:
  match i:
    case X.Continuar{X.EstadoExecucao{s, m}}:
      Some{N.instantaneo(m)}
    case X.Preparar{X.EstadoExecucao{s, m}}:
      Some{N.instantaneo(m)}
    case _:
      None{}

law adaptador_preserva_maquina_apos_passo:
  for m: N.Maquina
  for -s: D.Estado
  {instantaneo_da_iteracao(X.apos_passo(m, s)) == Some{N.instantaneo(m)} : Maybe<&2, S.Percurso>}
def adaptador_preserva_maquina_apos_passo(m, s):
  match m:
    case N.EmCurso{w, a, ts}:
      {==}
    case N.Parada{w, ts, r}:
      {==}

law adaptador_em_curso_avanca_exatamente_uma_acao:
  for -inicial: D.Estado
  for -w: D.Estado
  for -acao: S.Acao
  for -ts: List<&2, S.Evento>
  for -c: S.Configuracao
  {X.avancar(X.EstadoExecucao{inicial, N.EmCurso{w, acao, ts}}, c) ==
    X.apos_passo(N.avancar(N.EmCurso{w, acao, ts}, S.esquema(c)), inicial) : X.Iteracao}
def adaptador_em_curso_avanca_exatamente_uma_acao(inicial, w, acao, ts, c):
  {==}

law adaptador_parado_apenas_prepara_e_conclui:
  for -inicial: D.Estado
  for -w: D.Estado
  for -ts: List<&2, S.Evento>
  for -r: S.Resposta
  for -c: S.Configuracao
  {X.avancar(X.EstadoExecucao{inicial, N.Parada{w, ts, r}}, c) ==
    X.preparada(N.preparar(N.Parada{w, ts, r}, c), inicial) : X.Iteracao}
def adaptador_parado_apenas_prepara_e_conclui(inicial, w, ts, r, c):
  {==}

# O sinal privado zero impede que o controlador publique ate uma copia
# identica do estado antigo em recusa/erro. Nenhum estado e serializado.
def SinalSemPublicacao(status: S.Status, -estado: D.Estado,
  -valor: D.Valor, -bytes: List<&2, U32>) -> Type:
  match status:
    case S.Sucesso{}:
      Unit
    case _:
      {X.concluir(N.Conclusao{estado, S.Resposta{status, valor}, bytes}) ==
        X.Encerrar{Con{0, bytes}} : X.Iteracao}

law todo_desfecho_sem_sucesso_emite_apenas_resposta:
  for status: S.Status
  for -estado: D.Estado
  for -valor: D.Valor
  for -bytes: List<&2, U32>
  SinalSemPublicacao(status, estado, valor, bytes)
def todo_desfecho_sem_sucesso_emite_apenas_resposta(status, estado, valor, bytes):
  match status:
    case S.Sucesso{}:
      Unit{}
    case S.Recusa{}:
      {==}
    case S.Entrada{}:
      {==}
    case S.Autenticacao{}:
      {==}
    case S.Certificado{}:
      {==}
    case S.Dados{}:
      {==}
    case S.Limite{}:
      {==}
    case S.Falha{}:
      {==}

def pede_publicacao(i: X.Iteracao) -> Bool:
  match i:
    case X.Encerrar{Con{flag, bs}}:
      U32.is_eq(flag, 1)
    case _:
      False{}

law todo_pedido_de_publicacao_provem_de_sucesso:
  for status: S.Status
  for -estado: D.Estado
  for -valor: D.Valor
  for -bytes: List<&2, U32>
  for pedido: {pede_publicacao(X.concluir(N.Conclusao{estado, S.Resposta{status, valor}, bytes})) == True{} : Bool}
  {S.eh_sucesso(status) == True{} : Bool}
def todo_pedido_de_publicacao_provem_de_sucesso(status, estado, valor, bytes, pedido):
  match status:
    case S.Sucesso{}:
      {==}
    case S.Recusa{}:
      pedido
    case S.Entrada{}:
      pedido
    case S.Autenticacao{}:
      pedido
    case S.Certificado{}:
      pedido
    case S.Dados{}:
      pedido
    case S.Limite{}:
      pedido
    case S.Falha{}:
      pedido
