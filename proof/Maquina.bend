# Ordem dos eventos, operacoes efetivas e progresso do interpretador real.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Semantica.bend as S
import ../contrato/Interface.bend as I
import ../contrato/Vinculos.bend as V
import ../contrato/Logica.bend as L
import ../src/Nucleo.bend as N
import ./Fundamentos.bend as F

law referencia_parada:
  for n: Nat
  for -w: D.Estado
  for -ts: List<&2, S.Evento>
  for -r: S.Resposta
  for -e: D.Esquema
  {S.continuar_percurso(n, S.Parou{w, r}, e, ts) == S.Final{w, ts, r} : S.Percurso}
def referencia_parada(n, w, ts, r, e):
  match n:
    case 0n:
      {==}
    case 1n+k:
      {==}

law acrescentar_preserva_prefixo:
  for ts: List<&2, S.Evento>
  for -evento: S.Evento
  L.Prefixo(S.Evento, ts, S.acrescentar(ts, evento))
def acrescentar_preserva_prefixo(ts, evento):
  match ts:
    case Nil{}:
      Unit{}
    case Con{h, t}:
      L.Ambos{{==}, acrescentar_preserva_prefixo(t, evento)}

def PercursoComPrefixo(-n: Nat, -m: N.Maquina, -e: D.Esquema) -> Type:
  &percurso: S.Percurso -> L.E<{N.percorrer(n, m, e) == percurso : S.Percurso},
    L.Prefixo(S.Evento, S.eventos_percurso(N.instantaneo(m)), S.eventos_percurso(percurso))>

def receber_continuacao(-n: Nat, -w: D.Estado, -a: S.Acao, +ts: List<&2, S.Evento>,
  +ev: S.Evento, -e: D.Esquema,
  resultado: PercursoComPrefixo(n, N.EmCurso{w, a, S.acrescentar(ts, ev)}, e)) ->
  &percurso: S.Percurso -> L.E<{N.percorrer(n, N.EmCurso{w, a, S.acrescentar(ts, ev)}, e) == percurso : S.Percurso},
    L.Prefixo(S.Evento, ts, S.eventos_percurso(percurso))>:
  match resultado:
    case (+percurso, L.Ambos{igualdade, prefixo}):
      (percurso, L.Ambos{igualdade,
        F.prefixo_transitivo(S.Evento, ts, S.acrescentar(ts, ev), S.eventos_percurso(percurso),
          acrescentar_preserva_prefixo(ts, ev), prefixo)})

def passo_com_prefixo(passo: S.Passo, +n: Nat, +e: D.Esquema, +ts: List<&2, S.Evento>,
  rec: @m: N.Maquina -> PercursoComPrefixo(n, m, e)) ->
  &percurso: S.Percurso -> L.E<{N.percorrer(n, N.passo_maquina(passo, ts), e) == percurso : S.Percurso},
    L.Prefixo(S.Evento, ts, S.eventos_percurso(percurso))>:
  match passo:
    case S.Continua{w, a, +ev}:
      receber_continuacao(n, w, a, ts, ev, e, rec(N.EmCurso{w, a, S.acrescentar(ts, ev)}))
    case S.Parou{+w, +resposta}:
      (S.Final{w, ts, resposta}, L.Ambos{N.parada_absorve(n, w, ts, resposta, e), L.prefixo_refl(S.Evento, ts)})
    case S.OperacaoFalhou{+w, +ev}:
      (S.Final{w, S.acrescentar(ts, ev), S.resposta_erro(S.Dados{})},
        L.Ambos{N.parada_absorve(n, w, S.acrescentar(ts, ev), S.resposta_erro(S.Dados{}), e),
          acrescentar_preserva_prefixo(ts, ev)})

law percurso_com_prefixo:
  for +n: Nat
  for m: N.Maquina
  for +e: D.Esquema
  PercursoComPrefixo(n, m, e)
def percurso_com_prefixo(n, m, e):
  match n m:
    case 0n N.EmCurso{w, a, +ts}:
      (S.Prefixo{w, ts}, L.Ambos{{==}, L.prefixo_refl(S.Evento, ts)})
    case 0n N.Parada{w, +ts, resposta}:
      (S.Final{w, ts, resposta}, L.Ambos{{==}, L.prefixo_refl(S.Evento, ts)})
    case 1n+k N.EmCurso{w, a, ts}:
      passo_com_prefixo(S.passo(a, e, w), k, e, ts,
        proxima => percurso_com_prefixo(k, proxima, e))
    case 1n+k N.Parada{+w, +ts, +resposta}:
      (S.Final{w, ts, resposta}, L.Ambos{N.parada_absorve(1n+k, w, ts, resposta, e), L.prefixo_refl(S.Evento, ts)})

def extrair_prefixo(-n: Nat, -m: N.Maquina, -e: D.Esquema,
  resultado: PercursoComPrefixo(n, m, e)) ->
  L.Prefixo(S.Evento, S.eventos_percurso(N.instantaneo(m)), S.eventos_percurso(N.percorrer(n, m, e))):
  match resultado:
    case (percurso, L.Ambos{igualdade, prefixo}):
      %Equal.sym(S.Percurso, N.percorrer(n, m, e), percurso, igualdade) :
        L.Prefixo(S.Evento, S.eventos_percurso(N.instantaneo(m)), S.eventos_percurso(_))
      prefixo

law percorrer_conserva_eventos_anteriores:
  for +n: Nat
  for m: N.Maquina
  for +e: D.Esquema
  L.Prefixo(S.Evento, S.eventos_percurso(N.instantaneo(m)), S.eventos_percurso(N.percorrer(n, m, e)))
def percorrer_conserva_eventos_anteriores(n, m, e):
  extrair_prefixo(n, m, e, percurso_com_prefixo(n, m, e))

law prefixos_da_maquina_em_ordem:
  for n: Nat
  for +adicionais: Nat
  for m: N.Maquina
  for +e: D.Esquema
  L.Prefixo(S.Evento, S.eventos_percurso(N.percorrer(n, m, e)),
    S.eventos_percurso(N.percorrer(Nat.add(n, adicionais), m, e)))
def prefixos_da_maquina_em_ordem(n, adicionais, m, e):
  match n:
    case 0n:
      percorrer_conserva_eventos_anteriores(adicionais, m, e)
    case 1n+k:
      prefixos_da_maquina_em_ordem(k, adicionais, N.avancar(m, e), e)

law resultado_vincula_transicao:
  for resultado: D.ResultadoOp
  for -s: D.Estado
  for -o: D.Operacao
  for -k: S.Retorno -> S.Acao
  for -ts: List<&2, S.Evento>
  V.AposOperacao(resultado, s, o, ts,
    N.instantaneo(N.passo_maquina(S.aplicar(resultado, s, o, k), ts)))
def resultado_vincula_transicao(resultado, s, o, k, ts):
  match resultado:
    case D.FalhaDados{}:
      {==}
    case D.Observado{observacao}:
      L.Ambos{{==}, {==}}
    case D.Alterado{w}:
      L.Ambos{{==}, {==}}

law operacao_real_vincula_transicao:
  for +e: D.Esquema
  for +s: D.Estado
  for +o: D.Operacao
  for -k: S.Retorno -> S.Acao
  for -ts: List<&2, S.Evento>
  V.AposOperacao(D.operar(e, s, o), s, o, ts,
    N.instantaneo(N.avancar(N.EmCurso{s, S.Acessar{o, k}, ts}, e)))
def operacao_real_vincula_transicao(e, s, o, k, ts):
  resultado_vincula_transicao(D.operar(e, s, o), s, o, k, ts)

law iniciar_usa_exatamente_programa_contexto_argumentos_e_estado:
  for -p: S.Programa
  for -ctx: D.Contexto
  for -args: D.Valor
  for -s: D.Estado
  {N.iniciar(p, ctx, args, s) == N.EmCurso{s, S.iniciar(p, ctx, args), Nil{}} : N.Maquina}
def iniciar_usa_exatamente_programa_contexto_argumentos_e_estado(p, ctx, args, s):
  {==}

law terminacao_da_referencia_implica_terminacao_incremental:
  for p: S.Programa
  for +e: D.Esquema
  for +s: D.Estado
  for +ctx: D.Contexto
  for +args: D.Valor
  for termina: I.Termina(p, e, s, ctx, args)
  exs n: Nat
  exs w: D.Estado
  exs ts: List<&2, S.Evento>
  exs r: S.Resposta
  {N.percorrer(n, N.iniciar(p, ctx, args, s), e) == S.Final{w, ts, r} : S.Percurso}
def terminacao_da_referencia_implica_terminacao_incremental(p, e, s, ctx, args, termina):
  match termina:
    case (+n, w, ts, r, referencia):
      (n, w, ts, r, Equal.trans(S.Percurso,
        N.percorrer(n, N.iniciar(p, ctx, args, s), e), S.executar(n, p, e, s, ctx, args),
        S.Final{w, ts, r}, N.fidelidade_de_todos_os_prefixos(n, p, ctx, args, e, s), referencia))
