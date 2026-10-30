# Ordem, resposta e unicidade da conclusao real; a recepcao fornece o fechamento correto.
import Base
import ./Lei34Servico.bend as Adm
import ./CodecOctetos.bend as Octetos
import ./EntradaServico.bend as Causas
import ../src/Codec.bend as Codec
import ../contrato/Bytes.bend as B
import ./CanalServico.bend as Canal
import ./LigacaoServico.bend as Lig
import ./VisibilidadeServico.bend as Vis
import ../contrato/Recursos.bend as X
import ../src/Entrada.bend as Entrada
import ../src/Transporte.bend as Transporte
import ./Lei2Servico.bend as Dois
import ./FechosServico.bend as Fechos
import ./ErrosFixos.bend as Erros
import ../contrato/Dados.bend as D
import ../contrato/Semantica.bend as S
import ../contrato/Interface.bend as I
import ../contrato/LAWS.bend as K
import ../contrato/Logica.bend as L
import ./FasesServico.bend as Fases
import ./ProtocoloServico.bend as Q
import ./RotasServico.bend as H
import ./Publicacao.bend as U
import ./Preparacao.bend as Preparacao
import ./Fundamentos.bend as F
import ./Chamada.bend as Chamada
import ../src/Nucleo.bend as N

import ../contrato/Requisitos.bend as R
import ./Lei5Servico.bend as Lei5
import ../contrato/Protocolo.bend as P
import ./FonteServico.bend as Fonte
import ./ExecucaoServico.bend as Exec

import ./HistoricoServico.bend as Historia



def resposta_concluida(q: Q.Quadro) -> Maybe<&2, S.Resposta>:
  match q:
    case Q.Concluida{r, s, fecha}: Some{r}
    case _: None{}

def estado_concluido(q: Q.Quadro) -> Maybe<&2, D.Estado>:
  match q:
    case Q.Concluida{r, s, fecha}: Some{s}
    case _: None{}

def fato_da_conclusao(q: Q.Quadro) -> I.Fato:
  match q:
    case Q.Concluida{r, s, fecha}: I.Concluiu{r, s, fecha}
    case _: I.EncerrouCanal{}

# A resposta abaixo e ligada a ultima avaliacao REAL do mesmo percurso.
law ultima_avaliacao_do_resultado_real:
  for ~fonte: Fonte.Fonte
  for ~c: S.Configuracao
  for +s: D.Estado
  for +req: P.Requisicao
  for +ctx: D.Contexto
  for +origem: Fonte.JuizoSintatico
  for +n: Nat
  for +w: D.Estado
  for +ts: List<&2, S.Evento>
  for +proposta: S.Resposta
  for +quadros: List<&2, Q.QuadroExec>
  for sequencia: {quadros == Exec.gerar(n, N.iniciar(Fonte.programa(fonte, origem), ctx, I.argumentos(req), s), S.esquema(c)) : List<&2, Q.QuadroExec>}
  for resultado: {N.percorrer(n, N.iniciar(Fonte.programa(fonte, origem), ctx, I.argumentos(req), s), S.esquema(c)) == S.Final{w, ts, proposta} : S.Percurso}
  exs i: Nat
  {Exec.consultar(quadros, i) == Some{Q.Avaliacao{S.Final{w, ts, proposta}}} : Maybe<&2, Q.QuadroExec>}
def ultima_avaliacao_do_resultado_real(fonte, c, s, req, ctx, origem, n, w, ts, proposta, quadros, sequencia, resultado):
  Exec.ultimo_presente_tem_indice(quadros, Q.Avaliacao{S.Final{w, ts, proposta}},
    Equal.trans(Maybe<&2, Q.QuadroExec>, Exec.ultimo(quadros),
      Exec.ultimo(Exec.gerar(n, N.iniciar(Fonte.programa(fonte, origem), ctx, I.argumentos(req), s), S.esquema(c))),
      Some{Q.Avaliacao{S.Final{w, ts, proposta}}},
      Equal.cong(List<&2, Q.QuadroExec>, Maybe<&2, Q.QuadroExec>, Exec.ultimo,
        quadros, Exec.gerar(n, N.iniciar(Fonte.programa(fonte, origem), ctx, I.argumentos(req), s), S.esquema(c)), sequencia),
      Equal.trans(Maybe<&2, Q.QuadroExec>,
        Exec.ultimo(Exec.gerar(n, N.iniciar(Fonte.programa(fonte, origem), ctx, I.argumentos(req), s), S.esquema(c))),
        Some{Q.Avaliacao{N.percorrer(n, N.iniciar(Fonte.programa(fonte, origem), ctx, I.argumentos(req), s), S.esquema(c))}},
        Some{Q.Avaliacao{S.Final{w, ts, proposta}}},
        Exec.ultimo_representa_todo_percurso(n, N.iniciar(Fonte.programa(fonte, origem), ctx, I.argumentos(req), s), S.esquema(c)),
        Equal.cong(S.Percurso, Maybe<&2, Q.QuadroExec>, p => Some{Q.Avaliacao{p}},
          N.percorrer(n, N.iniciar(Fonte.programa(fonte, origem), ctx, I.argumentos(req), s), S.esquema(c)), S.Final{w, ts, proposta}, resultado))))

law menor_que_soma_por_direita:
  for a: Nat
  for b: Nat
  for -c: Nat
  for menor: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_lt(a, Nat.add(b, c)) == True{} : Bool}
def menor_que_soma_por_direita(a, b, c, menor):
  match a b:
    case 0n 0n: F.absurdo_booleano({Nat.is_lt(0n, c) == True{} : Bool}, menor)
    case 0n 1n+k: {==}
    case 1n+j 0n: F.absurdo_booleano({Nat.is_lt(1n+j, c) == True{} : Bool}, menor)
    case 1n+j 1n+k: menor_que_soma_por_direita(j, k, c, menor)

def final_no_prefixo(+antes: List<&2, Q.Quadro>, +depois: List<&2, Q.Quadro>,
  +r: P.Requisicao, +ctx: D.Contexto, +w: D.Estado, +ts: List<&2, S.Evento>, +proposta: S.Resposta, +fim: Nat,
  indice: &i: Nat -> {Q.consultar(antes, i) == Some{Q.Avaliada{r, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>}) ->
  &u: Nat -> L.E<{Nat.is_lt(u, Nat.add(Q.tamanho(antes), fim)) == True{} : Bool},
    {Q.consultar(Q.concatenar(antes, depois), u) == Some{Q.Avaliada{r, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>}>:
  match indice:
    case (+i, consulta):
      F.com_par((&u: Nat -> L.E<{Nat.is_lt(u, Nat.add(Q.tamanho(antes), fim)) == True{} : Bool},
          {Q.consultar(Q.concatenar(antes, depois), u) == Some{Q.Avaliada{r, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>}>),
        {Q.consultar(antes, i) == Some{Q.Avaliada{r, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>},
        {Q.consultar(antes, i) == Some{Q.Avaliada{r, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>},
        Chamada.duplicar_igualdade(Maybe<&2, Q.Quadro>, Q.consultar(antes, i), Some{Q.Avaliada{r, ctx, S.Final{w, ts, proposta}}}, consulta),
        limite => fato => (i, L.Ambos{
          menor_que_soma_por_direita(i, Q.tamanho(antes), fim, Q.posicao_presente_dentro(antes, i, Q.Avaliada{r, ctx, S.Final{w, ts, proposta}}, limite)),
          Lei5.consulta_do_subtraco(Nil{}, antes, depois, i, Q.Avaliada{r, ctx, S.Final{w, ts, proposta}}, fato)}))

def resposta_final_com_avaliacao(~fonte: Fonte.Fonte, -a: I.Ambiente, -k: String, -x: I.Cenario,
  +antes: List<&2, Q.Quadro>, +depois: List<&2, Q.Quadro>, +fim: Nat, +req: P.Requisicao,
  +ctx: D.Contexto, +origem: Fonte.JuizoSintatico, +w: D.Estado, +ts: List<&2, S.Evento>, +proposta: S.Resposta,
  -resposta: S.Resposta, finalizada: {R.finalizar(proposta, I.configuracao(x), w) == resposta : S.Resposta},
  indice: &u: Nat -> L.E<{Nat.is_lt(u, Nat.add(Q.tamanho(antes), fim)) == True{} : Bool},
    {Q.consultar(Q.concatenar(antes, depois), u) == Some{Q.Avaliada{req, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>}>,
  introduzir: @u: Nat -> {Q.consultar(Q.concatenar(antes, depois), u) == Some{Q.Avaliada{req, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>} ->
    I.Acontece(a, k, x, u, I.Avaliou{req, ctx, Fonte.programa(fonte, origem), S.Final{w, ts, proposta}})) ->
  I.RespostaDoPrograma(a, k, x, Nat.add(Q.tamanho(antes), fim), resposta, w):
  match indice:
    case (+u, L.Ambos{ordem, consulta}):
      (req, ctx, Fonte.programa(fonte, origem), ts, proposta, L.Ambos{(u, L.Ambos{ordem, introduzir(u, consulta)}), finalizada})

law resposta_final_tem_causa_na_avaliacao_real:
  for ~fonte: Fonte.Fonte
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for +antes: List<&2, Q.Quadro>
  for +depois: List<&2, Q.Quadro>
  for +fim: Nat
  for +req: P.Requisicao
  for +ctx: D.Contexto
  for +origem: Fonte.JuizoSintatico
  for +w: D.Estado
  for +ts: List<&2, S.Evento>
  for +proposta: S.Resposta
  for -resposta: S.Resposta
  for finalizada: {R.finalizar(proposta, I.configuracao(x), w) == resposta : S.Resposta}
  for indice: &i: Nat -> {Q.consultar(antes, i) == Some{Q.Avaliada{req, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>}
  for introduzir: @u: Nat -> {Q.consultar(Q.concatenar(antes, depois), u) == Some{Q.Avaliada{req, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>} ->
    I.Acontece(a, k, x, u, I.Avaliou{req, ctx, Fonte.programa(fonte, origem), S.Final{w, ts, proposta}})
  I.RespostaDoPrograma(a, k, x, Nat.add(Q.tamanho(antes), fim), resposta, w)
def resposta_final_tem_causa_na_avaliacao_real(fonte, a, k, x, antes, depois, fim, req, ctx, origem, w, ts, proposta, resposta, finalizada, indice, introduzir):
  resposta_final_com_avaliacao(fonte, a, k, x, antes, depois, fim, req, ctx, origem, w, ts, proposta, resposta, finalizada,
    final_no_prefixo(antes, depois, req, ctx, w, ts, proposta, fim, indice), introduzir)

# Entrega completa: marcos reais, preparacao anterior e exclusao de entrega parcial.
def antes_da_entrega(+antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta,
  +bs: List<&2, U32>, +fecha: Bool) -> List<&2, Q.Quadro>:
  Q.concatenar(antes, Con{Q.Preparada{r, bs}, Q.concatenar(H.render_publicacao(r, s), [Q.Concluida{r, s, fecha}])})

law separar_entrega:
  for +antes: List<&2, Q.Quadro>
  for +s: D.Estado
  for +r: S.Resposta
  for +bs: List<&2, U32>
  for +fecha: Bool
  for +entrega: H.Entrega
  {Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega)) ==
    Q.concatenar(antes_da_entrega(antes, s, r, bs, fecha), H.render_entrega(s, bs, fecha, entrega)) : List<&2, Q.Quadro>}
def separar_entrega(antes, s, r, bs, fecha, entrega):
  Equal.sym(List<&2, Q.Quadro>,
    Q.concatenar(antes_da_entrega(antes, s, r, bs, fecha), H.render_entrega(s, bs, fecha, entrega)),
    Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega)),
    Equal.trans(List<&2, Q.Quadro>,
      Q.concatenar(antes_da_entrega(antes, s, r, bs, fecha), H.render_entrega(s, bs, fecha, entrega)),
      Q.concatenar(antes, Q.concatenar(Con{Q.Preparada{r, bs}, Q.concatenar(H.render_publicacao(r, s), [Q.Concluida{r, s, fecha}])}, H.render_entrega(s, bs, fecha, entrega))),
      Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega)),
      Q.concatenar_assoc(antes, Con{Q.Preparada{r, bs}, Q.concatenar(H.render_publicacao(r, s), [Q.Concluida{r, s, fecha}])}, H.render_entrega(s, bs, fecha, entrega)),
      Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, resto => Q.concatenar(antes, Con{Q.Preparada{r, bs}, resto}),
        Q.concatenar(Q.concatenar(H.render_publicacao(r, s), [Q.Concluida{r, s, fecha}]), H.render_entrega(s, bs, fecha, entrega)),
        Q.concatenar(H.render_publicacao(r, s), Con{Q.Concluida{r, s, fecha}, H.render_entrega(s, bs, fecha, entrega)}),
        Q.concatenar_assoc(H.render_publicacao(r, s), [Q.Concluida{r, s, fecha}], H.render_entrega(s, bs, fecha, entrega)))))

def publicacao_sem_marca(+tipo: Fases.Tipo, r: S.Resposta, +s: D.Estado,
  nao: {Fases.desse_tipo(tipo, Q.Publicada{s}) == False{} : Bool}) ->
  {Fases.ausente(tipo, H.render_publicacao(r, s)) == True{} : Bool}:
  match r:
    case S.Resposta{S.Sucesso{}, v}:
      F.e_booleano_intro(Bool.not(Fases.desse_tipo(tipo, Q.Publicada{s})), True{},
        Equal.cong(Bool, Bool, Bool.not, Fases.desse_tipo(tipo, Q.Publicada{s}), False{}, nao), {==})
    case S.Resposta{S.Recusa{}, v}: {==}
    case S.Resposta{S.Entrada{}, v}: {==}
    case S.Resposta{S.Autenticacao{}, v}: {==}
    case S.Resposta{S.Certificado{}, v}: {==}
    case S.Resposta{S.Dados{}, v}: {==}
    case S.Resposta{S.Limite{}, v}: {==}
    case S.Resposta{S.Falha{}, v}: {==}

def antes_da_entrega_sem_marca(+tipo: Fases.Tipo, +antes: List<&2, Q.Quadro>, +s: D.Estado,
  +r: S.Resposta, +bs: List<&2, U32>, +fecha: Bool,
  sem: {Fases.ausente(tipo, antes) == True{} : Bool},
  preparo: {Fases.desse_tipo(tipo, Q.Preparada{r, bs}) == False{} : Bool},
  publicacao: {Fases.desse_tipo(tipo, Q.Publicada{s}) == False{} : Bool},
  conclusao: {Fases.desse_tipo(tipo, Q.Concluida{r, s, fecha}) == False{} : Bool}) ->
  {Fases.ausente(tipo, antes_da_entrega(antes, s, r, bs, fecha)) == True{} : Bool}:
  Fases.concatenar_ausencia(tipo, antes, Con{Q.Preparada{r, bs}, Q.concatenar(H.render_publicacao(r, s), [Q.Concluida{r, s, fecha}])}, sem,
    F.e_booleano_intro(Bool.not(Fases.desse_tipo(tipo, Q.Preparada{r, bs})),
      Fases.ausente(tipo, Q.concatenar(H.render_publicacao(r, s), [Q.Concluida{r, s, fecha}])),
      Equal.cong(Bool, Bool, Bool.not, Fases.desse_tipo(tipo, Q.Preparada{r, bs}), False{}, preparo),
      Fases.concatenar_ausencia(tipo, H.render_publicacao(r, s), [Q.Concluida{r, s, fecha}], publicacao_sem_marca(tipo, r, s, publicacao),
        F.e_booleano_intro(Bool.not(Fases.desse_tipo(tipo, Q.Concluida{r, s, fecha})), True{},
          Equal.cong(Bool, Bool, Bool.not, Fases.desse_tipo(tipo, Q.Concluida{r, s, fecha}), False{}, conclusao), {==}))))

def entrega_completa_localizada(+antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta,
  +bs: List<&2, U32>, +fecho: Bool, +proxima: Bool, +t: Nat, +q: Q.Quadro,
  sem: {Fases.ausente(Fases.Completa{}, antes) == True{} : Bool},
  alvo: {Fases.desse_tipo(Fases.Completa{}, q) == True{} : Bool},
  consulta: {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), t) == Some{q} : Maybe<&2, Q.Quadro>}) ->
  L.E<{t == Q.tamanho(antes_da_entrega(antes, s, r, bs, fecho)) : Nat}, {q == Q.Entregue{bs} : Q.Quadro}>:
  Fases.marca_unica_entre_partes_ausentes(Fases.Completa{}, antes_da_entrega(antes, s, r, bs, fecho), H.depois_entrega(fecho, s, proxima), Q.Entregue{bs}, t, q,
    antes_da_entrega_sem_marca(Fases.Completa{}, antes, s, r, bs, fecho, sem, {==}, {==}, {==}),
    Fases.depois_entrega_sem_macros(Fases.Completa{}, fecho, s, proxima), alvo,
    Equal.trans(Maybe<&2, Q.Quadro>,
      Q.consultar(Q.concatenar(antes_da_entrega(antes, s, r, bs, fecho), H.render_entrega(s, bs, fecho, H.Completa{proxima})), t),
      Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), t), Some{q},
      Equal.cong(List<&2, Q.Quadro>, Maybe<&2, Q.Quadro>, xs => Q.consultar(xs, t),
        Q.concatenar(antes_da_entrega(antes, s, r, bs, fecho), H.render_entrega(s, bs, fecho, H.Completa{proxima})),
        Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})),
        Equal.sym(List<&2, Q.Quadro>, Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})),
          Q.concatenar(antes_da_entrega(antes, s, r, bs, fecho), H.render_entrega(s, bs, fecho, H.Completa{proxima})), separar_entrega(antes, s, r, bs, fecho, H.Completa{proxima}))), consulta))

def bytes_entregues(q: Q.Quadro) -> Maybe<&2, List<&2, U32>>:
  match q:
    case Q.Entregue{bs}: Some{bs}
    case _: None{}

def entrega_localizada_compara(+antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecho: Bool,
  -u: Nat, -t: Nat, +outros: List<&2, U32>, canonico: {t == Q.tamanho(antes_da_entrega(antes, s, r, bs, fecho)) : Nat},
  local: L.E<{u == Q.tamanho(antes_da_entrega(antes, s, r, bs, fecho)) : Nat}, {Q.Entregue{outros} == Q.Entregue{bs} : Q.Quadro}>) ->
  L.E<{u == t : Nat}, {outros == bs : List<&2, U32>}>:
  match local:
    case L.Ambos{pos, quadro}:
      L.Ambos{Equal.trans(Nat, u, Q.tamanho(antes_da_entrega(antes, s, r, bs, fecho)), t, pos,
        Equal.sym(Nat, t, Q.tamanho(antes_da_entrega(antes, s, r, bs, fecho)), canonico)),
        F.algum_injetivo(List<&2, U32>, outros, bs, Equal.cong(Q.Quadro, Maybe<&2, List<&2, U32>>, bytes_entregues, Q.Entregue{outros}, Q.Entregue{bs}, quadro))}

def fim_completo_sem_interrupcao(+antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta,
  +bs: List<&2, U32>, +fecho: Bool, +proxima: Bool, sem: {Fases.ausente(Fases.Interrompida{}, antes) == True{} : Bool}) ->
  {Fases.ausente(Fases.Interrompida{}, Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima}))) == True{} : Bool}:
  %Equal.sym(List<&2, Q.Quadro>, Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})),
    Q.concatenar(antes_da_entrega(antes, s, r, bs, fecho), H.render_entrega(s, bs, fecho, H.Completa{proxima})),
    separar_entrega(antes, s, r, bs, fecho, H.Completa{proxima})) : {Fases.ausente(Fases.Interrompida{}, _) == True{} : Bool}
  Fases.concatenar_ausencia(Fases.Interrompida{}, antes_da_entrega(antes, s, r, bs, fecho), H.render_entrega(s, bs, fecho, H.Completa{proxima}),
    antes_da_entrega_sem_marca(Fases.Interrompida{}, antes, s, r, bs, fecho, sem, {==}, {==}, {==}),
    Fases.entrega_completa_nunca_quebrada(s, bs, fecho, proxima))

def posicao_da_entrega_completa(+antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecho: Bool,
  +proxima: Bool, +t: Nat, sem: {Fases.ausente(Fases.Completa{}, antes) == True{} : Bool},
  consulta: {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), t) == Some{Q.Entregue{bs}} : Maybe<&2, Q.Quadro>}) ->
  {t == Q.tamanho(antes_da_entrega(antes, s, r, bs, fecho)) : Nat}:
  L.e_esquerda({t == Q.tamanho(antes_da_entrega(antes, s, r, bs, fecho)) : Nat}, {Q.Entregue{bs} == Q.Entregue{bs} : Q.Quadro},
    entrega_completa_localizada(antes, s, r, bs, fecho, proxima, t, Q.Entregue{bs}, sem, {==}, consulta))

def entrega_completa_unica_real(-a: I.Ambiente, -k: String, -x: I.Cenario, +antes: List<&2, Q.Quadro>,
  +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecho: Bool, +proxima: Bool, -t: Nat,
  canonico: {t == Q.tamanho(antes_da_entrega(antes, s, r, bs, fecho)) : Nat},
  sem_completa: {Fases.ausente(Fases.Completa{}, antes) == True{} : Bool},
  sem_interrompida: {Fases.ausente(Fases.Interrompida{}, antes) == True{} : Bool},
  completa: @u: Nat -> @outros: List<&2, U32> -> I.Acontece(a, k, x, u, I.EntregouTudo{outros}) ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), u) == Some{Q.Entregue{outros}} : Maybe<&2, Q.Quadro>},
  interrompida: @u: Nat -> @prefixo: List<&2, U32> -> I.Acontece(a, k, x, u, I.EntregaInterrompida{prefixo}) ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), u) == Some{Q.Interrompida{prefixo}} : Maybe<&2, Q.Quadro>}) ->
  K.EntregaCompletaUnica(a, k, x, t, bs):
  L.Ambos{+u => +outros => fato => entrega_localizada_compara(antes, s, r, bs, fecho, u, t, outros, canonico,
      entrega_completa_localizada(antes, s, r, bs, fecho, proxima, u, Q.Entregue{outros}, sem_completa, {==}, completa(u, outros, fato))),
    +u => +prefixo => fato => Fases.ausente_exclui_consulta(Fases.Interrompida{},
      Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), u, Q.Interrompida{prefixo},
      fim_completo_sem_interrupcao(antes, s, r, bs, fecho, proxima, sem_interrompida), {==}, interrompida(u, prefixo, fato))}

def local_conclusao(+s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>) -> Nat:
  Q.tamanho(Con{Q.Preparada{r, bs}, H.render_publicacao(r, s)})

def indice_entrega(+antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>) -> Nat:
  Nat.add(Q.tamanho(antes), Succ{local_conclusao(s, r, bs)})

def pontos_completos(+antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecho: Bool, +proxima: Bool) ->
  L.E<{Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs))) == Some{Q.Concluida{r, s, fecho}} : Maybe<&2, Q.Quadro>},
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), indice_entrega(antes, s, r, bs)) == Some{Q.Entregue{bs}} : Maybe<&2, Q.Quadro>}>:
  F.com_par(
    L.E<{Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs))) == Some{Q.Concluida{r, s, fecho}} : Maybe<&2, Q.Quadro>},
      {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), indice_entrega(antes, s, r, bs)) == Some{Q.Entregue{bs}} : Maybe<&2, Q.Quadro>}>,
    {Q.consultar(H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima}), local_conclusao(s, r, bs)) == Some{Q.Concluida{r, s, fecho}} : Maybe<&2, Q.Quadro>},
    {Q.consultar(H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima}), Succ{local_conclusao(s, r, bs)}) == Some{Q.Entregue{bs}} : Maybe<&2, Q.Quadro>},
    Q.dois_quadros_apos_prefixo(Con{Q.Preparada{r, bs}, H.render_publicacao(r, s)}, H.depois_entrega(fecho, s, proxima), Q.Concluida{r, s, fecho}, Q.Entregue{bs}),
    conclusao => entrega => L.Ambos{
      Equal.trans(Maybe<&2, Q.Quadro>, Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs))),
        Q.consultar(H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima}), local_conclusao(s, r, bs)), Some{Q.Concluida{r, s, fecho}},
        Q.consultar_apos_prefixo(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima}), local_conclusao(s, r, bs)), conclusao),
      Equal.trans(Maybe<&2, Q.Quadro>, Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), indice_entrega(antes, s, r, bs)),
        Q.consultar(H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima}), Succ{local_conclusao(s, r, bs)}), Some{Q.Entregue{bs}},
        Q.consultar_apos_prefixo(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima}), Succ{local_conclusao(s, r, bs)}), entrega)})

def preparo_no_fim_completo(+antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecho: Bool, +proxima: Bool) ->
  {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), Nat.add(Q.tamanho(antes), 0n)) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>}:
  Q.consultar_apos_prefixo(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima}), 0n)

def posicao_completa_canonica(+antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecho: Bool, +proxima: Bool,
  sem: {Fases.ausente(Fases.Completa{}, antes) == True{} : Bool}) ->
  {indice_entrega(antes, s, r, bs) == Q.tamanho(antes_da_entrega(antes, s, r, bs, fecho)) : Nat}:
  posicao_da_entrega_completa(antes, s, r, bs, fecho, proxima, indice_entrega(antes, s, r, bs), sem,
    L.e_direita(
      {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs))) == Some{Q.Concluida{r, s, fecho}} : Maybe<&2, Q.Quadro>},
      {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), indice_entrega(antes, s, r, bs)) == Some{Q.Entregue{bs}} : Maybe<&2, Q.Quadro>}, pontos_completos(antes, s, r, bs, fecho, proxima)))

def unicidade_completa_canonica(-a: I.Ambiente, -k: String, -x: I.Cenario,
  +antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecho: Bool, +proxima: Bool,
  sem_completa: {Fases.ausente(Fases.Completa{}, antes) == True{} : Bool},
  sem_interrompida: {Fases.ausente(Fases.Interrompida{}, antes) == True{} : Bool},
  completa: @u: Nat -> @outros: List<&2, U32> -> I.Acontece(a, k, x, u, I.EntregouTudo{outros}) ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), u) == Some{Q.Entregue{outros}} : Maybe<&2, Q.Quadro>},
  interrompida: @u: Nat -> @prefixo: List<&2, U32> -> I.Acontece(a, k, x, u, I.EntregaInterrompida{prefixo}) ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), u) == Some{Q.Interrompida{prefixo}} : Maybe<&2, Q.Quadro>}) ->
  K.EntregaCompletaUnica(a, k, x, indice_entrega(antes, s, r, bs), bs):
  F.com_par(K.EntregaCompletaUnica(a, k, x, indice_entrega(antes, s, r, bs), bs),
    {Fases.ausente(Fases.Completa{}, antes) == True{} : Bool}, {Fases.ausente(Fases.Completa{}, antes) == True{} : Bool},
    Chamada.duplicar_igualdade(Bool, Fases.ausente(Fases.Completa{}, antes), True{}, sem_completa),
    indice => outras => entrega_completa_unica_real(a, k, x, antes, s, r, bs, fecho, proxima, indice_entrega(antes, s, r, bs),
      posicao_completa_canonica(antes, s, r, bs, fecho, proxima, indice), outras, sem_interrompida, completa, interrompida))

law entrega_completa_canonica_obedece_regra7:
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for +antes: List<&2, Q.Quadro>
  for +s: D.Estado
  for +r: S.Resposta
  for +bs: List<&2, U32>
  for +fecho: Bool
  for +proxima: Bool
  for sem_completa: {Fases.ausente(Fases.Completa{}, antes) == True{} : Bool}
  for sem_interrompida: {Fases.ausente(Fases.Interrompida{}, antes) == True{} : Bool}
  for preparar: @u: Nat -> @rp: S.Resposta -> @bytes: List<&2, U32> ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), u) == Some{Q.Preparada{rp, bytes}} : Maybe<&2, Q.Quadro>} ->
    I.Acontece(a, k, x, u, I.Preparou{rp, bytes})
  for concluir: @u: Nat -> @rp: S.Resposta -> @w: D.Estado -> @fecha: Bool ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), u) == Some{Q.Concluida{rp, w, fecha}} : Maybe<&2, Q.Quadro>} ->
    I.Acontece(a, k, x, u, I.Concluiu{rp, w, fecha})
  for completa: @u: Nat -> @outros: List<&2, U32> -> I.Acontece(a, k, x, u, I.EntregouTudo{outros}) ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), u) == Some{Q.Entregue{outros}} : Maybe<&2, Q.Quadro>}
  for interrompida: @u: Nat -> @prefixo: List<&2, U32> -> I.Acontece(a, k, x, u, I.EntregaInterrompida{prefixo}) ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), u) == Some{Q.Interrompida{prefixo}} : Maybe<&2, Q.Quadro>}
  K.Regra7(I.EntregouTudo{bs}, a, k, x, indice_entrega(antes, s, r, bs))
def entrega_completa_canonica_obedece_regra7(a, k, x, antes, s, r, bs, fecho, proxima, sem_completa, sem_interrompida,
  preparar, concluir, completa, interrompida):
  (r, s, fecho, L.Ambos{
    (Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs)), L.Ambos{
      Q.ordem_deslocada(Q.tamanho(antes), local_conclusao(s, r, bs), Succ{local_conclusao(s, r, bs)}, Exec.menor_sucessor(local_conclusao(s, r, bs))),
      concluir(Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs)), r, s, fecho,
        L.e_esquerda(
          {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs))) == Some{Q.Concluida{r, s, fecho}} : Maybe<&2, Q.Quadro>},
          {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), indice_entrega(antes, s, r, bs)) == Some{Q.Entregue{bs}} : Maybe<&2, Q.Quadro>}, pontos_completos(antes, s, r, bs, fecho, proxima)))}),
    L.Ambos{(Nat.add(Q.tamanho(antes), 0n), L.Ambos{
        Q.ordem_deslocada(Q.tamanho(antes), 0n, Succ{local_conclusao(s, r, bs)}, {==}),
        preparar(Nat.add(Q.tamanho(antes), 0n), r, bs, preparo_no_fim_completo(antes, s, r, bs, fecho, proxima))}),
      unicidade_completa_canonica(a, k, x, antes, s, r, bs, fecho, proxima, sem_completa, sem_interrompida, completa, interrompida)}})

def transportar_entrega7(-a: I.Ambiente, -k: String, -x: I.Cenario, +antes: List<&2, Q.Quadro>,
  +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, -t: Nat, +outros: List<&2, U32>,
  igual: L.E<{t == indice_entrega(antes, s, r, bs) : Nat}, {outros == bs : List<&2, U32>}>,
  canonica: K.Regra7(I.EntregouTudo{bs}, a, k, x, indice_entrega(antes, s, r, bs))) ->
  K.Regra7(I.EntregouTudo{outros}, a, k, x, t):
  match igual:
    case L.Ambos{pos, bytes}:
      %Equal.sym(Nat, t, indice_entrega(antes, s, r, bs), pos) : K.Regra7(I.EntregouTudo{outros}, a, k, x, _)
      %Equal.sym(List<&2, U32>, outros, bs, bytes) : K.Regra7(I.EntregouTudo{_}, a, k, x, indice_entrega(antes, s, r, bs))
      canonica

law entrega_completa_refletida_obedece_regra7:
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for +antes: List<&2, Q.Quadro>
  for +s: D.Estado
  for +r: S.Resposta
  for +bs: List<&2, U32>
  for +fecho: Bool
  for +proxima: Bool
  for +t: Nat
  for +outros: List<&2, U32>
  for consulta: {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), t) == Some{Q.Entregue{outros}} : Maybe<&2, Q.Quadro>}
  for sem_completa: {Fases.ausente(Fases.Completa{}, antes) == True{} : Bool}
  for sem_interrompida: {Fases.ausente(Fases.Interrompida{}, antes) == True{} : Bool}
  for preparar: @u: Nat -> @rp: S.Resposta -> @bytes: List<&2, U32> ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), u) == Some{Q.Preparada{rp, bytes}} : Maybe<&2, Q.Quadro>} ->
    I.Acontece(a, k, x, u, I.Preparou{rp, bytes})
  for concluir: @u: Nat -> @rp: S.Resposta -> @w: D.Estado -> @fecha: Bool ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), u) == Some{Q.Concluida{rp, w, fecha}} : Maybe<&2, Q.Quadro>} ->
    I.Acontece(a, k, x, u, I.Concluiu{rp, w, fecha})
  for completa: @u: Nat -> @bytes: List<&2, U32> -> I.Acontece(a, k, x, u, I.EntregouTudo{bytes}) ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), u) == Some{Q.Entregue{bytes}} : Maybe<&2, Q.Quadro>}
  for interrompida: @u: Nat -> @prefixo: List<&2, U32> -> I.Acontece(a, k, x, u, I.EntregaInterrompida{prefixo}) ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), u) == Some{Q.Interrompida{prefixo}} : Maybe<&2, Q.Quadro>}
  K.Regra7(I.EntregouTudo{outros}, a, k, x, t)
def entrega_completa_refletida_obedece_regra7(a, k, x, antes, s, r, bs, fecho, proxima, t, outros, consulta, sem_completa, sem_interrompida,
  preparar, concluir, completa, interrompida):
  F.com_par(K.Regra7(I.EntregouTudo{outros}, a, k, x, t),
    {Fases.ausente(Fases.Completa{}, antes) == True{} : Bool}, {Fases.ausente(Fases.Completa{}, antes) == True{} : Bool},
    Chamada.duplicar_igualdade(Bool, Fases.ausente(Fases.Completa{}, antes), True{}, sem_completa),
    atual => resto => F.com_par(K.Regra7(I.EntregouTudo{outros}, a, k, x, t),
      {Fases.ausente(Fases.Completa{}, antes) == True{} : Bool}, {Fases.ausente(Fases.Completa{}, antes) == True{} : Bool},
      Chamada.duplicar_igualdade(Bool, Fases.ausente(Fases.Completa{}, antes), True{}, resto),
      pos => canonica => transportar_entrega7(a, k, x, antes, s, r, bs, t, outros,
        entrega_localizada_compara(antes, s, r, bs, fecho, t, indice_entrega(antes, s, r, bs), outros,
          posicao_completa_canonica(antes, s, r, bs, fecho, proxima, pos),
          entrega_completa_localizada(antes, s, r, bs, fecho, proxima, t, Q.Entregue{outros}, atual, {==}, consulta)),
        entrega_completa_canonica_obedece_regra7(a, k, x, antes, s, r, bs, fecho, proxima, canonica, sem_interrompida, preparar, concluir, completa, interrompida))))

# Publicacao deriva validade do historico e resposta da avaliacao real.
def OrigemDaFonte(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado, +origem: Fonte.JuizoSintatico,
  registro: Historia.Registro) -> Type:
  match registro:
    case Historia.Registro{req, ctx, n, w, ts, proposta, preparada}:
      L.E<R.Certifica(c, I.codigo(req), Fonte.programa(fonte, origem), ctx, I.argumentos(req)),
        L.E<{D.autenticar(s, I.credencial(req)) == Some{ctx} : Maybe<&2, D.Contexto>},
          L.E<{N.percorrer(n, N.iniciar(Fonte.programa(fonte, origem), ctx, I.argumentos(req), s), S.esquema(c)) == S.Final{w, ts, proposta} : S.Percurso},
            {N.preparar(N.Parada{w, ts, proposta}, c) == Some{preparada} : Maybe<&2, N.Preparada>}>>>

def historico_da_fonte(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado, +origem: Fonte.JuizoSintatico,
  +registro: Historia.Registro, prova: OrigemDaFonte(fonte, c, s, origem, registro)) -> Historia.Origem(c, s, registro):
  match registro:
    case Historia.Registro{req, ctx, n, w, ts, proposta, preparada}:
      (Fonte.programa(fonte, origem), prova)

def transportar_publicacao6(-a: I.Ambiente, -k: String, -x: I.Cenario, +antes: List<&2, Q.Quadro>,
  +w: D.Estado, -t: Nat, +publicado: D.Estado,
  igual: L.E<{t == Nat.add(Q.tamanho(antes), 1n) : Nat}, {publicado == w : D.Estado}>,
  canonica: K.Regra6(I.Publicou{w}, a, k, x, Nat.add(Q.tamanho(antes), 1n))) -> K.Regra6(I.Publicou{publicado}, a, k, x, t):
  match igual:
    case L.Ambos{pos, estado}:
      %Equal.sym(Nat, t, Nat.add(Q.tamanho(antes), 1n), pos) : K.Regra6(I.Publicou{publicado}, a, k, x, _)
      %Equal.sym(D.Estado, publicado, w, estado) : K.Regra6(I.Publicou{_}, a, k, x, Nat.add(Q.tamanho(antes), 1n))
      canonica

def proposta_nao_fabrica_status_host(~fonte: Fonte.Fonte, ~c: S.Configuracao, +s: D.Estado,
  +req: P.Requisicao, +ctx: D.Contexto, +origem: Fonte.JuizoSintatico, +n: Nat,
  +w: D.Estado, +ts: List<&2, S.Evento>, +proposta: S.Resposta,
  resultado: {N.percorrer(n, N.iniciar(Fonte.programa(fonte, origem), ctx, I.argumentos(req), s), S.esquema(c)) == S.Final{w, ts, proposta} : S.Percurso}) ->
  Fases.DoCodigo(proposta):
  %resultado : Fases.PercursoDoCodigo(_)
  Fases.percurso_nao_fabrica_status_do_host(n, N.iniciar(Fonte.programa(fonte, origem), ctx, I.argumentos(req), s), S.esquema(c), Unit{})

def resposta_preparada_de_fiel(~c: S.Configuracao, +w: D.Estado, +ts: List<&2, S.Evento>,
  +proposta: S.Resposta, +r: S.Resposta, +bs: List<&2, U32>,
  fiel: Preparacao.Fiel(w, ts, R.finalizar(proposta, c, w), N.Preparada{w, ts, r, bs})) ->
  {R.finalizar(proposta, c, w) == r : S.Resposta}:
  match fiel:
    case L.Ambos{igual, mensagem}:
      Equal.sym(S.Resposta, r, R.finalizar(proposta, c, w), Equal.cong(N.Preparada, S.Resposta, U.resposta,
        N.Preparada{w, ts, r, bs}, N.Preparada{w, ts, R.finalizar(proposta, c, w), bs}, igual))

def resposta_preparada_e_finalizacao(~c: S.Configuracao, +w: D.Estado, +ts: List<&2, S.Evento>,
  +proposta: S.Resposta, +r: S.Resposta, +bs: List<&2, U32>,
  obtida: {N.preparar(N.Parada{w, ts, proposta}, c) == Some{N.Preparada{w, ts, r, bs}} : Maybe<&2, N.Preparada>}) ->
  {R.finalizar(proposta, c, w) == r : S.Resposta}:
  resposta_preparada_de_fiel(c, w, ts, proposta, r, bs,
    Preparacao.preparar_preserva_resposta_estado_eventos_e_bytes(N.Parada{w, ts, proposta}, c, N.Preparada{w, ts, r, bs}, obtida))

def dados_preparados_do_cenario(~c: S.Configuracao, -x: I.Cenario, +w: D.Estado, +ts: List<&2, S.Evento>,
  +proposta: S.Resposta, +r: S.Resposta, +bs: List<&2, U32>,
  obtida: {N.preparar(N.Parada{w, ts, proposta}, c) == Some{N.Preparada{w, ts, r, bs}} : Maybe<&2, N.Preparada>},
  configuracao: {I.configuracao(x) == c : S.Configuracao}, valida: {R.configuracao_valida(c) == True{} : Bool}) ->
  Fases.DadosPreparados(I.configuracao(x), N.Preparada{w, ts, r, bs}):
  %Equal.sym(S.Configuracao, I.configuracao(x), c, configuracao) : Fases.DadosPreparados(_, N.Preparada{w, ts, r, bs})
  Fases.preparar_real_garante_payload_mensagem_e_tamanho(c, w, ts, proposta, N.Preparada{w, ts, r, bs}, obtida,
    Preparacao.limites_da_configuracao(c, valida))

def causa_do_preparo(~fonte: Fonte.Fonte, ~c: S.Configuracao, -a: I.Ambiente, -k: String, -x: I.Cenario,
  +antes: List<&2, Q.Quadro>, +depois: List<&2, Q.Quadro>, +req: P.Requisicao, +ctx: D.Contexto,
  +origem: Fonte.JuizoSintatico, +w: D.Estado, +ts: List<&2, S.Evento>, +proposta: S.Resposta, +r: S.Resposta,
  configuracao: {I.configuracao(x) == c : S.Configuracao}, finalizada: {R.finalizar(proposta, c, w) == r : S.Resposta},
  do_codigo: Fases.DoCodigo(proposta),
  indice: &i: Nat -> {Q.consultar(antes, i) == Some{Q.Avaliada{req, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>},
  avaliar: @u: Nat -> {Q.consultar(Q.concatenar(antes, depois), u) == Some{Q.Avaliada{req, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>} ->
    I.Acontece(a, k, x, u, I.Avaliou{req, ctx, Fonte.programa(fonte, origem), S.Final{w, ts, proposta}})) ->
  I.RespostaJustificada(r, a, k, x, Nat.add(Q.tamanho(antes), 0n)):
  %finalizada : I.RespostaJustificada(_, a, k, x, Nat.add(Q.tamanho(antes), 0n))
  Fases.resposta_de_programa_justifica_o_status_real(a, k, x, Nat.add(Q.tamanho(antes), 0n), R.finalizar(proposta, c, w), w,
    Fases.finalizar_so_acrescenta_dados_ou_limite(proposta, c, w, do_codigo),
    resposta_final_tem_causa_na_avaliacao_real(fonte, a, k, x, antes, depois, 0n, req, ctx, origem, w, ts, proposta,
      R.finalizar(proposta, c, w), Equal.cong(S.Configuracao, S.Resposta, cfg => R.finalizar(proposta, cfg, w),
        I.configuracao(x), c, configuracao), indice, avaliar))

def reunir_preparo(-a: I.Ambiente, -k: String, -x: I.Cenario, -t: Nat, -w: D.Estado, -ts: List<&2, S.Evento>,
  +r: S.Resposta, +bs: List<&2, U32>, dados: Fases.DadosPreparados(I.configuracao(x), N.Preparada{w, ts, r, bs}),
  causa: I.RespostaJustificada(r, a, k, x, t)) -> K.Regra7(I.Preparou{r, bs}, a, k, x, t):
  match dados:
    case L.Ambos{valor, L.Ambos{mensagem, tamanho}}: L.Ambos{valor, L.Ambos{mensagem, L.Ambos{tamanho, causa}}}

law preparo_de_programa_obedece_regra7:
  for ~fonte: Fonte.Fonte
  for ~c: S.Configuracao
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for +antes: List<&2, Q.Quadro>
  for +depois: List<&2, Q.Quadro>
  for +s: D.Estado
  for +req: P.Requisicao
  for +ctx: D.Contexto
  for +origem: Fonte.JuizoSintatico
  for +n: Nat
  for +w: D.Estado
  for +ts: List<&2, S.Evento>
  for +proposta: S.Resposta
  for +r: S.Resposta
  for +bs: List<&2, U32>
  for configuracao: {I.configuracao(x) == c : S.Configuracao}
  for valida: {R.configuracao_valida(c) == True{} : Bool}
  for obtida: {N.preparar(N.Parada{w, ts, proposta}, c) == Some{N.Preparada{w, ts, r, bs}} : Maybe<&2, N.Preparada>}
  for resultado: {N.percorrer(n, N.iniciar(Fonte.programa(fonte, origem), ctx, I.argumentos(req), s), S.esquema(c)) == S.Final{w, ts, proposta} : S.Percurso}
  for indice: &i: Nat -> {Q.consultar(antes, i) == Some{Q.Avaliada{req, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>}
  for avaliar: @u: Nat -> {Q.consultar(Q.concatenar(antes, depois), u) == Some{Q.Avaliada{req, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>} ->
    I.Acontece(a, k, x, u, I.Avaliou{req, ctx, Fonte.programa(fonte, origem), S.Final{w, ts, proposta}})
  K.Regra7(I.Preparou{r, bs}, a, k, x, Nat.add(Q.tamanho(antes), 0n))
def preparo_de_programa_obedece_regra7(fonte, c, a, k, x, antes, depois, s, req, ctx, origem, n, w, ts, proposta, r, bs,
  configuracao, valida, obtida, resultado, indice, avaliar):
  F.com_par(K.Regra7(I.Preparou{r, bs}, a, k, x, Nat.add(Q.tamanho(antes), 0n)),
    {I.configuracao(x) == c : S.Configuracao}, {I.configuracao(x) == c : S.Configuracao},
    Chamada.duplicar_igualdade(S.Configuracao, I.configuracao(x), c, configuracao),
    dados_cfg => causa_cfg => F.com_par(K.Regra7(I.Preparou{r, bs}, a, k, x, Nat.add(Q.tamanho(antes), 0n)),
      {N.preparar(N.Parada{w, ts, proposta}, c) == Some{N.Preparada{w, ts, r, bs}} : Maybe<&2, N.Preparada>},
      {N.preparar(N.Parada{w, ts, proposta}, c) == Some{N.Preparada{w, ts, r, bs}} : Maybe<&2, N.Preparada>},
      Chamada.duplicar_igualdade(Maybe<&2, N.Preparada>, N.preparar(N.Parada{w, ts, proposta}, c), Some{N.Preparada{w, ts, r, bs}}, obtida),
      dados => resposta => reunir_preparo(a, k, x, Nat.add(Q.tamanho(antes), 0n), w, ts, r, bs,
        dados_preparados_do_cenario(c, x, w, ts, proposta, r, bs, dados, dados_cfg, valida),
        causa_do_preparo(fonte, c, a, k, x, antes, depois, req, ctx, origem, w, ts, proposta, r, causa_cfg,
          resposta_preparada_e_finalizacao(c, w, ts, proposta, r, bs, resposta),
          proposta_nao_fabrica_status_host(fonte, c, s, req, ctx, origem, n, w, ts, proposta, resultado), indice, avaliar))))

# Uma entrega parcial conserva o prefixo real escrito e nao fabrica entrega completa.
def entrega_parcial_localizada(+antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta,
  +bs: List<&2, U32>, +fecho: Bool, +prefixo: List<&2, U32>, +t: Nat, +q: Q.Quadro,
  sem: {Fases.ausente(Fases.Interrompida{}, antes) == True{} : Bool},
  alvo: {Fases.desse_tipo(Fases.Interrompida{}, q) == True{} : Bool},
  consulta: {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), t) == Some{q} : Maybe<&2, Q.Quadro>}) ->
  L.E<{t == Q.tamanho(antes_da_entrega(antes, s, r, bs, fecho)) : Nat}, {q == Q.Interrompida{prefixo} : Q.Quadro}>:
  Fases.marca_unica_entre_partes_ausentes(Fases.Interrompida{}, antes_da_entrega(antes, s, r, bs, fecho), [Q.Fechada{}], Q.Interrompida{prefixo}, t, q,
    antes_da_entrega_sem_marca(Fases.Interrompida{}, antes, s, r, bs, fecho, sem, {==}, {==}, {==}), {==}, alvo,
    Equal.trans(Maybe<&2, Q.Quadro>,
      Q.consultar(Q.concatenar(antes_da_entrega(antes, s, r, bs, fecho), H.render_entrega(s, bs, fecho, H.Quebrada{prefixo})), t),
      Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), t), Some{q},
      Equal.cong(List<&2, Q.Quadro>, Maybe<&2, Q.Quadro>, xs => Q.consultar(xs, t),
        Q.concatenar(antes_da_entrega(antes, s, r, bs, fecho), H.render_entrega(s, bs, fecho, H.Quebrada{prefixo})),
        Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})),
        Equal.sym(List<&2, Q.Quadro>, Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})),
          Q.concatenar(antes_da_entrega(antes, s, r, bs, fecho), H.render_entrega(s, bs, fecho, H.Quebrada{prefixo})), separar_entrega(antes, s, r, bs, fecho, H.Quebrada{prefixo}))), consulta))

def prefixo_interrompido(q: Q.Quadro) -> Maybe<&2, List<&2, U32>>:
  match q:
    case Q.Interrompida{bs}: Some{bs}
    case _: None{}

def posicao_parcial_compara(+antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecho: Bool,
  +prefixo: List<&2, U32>, -u: Nat, -t: Nat, +outros: List<&2, U32>,
  canonico: {t == Q.tamanho(antes_da_entrega(antes, s, r, bs, fecho)) : Nat},
  local: L.E<{u == Q.tamanho(antes_da_entrega(antes, s, r, bs, fecho)) : Nat}, {Q.Interrompida{outros} == Q.Interrompida{prefixo} : Q.Quadro}>) ->
  L.E<{u == t : Nat}, {outros == prefixo : List<&2, U32>}>:
  match local:
    case L.Ambos{pos, quadro}:
      L.Ambos{Equal.trans(Nat, u, Q.tamanho(antes_da_entrega(antes, s, r, bs, fecho)), t, pos,
          Equal.sym(Nat, t, Q.tamanho(antes_da_entrega(antes, s, r, bs, fecho)), canonico)),
        F.algum_injetivo(List<&2, U32>, outros, prefixo, Equal.cong(Q.Quadro, Maybe<&2, List<&2, U32>>, prefixo_interrompido, Q.Interrompida{outros}, Q.Interrompida{prefixo}, quadro))}

def fim_parcial_sem_completa(+antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecho: Bool,
  +prefixo: List<&2, U32>, sem: {Fases.ausente(Fases.Completa{}, antes) == True{} : Bool}) ->
  {Fases.ausente(Fases.Completa{}, Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo}))) == True{} : Bool}:
  %Equal.sym(List<&2, Q.Quadro>, Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})),
    Q.concatenar(antes_da_entrega(antes, s, r, bs, fecho), H.render_entrega(s, bs, fecho, H.Quebrada{prefixo})),
    separar_entrega(antes, s, r, bs, fecho, H.Quebrada{prefixo})) : {Fases.ausente(Fases.Completa{}, _) == True{} : Bool}
  Fases.concatenar_ausencia(Fases.Completa{}, antes_da_entrega(antes, s, r, bs, fecho), H.render_entrega(s, bs, fecho, H.Quebrada{prefixo}),
    antes_da_entrega_sem_marca(Fases.Completa{}, antes, s, r, bs, fecho, sem, {==}, {==}, {==}), {==})

def pontos_parciais(+antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecho: Bool, +prefixo: List<&2, U32>) ->
  L.E<{Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs))) == Some{Q.Concluida{r, s, fecho}} : Maybe<&2, Q.Quadro>},
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), indice_entrega(antes, s, r, bs)) == Some{Q.Interrompida{prefixo}} : Maybe<&2, Q.Quadro>}>:
  F.com_par(
    L.E<{Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs))) == Some{Q.Concluida{r, s, fecho}} : Maybe<&2, Q.Quadro>},
      {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), indice_entrega(antes, s, r, bs)) == Some{Q.Interrompida{prefixo}} : Maybe<&2, Q.Quadro>}>,
    {Q.consultar(H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo}), local_conclusao(s, r, bs)) == Some{Q.Concluida{r, s, fecho}} : Maybe<&2, Q.Quadro>},
    {Q.consultar(H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo}), Succ{local_conclusao(s, r, bs)}) == Some{Q.Interrompida{prefixo}} : Maybe<&2, Q.Quadro>},
    Q.dois_quadros_apos_prefixo(Con{Q.Preparada{r, bs}, H.render_publicacao(r, s)}, [Q.Fechada{}], Q.Concluida{r, s, fecho}, Q.Interrompida{prefixo}),
    conclusao => entrega => L.Ambos{
      Equal.trans(Maybe<&2, Q.Quadro>, Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs))),
        Q.consultar(H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo}), local_conclusao(s, r, bs)), Some{Q.Concluida{r, s, fecho}},
        Q.consultar_apos_prefixo(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo}), local_conclusao(s, r, bs)), conclusao),
      Equal.trans(Maybe<&2, Q.Quadro>, Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), indice_entrega(antes, s, r, bs)),
        Q.consultar(H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo}), Succ{local_conclusao(s, r, bs)}), Some{Q.Interrompida{prefixo}},
        Q.consultar_apos_prefixo(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo}), Succ{local_conclusao(s, r, bs)}), entrega)})

def parcial_unica_real(-a: I.Ambiente, -k: String, -x: I.Cenario, +antes: List<&2, Q.Quadro>,
  +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecho: Bool, +prefixo: List<&2, U32>, -t: Nat,
  canonico: {t == Q.tamanho(antes_da_entrega(antes, s, r, bs, fecho)) : Nat},
  sem_completa: {Fases.ausente(Fases.Completa{}, antes) == True{} : Bool},
  sem_interrompida: {Fases.ausente(Fases.Interrompida{}, antes) == True{} : Bool},
  completa: @u: Nat -> @outros: List<&2, U32> -> I.Acontece(a, k, x, u, I.EntregouTudo{outros}) ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), u) == Some{Q.Entregue{outros}} : Maybe<&2, Q.Quadro>},
  interrompida: @u: Nat -> @outros: List<&2, U32> -> I.Acontece(a, k, x, u, I.EntregaInterrompida{outros}) ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), u) == Some{Q.Interrompida{outros}} : Maybe<&2, Q.Quadro>}) ->
  K.EntregaInterrompidaUnica(a, k, x, t, prefixo):
  L.Ambos{+u => +outros => fato => posicao_parcial_compara(antes, s, r, bs, fecho, prefixo, u, t, outros, canonico,
      entrega_parcial_localizada(antes, s, r, bs, fecho, prefixo, u, Q.Interrompida{outros}, sem_interrompida, {==}, interrompida(u, outros, fato))),
    +u => +outros => fato => Fases.ausente_exclui_consulta(Fases.Completa{},
      Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), u, Q.Entregue{outros},
      fim_parcial_sem_completa(antes, s, r, bs, fecho, prefixo, sem_completa), {==}, completa(u, outros, fato))}

def posicao_parcial_canonica(+antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecho: Bool,
  +prefixo: List<&2, U32>, sem: {Fases.ausente(Fases.Interrompida{}, antes) == True{} : Bool}) ->
  {indice_entrega(antes, s, r, bs) == Q.tamanho(antes_da_entrega(antes, s, r, bs, fecho)) : Nat}:
  L.e_esquerda({indice_entrega(antes, s, r, bs) == Q.tamanho(antes_da_entrega(antes, s, r, bs, fecho)) : Nat}, {Q.Interrompida{prefixo} == Q.Interrompida{prefixo} : Q.Quadro},
    entrega_parcial_localizada(antes, s, r, bs, fecho, prefixo, indice_entrega(antes, s, r, bs), Q.Interrompida{prefixo}, sem, {==},
      L.e_direita(
        {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs))) == Some{Q.Concluida{r, s, fecho}} : Maybe<&2, Q.Quadro>},
        {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), indice_entrega(antes, s, r, bs)) == Some{Q.Interrompida{prefixo}} : Maybe<&2, Q.Quadro>}, pontos_parciais(antes, s, r, bs, fecho, prefixo))))

law entrega_parcial_canonica_obedece_regra7:
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for +antes: List<&2, Q.Quadro>
  for +s: D.Estado
  for +r: S.Resposta
  for +bs: List<&2, U32>
  for +fecho: Bool
  for +prefixo: List<&2, U32>
  for prefixo_real: L.Prefixo(U32, prefixo, bs)
  for falhou: I.FalhaEntregaReal(a, k, x, indice_entrega(antes, s, r, bs))
  for sem_completa: {Fases.ausente(Fases.Completa{}, antes) == True{} : Bool}
  for sem_interrompida: {Fases.ausente(Fases.Interrompida{}, antes) == True{} : Bool}
  for preparar: @u: Nat -> @rp: S.Resposta -> @bytes: List<&2, U32> ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), u) == Some{Q.Preparada{rp, bytes}} : Maybe<&2, Q.Quadro>} -> I.Acontece(a, k, x, u, I.Preparou{rp, bytes})
  for concluir: @u: Nat -> @rp: S.Resposta -> @w: D.Estado -> @fecha: Bool ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), u) == Some{Q.Concluida{rp, w, fecha}} : Maybe<&2, Q.Quadro>} -> I.Acontece(a, k, x, u, I.Concluiu{rp, w, fecha})
  for completa: @u: Nat -> @outros: List<&2, U32> -> I.Acontece(a, k, x, u, I.EntregouTudo{outros}) ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), u) == Some{Q.Entregue{outros}} : Maybe<&2, Q.Quadro>}
  for interrompida: @u: Nat -> @outros: List<&2, U32> -> I.Acontece(a, k, x, u, I.EntregaInterrompida{outros}) ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), u) == Some{Q.Interrompida{outros}} : Maybe<&2, Q.Quadro>}
  K.Regra7(I.EntregaInterrompida{prefixo}, a, k, x, indice_entrega(antes, s, r, bs))
def entrega_parcial_canonica_obedece_regra7(a, k, x, antes, s, r, bs, fecho, prefixo, prefixo_real, falhou, sem_completa, sem_interrompida, preparar, concluir, completa, interrompida):
  F.com_par(K.Regra7(I.EntregaInterrompida{prefixo}, a, k, x, indice_entrega(antes, s, r, bs)),
    {Fases.ausente(Fases.Interrompida{}, antes) == True{} : Bool}, {Fases.ausente(Fases.Interrompida{}, antes) == True{} : Bool},
    Chamada.duplicar_igualdade(Bool, Fases.ausente(Fases.Interrompida{}, antes), True{}, sem_interrompida),
    para_indice => para_outros =>
      (r, s, fecho, bs, L.Ambos{
        (Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs)), L.Ambos{
          Q.ordem_deslocada(Q.tamanho(antes), local_conclusao(s, r, bs), Succ{local_conclusao(s, r, bs)}, Exec.menor_sucessor(local_conclusao(s, r, bs))),
          concluir(Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs)), r, s, fecho,
            L.e_esquerda(
              {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs))) == Some{Q.Concluida{r, s, fecho}} : Maybe<&2, Q.Quadro>},
              {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), indice_entrega(antes, s, r, bs)) == Some{Q.Interrompida{prefixo}} : Maybe<&2, Q.Quadro>}, pontos_parciais(antes, s, r, bs, fecho, prefixo)))}),
        L.Ambos{(Nat.add(Q.tamanho(antes), 0n), L.Ambos{Q.ordem_deslocada(Q.tamanho(antes), 0n, Succ{local_conclusao(s, r, bs)}, {==}),
            preparar(Nat.add(Q.tamanho(antes), 0n), r, bs, Q.consultar_apos_prefixo(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo}), 0n))}),
          L.Ambos{prefixo_real, L.Ambos{parcial_unica_real(a, k, x, antes, s, r, bs, fecho, prefixo, indice_entrega(antes, s, r, bs),
            posicao_parcial_canonica(antes, s, r, bs, fecho, prefixo, para_indice), sem_completa, para_outros, completa, interrompida), falhou}}}}))

def transportar_parcial7(-a: I.Ambiente, -k: String, -x: I.Cenario, +antes: List<&2, Q.Quadro>,
  +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +prefixo: List<&2, U32>, -t: Nat, +outros: List<&2, U32>,
  igual: L.E<{t == indice_entrega(antes, s, r, bs) : Nat}, {outros == prefixo : List<&2, U32>}>,
  canonica: K.Regra7(I.EntregaInterrompida{prefixo}, a, k, x, indice_entrega(antes, s, r, bs))) ->
  K.Regra7(I.EntregaInterrompida{outros}, a, k, x, t):
  match igual:
    case L.Ambos{pos, bytes}:
      %Equal.sym(Nat, t, indice_entrega(antes, s, r, bs), pos) : K.Regra7(I.EntregaInterrompida{outros}, a, k, x, _)
      %Equal.sym(List<&2, U32>, outros, prefixo, bytes) : K.Regra7(I.EntregaInterrompida{_}, a, k, x, indice_entrega(antes, s, r, bs))
      canonica

# O recibo de write diz somente bytes efetivos e erro real; o restante vem da rota.
def parcela_real_localizada(-a: I.Ambiente, -k: String, -x: I.Cenario, +antes: List<&2, Q.Quadro>,
  +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +prefixo: List<&2, U32>, -t: Nat, +outros: List<&2, U32>,
  igual: L.E<{t == indice_entrega(antes, s, r, bs) : Nat}, {outros == prefixo : List<&2, U32>}>,
  falhou: I.FalhaEntregaReal(a, k, x, t),
  gerar: I.FalhaEntregaReal(a, k, x, indice_entrega(antes, s, r, bs)) -> K.Regra7(I.EntregaInterrompida{prefixo}, a, k, x, indice_entrega(antes, s, r, bs))) ->
  K.Regra7(I.EntregaInterrompida{outros}, a, k, x, t):
  match igual:
    case L.Ambos{pos, dados}:
      F.com_par(K.Regra7(I.EntregaInterrompida{outros}, a, k, x, t),
        {t == indice_entrega(antes, s, r, bs) : Nat}, {t == indice_entrega(antes, s, r, bs) : Nat},
        Chamada.duplicar_igualdade(Nat, t, indice_entrega(antes, s, r, bs), pos),
        para_tipo => para_recibo => transportar_parcial7(a, k, x, antes, s, r, bs, prefixo, t, outros, L.Ambos{para_tipo, dados},
          gerar((%para_recibo : I.FalhaEntregaReal(a, k, x, _) falhou))))

law entrega_parcial_refletida_obedece_regra7:
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for +antes: List<&2, Q.Quadro>
  for +s: D.Estado
  for +r: S.Resposta
  for +bs: List<&2, U32>
  for +fecho: Bool
  for +prefixo: List<&2, U32>
  for +t: Nat
  for +outros: List<&2, U32>
  for consulta: {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), t) == Some{Q.Interrompida{outros}} : Maybe<&2, Q.Quadro>}
  for prefixo_real: L.Prefixo(U32, prefixo, bs)
  for falhou: I.FalhaEntregaReal(a, k, x, t)
  for sem_completa: {Fases.ausente(Fases.Completa{}, antes) == True{} : Bool}
  for sem_interrompida: {Fases.ausente(Fases.Interrompida{}, antes) == True{} : Bool}
  for preparar: @u: Nat -> @rp: S.Resposta -> @bytes: List<&2, U32> ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), u) == Some{Q.Preparada{rp, bytes}} : Maybe<&2, Q.Quadro>} -> I.Acontece(a, k, x, u, I.Preparou{rp, bytes})
  for concluir: @u: Nat -> @rp: S.Resposta -> @w: D.Estado -> @fecha: Bool ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), u) == Some{Q.Concluida{rp, w, fecha}} : Maybe<&2, Q.Quadro>} -> I.Acontece(a, k, x, u, I.Concluiu{rp, w, fecha})
  for completa: @u: Nat -> @bytes: List<&2, U32> -> I.Acontece(a, k, x, u, I.EntregouTudo{bytes}) ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), u) == Some{Q.Entregue{bytes}} : Maybe<&2, Q.Quadro>}
  for interrompida: @u: Nat -> @bytes: List<&2, U32> -> I.Acontece(a, k, x, u, I.EntregaInterrompida{bytes}) ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), u) == Some{Q.Interrompida{bytes}} : Maybe<&2, Q.Quadro>}
  K.Regra7(I.EntregaInterrompida{outros}, a, k, x, t)
def entrega_parcial_refletida_obedece_regra7(a, k, x, antes, s, r, bs, fecho, prefixo, t, outros, consulta, prefixo_real, falhou,
  sem_completa, sem_interrompida, preparar, concluir, completa, interrompida):
  F.com_par(K.Regra7(I.EntregaInterrompida{outros}, a, k, x, t),
    {Fases.ausente(Fases.Interrompida{}, antes) == True{} : Bool}, {Fases.ausente(Fases.Interrompida{}, antes) == True{} : Bool},
    Chamada.duplicar_igualdade(Bool, Fases.ausente(Fases.Interrompida{}, antes), True{}, sem_interrompida),
    atual => resto => F.com_par(K.Regra7(I.EntregaInterrompida{outros}, a, k, x, t),
      {Fases.ausente(Fases.Interrompida{}, antes) == True{} : Bool}, {Fases.ausente(Fases.Interrompida{}, antes) == True{} : Bool},
      Chamada.duplicar_igualdade(Bool, Fases.ausente(Fases.Interrompida{}, antes), True{}, resto),
      pos => canonica => parcela_real_localizada(a, k, x, antes, s, r, bs, prefixo, t, outros,
        posicao_parcial_compara(antes, s, r, bs, fecho, prefixo, t, indice_entrega(antes, s, r, bs), outros,
          posicao_parcial_canonica(antes, s, r, bs, fecho, prefixo, pos),
          entrega_parcial_localizada(antes, s, r, bs, fecho, prefixo, t, Q.Interrompida{outros}, atual, {==}, consulta)), falhou,
        real => entrega_parcial_canonica_obedece_regra7(a, k, x, antes, s, r, bs, fecho, prefixo, prefixo_real, real, sem_completa, canonica, preparar, concluir, completa, interrompida))))


def por_indice(-T: Type, -P: Nat -> Type, origem: &i: Nat -> P(i), passo: @i: Nat -> P(i) -> T) -> T:
  match origem:
    case (i, h): passo(i, h)

# Resultado da primitiva de escrita: pending nao e uma conclusao da escrita.
def EntregaTerminada(entrega: H.Entrega) -> Type:
  match entrega:
    case H.Completa{proxima}: Unit
    case H.Quebrada{prefixo}: Unit
    case H.PendenteEntrega{}: Empty

def fechado_apos_entrega(+antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>,
  +entrega: H.Entrega, +marca: Q.Quadro,
  forma: {H.render_entrega(s, bs, True{}, entrega) == [marca, Q.Fechada{}] : List<&2, Q.Quadro>}) ->
  &i: Nat -> {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, True{}, entrega)), i) == Some{Q.Fechada{}} : Maybe<&2, Q.Quadro>}:
  (Succ{Q.tamanho(antes_da_entrega(antes, s, r, bs, True{}))},
    Equal.trans(Maybe<&2, Q.Quadro>,
      Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, True{}, entrega)), Succ{Q.tamanho(antes_da_entrega(antes, s, r, bs, True{}))}),
      Q.consultar(Q.concatenar(antes_da_entrega(antes, s, r, bs, True{}), [marca, Q.Fechada{}]), Succ{Q.tamanho(antes_da_entrega(antes, s, r, bs, True{}))}), Some{Q.Fechada{}},
      Equal.cong(List<&2, Q.Quadro>, Maybe<&2, Q.Quadro>, xs => Q.consultar(xs, Succ{Q.tamanho(antes_da_entrega(antes, s, r, bs, True{}))}),
        Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, True{}, entrega)),
        Q.concatenar(antes_da_entrega(antes, s, r, bs, True{}), [marca, Q.Fechada{}]),
        Equal.trans(List<&2, Q.Quadro>, Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, True{}, entrega)),
          Q.concatenar(antes_da_entrega(antes, s, r, bs, True{}), H.render_entrega(s, bs, True{}, entrega)),
          Q.concatenar(antes_da_entrega(antes, s, r, bs, True{}), [marca, Q.Fechada{}]), separar_entrega(antes, s, r, bs, True{}, entrega),
          Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, ys => Q.concatenar(antes_da_entrega(antes, s, r, bs, True{}), ys), H.render_entrega(s, bs, True{}, entrega), [marca, Q.Fechada{}], forma))),
      L.e_direita(
        {Q.consultar(Q.concatenar(antes_da_entrega(antes, s, r, bs, True{}), [marca, Q.Fechada{}]), Q.tamanho(antes_da_entrega(antes, s, r, bs, True{}))) == Some{marca} : Maybe<&2, Q.Quadro>},
        {Q.consultar(Q.concatenar(antes_da_entrega(antes, s, r, bs, True{}), [marca, Q.Fechada{}]), Succ{Q.tamanho(antes_da_entrega(antes, s, r, bs, True{}))}) == Some{Q.Fechada{}} : Maybe<&2, Q.Quadro>},
        Q.dois_quadros_apos_prefixo(antes_da_entrega(antes, s, r, bs, True{}), Nil{}, marca, Q.Fechada{}))))

def entrega_terminada_fecha(+antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>,
  entrega: H.Entrega, terminou: EntregaTerminada(entrega)) ->
  &i: Nat -> {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, True{}, entrega)), i) == Some{Q.Fechada{}} : Maybe<&2, Q.Quadro>}:
  match entrega:
    case H.Completa{+proxima}: fechado_apos_entrega(antes, s, r, bs, H.Completa{proxima}, Q.Entregue{bs}, {==})
    case H.Quebrada{+prefixo}: fechado_apos_entrega(antes, s, r, bs, H.Quebrada{prefixo}, Q.Interrompida{prefixo}, {==})
    case H.PendenteEntrega{}: match terminou:

def fechar_da_escrita(-a: I.Ambiente, -k: String, -x: I.Cenario, +antes: List<&2, Q.Quadro>,
  +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, fecho: Bool, +entrega: H.Entrega,
  disponivel: I.Processavel(a, x) -> EntregaTerminada(entrega),
  fechar: @u: Nat -> {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, entrega)), u) == Some{Q.Fechada{}} : Maybe<&2, Q.Quadro>} -> I.Acontece(a, k, x, u, I.EncerrouCanal{})) ->
  K.FechaEventualmente(fecho, a, k, x):
  match fecho:
    case False{}: Unit{}
    case True{}: pode => por_indice(I.EmAlgumMomento(a, k, x, I.EncerrouCanal{}),
      u => {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, True{}, entrega)), u) == Some{Q.Fechada{}} : Maybe<&2, Q.Quadro>},
      entrega_terminada_fecha(antes, s, r, bs, entrega, disponivel(pode)), +u => consulta => (u, fechar(u, consulta)))

# Unicidade de Concluiu, agora com a politica de fecho real em vez de False fixo.
def conclusao_localizada_no_fecho(+antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>,
  +fecho: Bool, +entrega: H.Entrega, +t: Nat, +q: Q.Quadro,
  sem: {Fases.ausente(Fases.Conclusao{}, antes) == True{} : Bool},
  alvo: {Fases.desse_tipo(Fases.Conclusao{}, q) == True{} : Bool},
  consulta: {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, entrega)), t) == Some{q} : Maybe<&2, Q.Quadro>}) ->
  L.E<{t == Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs)) : Nat}, {q == Q.Concluida{r, s, fecho} : Q.Quadro}>:
  F.com_par(L.E<{t == Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs)) : Nat}, {q == Q.Concluida{r, s, fecho} : Q.Quadro}>,
    {Fases.desse_tipo(Fases.Conclusao{}, q) == True{} : Bool}, {Fases.desse_tipo(Fases.Conclusao{}, q) == True{} : Bool},
    Chamada.duplicar_igualdade(Bool, Fases.desse_tipo(Fases.Conclusao{}, q), True{}, alvo),
    para_prefixo => para_fim => por_indice(
      L.E<{t == Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs)) : Nat}, {q == Q.Concluida{r, s, fecho} : Q.Quadro}>,
      u => L.E<{t == Nat.add(Q.tamanho(antes), u) : Nat}, {Q.consultar(H.render_conclusao(N.Conclusao{s, r, bs}, fecho, entrega), u) == Some{q} : Maybe<&2, Q.Quadro>}>,
      Fases.localizar_no_sufixo(Fases.Conclusao{}, antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, entrega), t, q, sem, para_prefixo, consulta),
      +u => parte => F.com_par(
        L.E<{t == Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs)) : Nat}, {q == Q.Concluida{r, s, fecho} : Q.Quadro}>,
        {t == Nat.add(Q.tamanho(antes), u) : Nat}, {Q.consultar(H.render_conclusao(N.Conclusao{s, r, bs}, fecho, entrega), u) == Some{q} : Maybe<&2, Q.Quadro>}, parte,
        pos => obtida => F.com_par(
          L.E<{t == Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs)) : Nat}, {q == Q.Concluida{r, s, fecho} : Q.Quadro}>,
          {u == local_conclusao(s, r, bs) : Nat}, {q == Q.Concluida{r, s, fecho} : Q.Quadro}, Fases.conclusao_no_fim_e_unica(s, r, bs, fecho, entrega, u, q, para_fim, obtida),
          indice => igual => L.Ambos{Equal.trans(Nat, t, Nat.add(Q.tamanho(antes), u), Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs)), pos,
            Equal.cong(Nat, Nat, j => Nat.add(Q.tamanho(antes), j), u, local_conclusao(s, r, bs), indice)), igual}))))

def campos_conclusao_em_fecho(+r: S.Resposta, +s: D.Estado, +fecha: Bool, +r0: S.Resposta, +s0: D.Estado, +fecho: Bool,
  igual: {Q.Concluida{r, s, fecha} == Q.Concluida{r0, s0, fecho} : Q.Quadro}) ->
  L.E<{r == r0 : S.Resposta}, {s == s0 : D.Estado}>:
  F.com_par(L.E<{r == r0 : S.Resposta}, {s == s0 : D.Estado}>,
    {Q.Concluida{r, s, fecha} == Q.Concluida{r0, s0, fecho} : Q.Quadro}, {Q.Concluida{r, s, fecha} == Q.Concluida{r0, s0, fecho} : Q.Quadro},
    Chamada.duplicar_igualdade(Q.Quadro, Q.Concluida{r, s, fecha}, Q.Concluida{r0, s0, fecho}, igual),
    resposta => estado => L.Ambos{
      F.algum_injetivo(S.Resposta, r, r0, Equal.cong(Q.Quadro, Maybe<&2, S.Resposta>, resposta_concluida, Q.Concluida{r, s, fecha}, Q.Concluida{r0, s0, fecho}, resposta)),
      F.algum_injetivo(D.Estado, s, s0, Equal.cong(Q.Quadro, Maybe<&2, D.Estado>, estado_concluido, Q.Concluida{r, s, fecha}, Q.Concluida{r0, s0, fecho}, estado))})

def conclusao_compara_no_fecho(+antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecho: Bool,
  -u: Nat, +r2: S.Resposta, +s2: D.Estado, +f2: Bool,
  local: L.E<{u == Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs)) : Nat}, {Q.Concluida{r2, s2, f2} == Q.Concluida{r, s, fecho} : Q.Quadro}>) ->
  L.E<{u == Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs)) : Nat}, L.E<{r2 == r : S.Resposta}, {s2 == s : D.Estado}>>:
  match local:
    case L.Ambos{pos, campos}: L.Ambos{pos, campos_conclusao_em_fecho(r2, s2, f2, r, s, fecho, campos)}

law conclusao_em_fecho_obedece_regra7:
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for +antes: List<&2, Q.Quadro>
  for +s: D.Estado
  for +r: S.Resposta
  for +bs: List<&2, U32>
  for +fecho: Bool
  for +entrega: H.Entrega
  for sem_concluir: {Fases.ausente(Fases.Conclusao{}, antes) == True{} : Bool}
  for permitido: K.FechamentoPermitido(a, k, x, Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs)), fecho)
  for disponivel: I.Processavel(a, x) -> EntregaTerminada(entrega)
  for preparar: @u: Nat -> @rp: S.Resposta -> @bytes: List<&2, U32> ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, entrega)), u) == Some{Q.Preparada{rp, bytes}} : Maybe<&2, Q.Quadro>} -> I.Acontece(a, k, x, u, I.Preparou{rp, bytes})
  for concluir: @u: Nat -> @rp: S.Resposta -> @w: D.Estado -> @fecha: Bool -> I.Acontece(a, k, x, u, I.Concluiu{rp, w, fecha}) ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, entrega)), u) == Some{Q.Concluida{rp, w, fecha}} : Maybe<&2, Q.Quadro>}
  for fechar: @u: Nat -> {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, entrega)), u) == Some{Q.Fechada{}} : Maybe<&2, Q.Quadro>} -> I.Acontece(a, k, x, u, I.EncerrouCanal{})
  K.Regra7(I.Concluiu{r, s, fecho}, a, k, x, Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs)))
def conclusao_em_fecho_obedece_regra7(a, k, x, antes, s, r, bs, fecho, entrega, sem_concluir, permitido, disponivel, preparar, concluir, fechar):
  L.Ambos{(bs, Nat.add(Q.tamanho(antes), 0n), L.Ambos{Q.ordem_deslocada(Q.tamanho(antes), 0n, local_conclusao(s, r, bs), {==}),
      preparar(Nat.add(Q.tamanho(antes), 0n), r, bs, Q.consultar_apos_prefixo(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, entrega), 0n))}),
    L.Ambos{L.Ambos{permitido, fechar_da_escrita(a, k, x, antes, s, r, bs, fecho, entrega, disponivel, fechar)},
      +u => +r2 => +s2 => +f2 => fato => conclusao_compara_no_fecho(antes, s, r, bs, fecho, u, r2, s2, f2,
        conclusao_localizada_no_fecho(antes, s, r, bs, fecho, entrega, u, Q.Concluida{r2, s2, f2}, sem_concluir, {==}, concluir(u, r2, s2, f2, fato)))}}

def transportar_conclusao7_no_fecho(-a: I.Ambiente, -k: String, -x: I.Cenario, +antes: List<&2, Q.Quadro>,
  +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecho: Bool, -t: Nat, +q: Q.Quadro,
  local: L.E<{t == Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs)) : Nat}, {q == Q.Concluida{r, s, fecho} : Q.Quadro}>,
  canonica: K.Regra7(I.Concluiu{r, s, fecho}, a, k, x, Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs)))) ->
  K.Regra7(fato_da_conclusao(q), a, k, x, t):
  match local:
    case L.Ambos{pos, quadro}:
      %Equal.sym(Nat, t, Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs)), pos) : K.Regra7(fato_da_conclusao(q), a, k, x, _)
      %Equal.sym(Q.Quadro, q, Q.Concluida{r, s, fecho}, quadro) : K.Regra7(fato_da_conclusao(_), a, k, x, Nat.add(Q.tamanho(antes), local_conclusao(s, r, bs)))
      canonica


# Politica do header: um erro recuperavel de pacote so vem depois de receber corpo.
def EnquadramentoAlcancado(pre: H.Preprocessamento, -disposicao: X.Disposicao) -> Type:
  match pre:
    case H.FalhaEnquadramento{id, fatal}:
      match fatal:
        case False{}: &br: List<&2, U32> -> {disposicao == X.ProcessarCorpo{br} : X.Disposicao}
        case True{}: Unit
    case _: Unit

def entrada_fecha(caso: H.Caso) -> Bool:
  match caso:
    case H.EntradaRecusa{e, fecha, entrega}: fecha
    case _: False{}

def eh_entrada(caso: H.Caso) -> Bool:
  match caso:
    case H.EntradaRecusa{erro, fecha, en}: True{}
    case _: False{}

def limpeza_nao_e_entrada(r: P.Requisicao, ctx: D.Contexto, xs: List<&2, Q.QuadroExec>, p: N.Preparada,
  li: H.Limpeza, en: H.Entrega) -> {eh_entrada(H.decidir_limpeza(r, ctx, xs, p, li, en)) == False{} : Bool}:
  match li:
    case H.Limpa{}: {==}
    case H.ErroLimpeza{id, fatal}: {==}
    case H.FatalAposStore{etapa, id}: {==}
    case H.PendenteLimpeza{}: {==}

def execucao_nao_e_entrada(r: P.Requisicao, ctx: D.Contexto, ex: H.SaidaExecucao, li: H.Limpeza, en: H.Entrega) ->
  {eh_entrada(H.decidir_execucao(r, ctx, ex, li, en)) == False{} : Bool}:
  match ex:
    case H.Finalizou{xs, p}: limpeza_nao_e_entrada(r, ctx, xs, p, li, en)
    case H.ErroExecucao{ponto, etapa, id, fatal}: {==}
    case H.PendenteExecucao{ponto}: {==}

def juizo_nao_e_entrada(r: P.Requisicao, ctx: D.Contexto, dados: H.DadosFerramentas) ->
  {eh_entrada(H.decidir_juizo(r, ctx, dados)) == False{} : Bool}:
  match dados:
    case H.DadosFerramentas{j, ex, li, en, pre}:
      match j:
        case H.Aceitou{}: execucao_nao_e_entrada(r, ctx, ex, li, en)
        case H.Recusou{}: {==}
        case H.ErroJuizo{id, fatal}: {==}
        case H.PendenteJuizo{}: {==}

def identidade_nao_e_entrada(ctx: Maybe<&2, D.Contexto>, r: P.Requisicao, dados: H.DadosFerramentas) ->
  {eh_entrada(H.decidir_identidade(ctx, r, dados)) == False{} : Bool}:
  match ctx:
    case None{}:
      match dados:
        case H.DadosFerramentas{j, ex, li, en, pre}: {==}
    case Some{c}: juizo_nao_e_entrada(r, c, dados)

def autenticacao_nao_e_entrada(pre: H.Preprocessamento, s: D.Estado, +r: P.Requisicao, dados: H.DadosFerramentas) ->
  {eh_entrada(H.decidir_autenticacao(pre, s, r, dados)) == False{} : Bool}:
  match pre:
    case H.FalhaAuth{id, fatal}: {==}
    case H.PendenteAuth{}: {==}
    case H.Normal{}: identidade_nao_e_entrada(D.autenticar(s, I.credencial(r)), r, dados)
    case H.FalhaDecode{id, fatal}: identidade_nao_e_entrada(D.autenticar(s, I.credencial(r)), r, dados)
    case H.FalhaEnquadramento{id, fatal}: identidade_nao_e_entrada(D.autenticar(s, I.credencial(r)), r, dados)
    case H.PendenteDecode{}: identidade_nao_e_entrada(D.autenticar(s, I.credencial(r)), r, dados)
    case H.PendenteEnquadramento{}: identidade_nao_e_entrada(D.autenticar(s, I.credencial(r)), r, dados)

def sem_entrada_nao_fecha(caso: H.Caso, nao: {eh_entrada(caso) == False{} : Bool}) -> {entrada_fecha(caso) == False{} : Bool}:
  match caso:
    case H.EntradaRecusa{e, +fecha, en}: F.absurdo_booleano({fecha == False{} : Bool}, Equal.sym(Bool, True{}, False{}, nao))
    case H.AutRecusa{r, en}: {==}
    case H.GateRecusa{r, ctx, en}: {==}
    case H.Executada{r, ctx, qs, p, en}: {==}
    case H.FalhaAntes{fase, etapa, id, fatal, en}: {==}
    case H.InicialOk{}: {==}
    case H.InicialRecusa{status}: {==}
    case H.InicialFalha{aceita, etapa, id, fatal}: {==}
    case H.SemResposta{}: {==}
    case H.FatalAposPublicacao{r, ctx, qs, p, etapa, id}: {==}
    case H.Pendente{fase}: {==}
    case H.InicialPendente{aceita}: {==}

def pre_nao_fecha(pre: Entrada.PreAutenticacao, +dados: H.DadosFerramentas) ->
  {entrada_fecha(H.decidir_pre(pre, dados)) == False{} : Bool}:
  match pre:
    case Entrada.Pronta{+s, +r}: sem_entrada_nao_fecha(H.decidir_autenticacao(H.preprocessamento(dados), s, r, dados), autenticacao_nao_e_entrada(H.preprocessamento(dados), s, r, dados))
    case Entrada.ErroMensagem{status}:
      match dados:
        case H.DadosFerramentas{j, ex, li, en, pre}: {==}
    case Entrada.ErroTransporte{}:
      match dados:
        case H.DadosFerramentas{j, ex, li, en, pre}: {==}

def decode_nao_fecha(pre: H.Preprocessamento, bs: List<&2, U32>, e: D.Esquema, lim: S.Limites, dados: H.DadosFerramentas) ->
  {entrada_fecha(H.decidir_decode(pre, bs, e, lim, dados)) == False{} : Bool}:
  match pre:
    case H.FalhaDecode{id, fatal}: {==}
    case H.PendenteDecode{}: {==}
    case H.Normal{}: pre_nao_fecha(Entrada.decodificar(bs, e, lim), dados)
    case H.FalhaAuth{id, fatal}: pre_nao_fecha(Entrada.decodificar(bs, e, lim), dados)
    case H.FalhaEnquadramento{id, fatal}: pre_nao_fecha(Entrada.decodificar(bs, e, lim), dados)
    case H.PendenteAuth{}: pre_nao_fecha(Entrada.decodificar(bs, e, lim), dados)
    case H.PendenteEnquadramento{}: pre_nao_fecha(Entrada.decodificar(bs, e, lim), dados)

def pacote_nao_fecha(pacote: Maybe<&2, List<&2, U32>>, e: D.Esquema, lim: S.Limites, +dados: H.DadosFerramentas) ->
  {entrada_fecha(H.decidir_pacote(pacote, e, lim, dados)) == False{} : Bool}:
  match pacote:
    case None{}:
      match dados:
        case H.DadosFerramentas{j, ex, li, en, pre}: {==}
    case Some{bs}: decode_nao_fecha(H.preprocessamento(dados), bs, e, lim, dados)

# Este tipo fala so do bit de enquadramento calculado, nao da Lei7.
def PoliticaFecho(disposicao: X.Disposicao, caso: H.Caso) -> Type:
  match caso:
    case H.EntradaRecusa{e, fecha, en}: I.FechamentoDisposicao(disposicao, fecha)
    case H.AutRecusa{r, en}: I.FechamentoDisposicao(disposicao, False{})
    case H.GateRecusa{r, ctx, en}: I.FechamentoDisposicao(disposicao, False{})
    case H.Executada{r, ctx, qs, p, en}: I.FechamentoDisposicao(disposicao, False{})
    case H.FalhaAntes{fase, etapa, id, fatal, en}:
      match fatal:
        case False{}: I.FechamentoDisposicao(disposicao, False{})
        case True{}: Unit
    case _: Unit

def corpo_tem_politica(+br: List<&2, U32>, caso: H.Caso,
  nao_fecha: {entrada_fecha(caso) == False{} : Bool}) -> PoliticaFecho(X.ProcessarCorpo{br}, caso):
  match caso:
    case H.EntradaRecusa{e, fecha, en}: nao_fecha
    case H.AutRecusa{r, en}: {==}
    case H.GateRecusa{r, ctx, en}: {==}
    case H.Executada{r, ctx, qs, p, en}: {==}
    case H.FalhaAntes{fase, etapa, id, fatal, en}:
      match fatal:
        case False{}: {==}
        case True{}: Unit{}
    case H.InicialOk{}: Unit{}
    case H.InicialRecusa{status}: Unit{}
    case H.InicialFalha{aceita, etapa, id, fatal}: Unit{}
    case H.SemResposta{}: Unit{}
    case H.FatalAposPublicacao{r, ctx, qs, p, etapa, id}: Unit{}
    case H.Pendente{fase}: Unit{}
    case H.InicialPendente{aceita}: Unit{}

def disposicao_tem_politica(+d: X.Disposicao, +be: List<&2, U32>, +e: D.Esquema, +lim: S.Limites,
  +dados: H.DadosFerramentas) -> PoliticaFecho(d, H.decidir_disposicao(d, be, e, lim, dados)):
  match d:
    case X.EncerrarSemResposta{}: Unit{}
    case X.RecusarEncerrar{s}:
      match dados:
        case H.DadosFerramentas{j, ex, li, en, pre}: {==}
    case X.RecusarContinuar{s}:
      match dados:
        case H.DadosFerramentas{j, ex, li, en, pre}: {==}
    case X.ProcessarCorpo{+br}: corpo_tem_politica(br, H.decidir_pacote(Transporte.juntar(be, br), e, lim, dados), pacote_nao_fecha(Transporte.juntar(be, br), e, lim, dados))

def enquadramento_tem_politica(pre: H.Preprocessamento, +d: X.Disposicao, +be: List<&2, U32>, +e: D.Esquema, +lim: S.Limites, +dados: H.DadosFerramentas,
  alcancado: EnquadramentoAlcancado(pre, d)) -> PoliticaFecho(d, H.decidir_enquadramento(pre, d, be, e, lim, dados)):
  match pre:
    case H.FalhaEnquadramento{id, fatal}:
      match fatal:
        case True{}: Unit{}
        case False{}:
          match alcancado:
            case (br, igual):
              %Equal.sym(X.Disposicao, d, X.ProcessarCorpo{br}, igual) : I.FechamentoDisposicao(_, False{})
              {==}
    case H.PendenteEnquadramento{}: Unit{}
    case H.Normal{}: disposicao_tem_politica(d, be, e, lim, dados)
    case H.FalhaDecode{id, fatal}: disposicao_tem_politica(d, be, e, lim, dados)
    case H.FalhaAuth{id, fatal}: disposicao_tem_politica(d, be, e, lim, dados)
    case H.PendenteDecode{}: disposicao_tem_politica(d, be, e, lim, dados)
    case H.PendenteAuth{}: disposicao_tem_politica(d, be, e, lim, dados)

law decisao_tem_politica_de_fecho:
  for ~c: S.Configuracao
  for +rx: X.Recepcao
  for +be: List<&2, U32>
  for +dados: H.DadosFerramentas
  for alcancado: EnquadramentoAlcancado(H.preprocessamento(dados), X.decidir_recepcao(c, rx))
  PoliticaFecho(X.decidir_recepcao(c, rx), H.decidir(c, rx, be, dados))
def decisao_tem_politica_de_fecho(c, rx, be, dados, alcancado):
  %Equal.sym(H.Caso, H.decidir(c, rx, be, dados), H.decidir_enquadramento(H.preprocessamento(dados), X.decidir_recepcao(c, rx), be, S.esquema(c), S.limites(c), dados),
    Dois.decidir_por_recepcao(c, rx, be, dados)) : PoliticaFecho(X.decidir_recepcao(c, rx), _)
  enquadramento_tem_politica(H.preprocessamento(dados), X.decidir_recepcao(c, rx), be, S.esquema(c), S.limites(c), dados, alcancado)

def PoliticaDeFecho(d: X.Disposicao, q: Maybe<&2, Fechos.Fecho>) -> Type:
  match q:
    case None{}: Unit
    case Some{Fechos.Fecho{antes, c, fecha, entrega, origem}}: I.FechamentoDisposicao(d, fecha)

# Disponibilidade de write/flush sobre o resultado tecnico selecionado.
# Nenhum fato de conclusao, publicacao ou encerramento e recebido aqui.
def EscritasDisponiveis(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao,
  q: Maybe<&2, Fechos.Fecho>) -> Type:
  match q:
    case None{}: Unit
    case Some{Fechos.Fecho{antes, concluida, fecha, entrega, origem}}:
      I.Processavel(Fonte.ambiente(fonte), I.Atender{mundo, c, s, rx}) -> EntregaTerminada(entrega)

def politica_do_erro(q: Maybe<&2, List<&2, U32>>, +d: X.Disposicao, antes: List<&2, Q.Quadro>, s: D.Estado,
  e: Erros.Erro, +fecha: Bool, entrega: H.Entrega, origem: H.Caso, politica: I.FechamentoDisposicao(d, fecha)) ->
  PoliticaDeFecho(d, Fechos.erro(q, antes, s, e, fecha, entrega, origem)):
  match q:
    case None{}: Unit{}
    case Some{bs}: politica

def politica_do_erro_fixo(+d: X.Disposicao, antes: List<&2, Q.Quadro>, s: D.Estado,
  +e: Erros.Erro, +fecha: Bool, entrega: H.Entrega, origem: H.Caso, politica: I.FechamentoDisposicao(d, fecha)) ->
  PoliticaDeFecho(d, Fechos.fechar_erro(antes, s, e, fecha, entrega, origem)):
  politica_do_erro(P.enquadrar(S.resposta_valor(S.resposta_erro(Erros.status(e)))), d, antes, s, e, fecha, entrega, origem, politica)

def politica_do_caso(+d: X.Disposicao, +m: H.Micro, +s: D.Estado, caso: H.Caso,
  politica: PoliticaFecho(d, caso)) -> PoliticaDeFecho(d, Fechos.do_caso(m, s, caso)):
  match caso:
    case H.EntradaRecusa{+e, +fecha, +en}: politica_do_erro_fixo(d, H.micro_entrada(m), s, Fechos.erro_da_entrada(e), fecha, en, H.EntradaRecusa{e, fecha, en}, politica)
    case H.AutRecusa{+r, +en}: politica_do_erro_fixo(d, Fechos.antes_autenticacao(m, r), s, Erros.Autenticacao{}, False{}, en, H.AutRecusa{r, en}, politica)
    case H.GateRecusa{+r, +ctx, +en}: politica_do_erro_fixo(d, Fechos.antes_gate(m, r, ctx), s, Erros.Certificado{}, False{}, en, H.GateRecusa{r, ctx, en}, politica)
    case H.Executada{r, ctx, qs, p, en}: politica
    case H.FalhaAntes{+fase, +etapa, +id, fatal, +en}:
      match fatal:
        case True{}: Unit{}
        case False{}: politica_do_erro_fixo(d, Fechos.antes_falha(m, fase, etapa, id, False{}), s, Erros.Falha{}, False{}, en, H.FalhaAntes{fase, etapa, id, False{}, en}, politica)
    case H.InicialOk{}: Unit{}
    case H.InicialRecusa{status}: Unit{}
    case H.InicialFalha{aceita, etapa, id, fatal}: Unit{}
    case H.SemResposta{}: Unit{}
    case H.FatalAposPublicacao{r, ctx, qs, p, etapa, id}: Unit{}
    case H.Pendente{fase}: Unit{}
    case H.InicialPendente{aceita}: Unit{}

def configurar_politica(+d: X.Disposicao, q: Maybe<&2, Fechos.Fecho>, politica: PoliticaDeFecho(d, q)) ->
  PoliticaDeFecho(d, Fechos.configurar(q)):
  match q:
    case None{}: Unit{}
    case Some{Fechos.Fecho{antes, c, fecha, entrega, origem}}: politica

def politica_da_rota(+d: X.Disposicao, +m: H.Micro, +s: D.Estado, +caso: H.Caso, politica: PoliticaFecho(d, caso)) ->
  PoliticaDeFecho(d, Fechos.fecho_do_caso(m, s, caso)):
  configurar_politica(d, Fechos.do_caso(m, s, caso), politica_do_caso(d, m, s, caso, politica))


def AlcancouPacote(~c: S.Configuracao, +rx: X.Recepcao, dados: Fonte.ChamadaData) -> Type:
  match dados:
    case Fonte.ChamadaData{cf, pf, cert, termina, be, ferramentas, micro}:
      EnquadramentoAlcancado(H.preprocessamento(ferramentas), X.decidir_recepcao(c, rx))

def politica_dos_dados(~c: S.Configuracao, +rx: X.Recepcao, dados: Fonte.ChamadaData,
  alcancado: AlcancouPacote(c, rx, dados)) -> PoliticaFecho(X.decidir_recepcao(c, rx), Lig.caso_dos_dados(c, rx, dados)):
  match dados:
    case Fonte.ChamadaData{cf, pf, cert, termina, be, ferramentas, micro}:
      decisao_tem_politica_de_fecho(c, rx, be, ferramentas, alcancado)

def conclusao_fonte_no_fecho(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +inicial: D.Estado,
  +rx: X.Recepcao, +antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecho: Bool, +entrega: H.Entrega,
  +t: Nat, +r2: S.Resposta, +s2: D.Estado, +f2: Bool,
  canonico: {I.Atender{mundo, c, inicial, rx} == Fonte.cenario(fonte, mundo) : I.Cenario},
  +mesma: {Vis.quadros_chamada(c, inicial, rx, Fonte.chamada(fonte, mundo)) == Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, entrega)) : List<&2, Q.Quadro>},
  +sem_concluir: {Fases.ausente(Fases.Conclusao{}, antes) == True{} : Bool},
  politica: I.FechamentoDisposicao(X.decidir_recepcao(c, rx), fecho),
  disponivel: I.Processavel(Fonte.ambiente(fonte), I.Atender{mundo, c, inicial, rx}) -> EntregaTerminada(entrega),
  consulta: {Q.consultar(Vis.quadros_chamada(c, inicial, rx, Fonte.chamada(fonte, mundo)), t) == Some{Q.Concluida{r2, s2, f2}} : Maybe<&2, Q.Quadro>}) ->
  K.Regra7(I.Concluiu{r2, s2, f2}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, t):
  F.com_par(K.Regra7(I.Concluiu{r2, s2, f2}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, t),
    {I.Atender{mundo, c, inicial, rx} == Fonte.cenario(fonte, mundo) : I.Cenario},
    {I.Atender{mundo, c, inicial, rx} == Fonte.cenario(fonte, mundo) : I.Cenario},
    Chamada.duplicar_igualdade(I.Cenario, I.Atender{mundo, c, inicial, rx}, Fonte.cenario(fonte, mundo), canonico),
    para_preparo => para_fecho => transportar_conclusao7_no_fecho(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, antes, s, r, bs, fecho, t, Q.Concluida{r2, s2, f2},
      conclusao_localizada_no_fecho(antes, s, r, bs, fecho, entrega, t, Q.Concluida{r2, s2, f2}, sem_concluir, {==},
        (%mesma : {Q.consultar(_, t) == Some{Q.Concluida{r2, s2, f2}} : Maybe<&2, Q.Quadro>} consulta)),
      conclusao_em_fecho_obedece_regra7(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, antes, s, r, bs, fecho, entrega,
        sem_concluir, L.Esquerda{politica}, disponivel,
        +u => +rp => +bytes => obtida => Lig.introduzir_na_lista(fonte, c, mundo, inicial, rx,
          Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, entrega)), u, Q.Preparada{rp, bytes}, I.Preparou{rp, bytes}, para_preparo, mesma, obtida, {==}, Unit{}),
        +u => +rp => +w => +fecha => fato => Lig.extrair_na_lista(fonte, c, mundo, inicial, rx,
          Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, entrega)), u, I.Concluiu{rp, w, fecha}, mesma, Unit{}, fato),
        +u => obtida => Lig.introduzir_na_lista(fonte, c, mundo, inicial, rx,
          Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, entrega)), u, Q.Fechada{}, I.EncerrouCanal{}, para_fecho, mesma, obtida, {==}, Unit{}))))

def consumir_conclusao_selecionada(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +inicial: D.Estado,
  +rx: X.Recepcao, +caso: H.Caso, q: Maybe<&2, Fechos.Fecho>, +t: Nat, +r: S.Resposta, +s: D.Estado, +fecha: Bool,
  canonico: {I.Atender{mundo, c, inicial, rx} == Fonte.cenario(fonte, mundo) : I.Cenario},
  forma: Fechos.Forma(Vis.quadros_chamada(c, inicial, rx, Fonte.chamada(fonte, mundo)), caso, q),
  politica: PoliticaDeFecho(X.decidir_recepcao(c, rx), q), disponivel: EscritasDisponiveis(fonte, c, mundo, inicial, rx, q),
  consulta: {Q.consultar(Vis.quadros_chamada(c, inicial, rx, Fonte.chamada(fonte, mundo)), t) == Some{Q.Concluida{r, s, fecha}} : Maybe<&2, Q.Quadro>}) ->
  K.Regra7(I.Concluiu{r, s, fecha}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, t):
  match q:
    case None{}: L.ex_falso(K.Regra7(I.Concluiu{r, s, fecha}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, t),
      Fases.ausente_exclui_consulta(Fases.Conclusao{}, Vis.quadros_chamada(c, inicial, rx, Fonte.chamada(fonte, mundo)), t, Q.Concluida{r, s, fecha}, forma, {==}, consulta))
    case Some{Fechos.Fecho{antes, N.Conclusao{w, rp, bs}, fecho, entrega, origem}}:
      match forma:
        case L.Ambos{mesmo_caso, L.Ambos{traco, L.Ambos{pub, concl}}}:
          conclusao_fonte_no_fecho(fonte, c, mundo, inicial, rx, antes, w, rp, bs, fecho, entrega, t, r, s, fecha,
            canonico, traco, concl, politica, disponivel, consulta)

def conclusao_da_chamada_obedece_regra7(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +inicial: D.Estado,
  +rx: X.Recepcao, +t: Nat, +r: S.Resposta, +s: D.Estado, +fecha: Bool,
  alcancado: AlcancouPacote(c, rx, Fonte.chamada(fonte, mundo)),
  disponivel: EscritasDisponiveis(fonte, c, mundo, inicial, rx,
    Fechos.fecho_do_caso(Lig.micro_dos_dados(Fonte.chamada(fonte, mundo)), inicial, Lig.caso_dos_dados(c, rx, Fonte.chamada(fonte, mundo)))),
  observado: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, t, I.Concluiu{r, s, fecha})) ->
  K.Regra7(I.Concluiu{r, s, fecha}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, t):
  F.com_par(K.Regra7(I.Concluiu{r, s, fecha}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, t),
    {Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
    L.E<{I.Atender{mundo, c, inicial, rx} == Fonte.cenario(fonte, mundo) : I.Cenario}, Fonte.da_rota(fonte, I.Atender{mundo, c, inicial, rx}, t, I.Concluiu{r, s, fecha})>,
    Fonte.eliminar_fato_literal(fonte, Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, t, I.Concluiu{r, s, fecha}, observado),
    nome => origem => F.com_par(K.Regra7(I.Concluiu{r, s, fecha}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, t),
      {I.Atender{mundo, c, inicial, rx} == Fonte.cenario(fonte, mundo) : I.Cenario}, Fonte.da_rota(fonte, I.Atender{mundo, c, inicial, rx}, t, I.Concluiu{r, s, fecha}), origem,
      canonico => obs => consumir_conclusao_selecionada(fonte, c, mundo, inicial, rx, Lig.caso_dos_dados(c, rx, Fonte.chamada(fonte, mundo)),
        Fechos.fecho_do_caso(Lig.micro_dos_dados(Fonte.chamada(fonte, mundo)), inicial, Lig.caso_dos_dados(c, rx, Fonte.chamada(fonte, mundo))), t, r, s, fecha, canonico,
        (%Equal.sym(List<&2, Q.Quadro>, Vis.quadros_chamada(c, inicial, rx, Fonte.chamada(fonte, mundo)),
          H.render(Lig.micro_dos_dados(Fonte.chamada(fonte, mundo)), inicial, Lig.caso_dos_dados(c, rx, Fonte.chamada(fonte, mundo))),
          Lig.quadros_seguem_o_caso(c, inicial, rx, Fonte.chamada(fonte, mundo))) : Fechos.Forma(_, Lig.caso_dos_dados(c, rx, Fonte.chamada(fonte, mundo)),
            Fechos.fecho_do_caso(Lig.micro_dos_dados(Fonte.chamada(fonte, mundo)), inicial, Lig.caso_dos_dados(c, rx, Fonte.chamada(fonte, mundo))))
          Fechos.forma_da_rota(Lig.micro_dos_dados(Fonte.chamada(fonte, mundo)), inicial, Lig.caso_dos_dados(c, rx, Fonte.chamada(fonte, mundo)))),
        politica_da_rota(X.decidir_recepcao(c, rx), Lig.micro_dos_dados(Fonte.chamada(fonte, mundo)), inicial, Lig.caso_dos_dados(c, rx, Fonte.chamada(fonte, mundo)),
          politica_dos_dados(c, rx, Fonte.chamada(fonte, mundo), alcancado)), disponivel,
        Lig.quadro_da_observacao(fonte, c, inicial, rx, Fonte.chamada(fonte, mundo), t, I.Concluiu{r, s, fecha}, Unit{}, obs))))


# Dados do erro fixo calculado pelo mesmo encoder; a causa e provada a parte.
def dados_do_erro_preparado(~c: S.Configuracao, +status: S.Status, +bs: List<&2, U32>,
  configuracao: {R.configuracao_valida(c) == True{} : Bool}, erro: Preparacao.Erro(status),
  mensagem: P.Mensagem(S.resposta_valor(S.resposta_erro(status)), bs)) ->
  L.E<I.ErroFixo(S.resposta_erro(status)), L.E<P.Mensagem(S.resposta_valor(S.resposta_erro(status)), bs),
    {R.cabe(R.limite_resposta(S.limites(c)), S.resposta_valor(S.resposta_erro(status))) == True{} : Bool}>>:
  F.com_par(
    L.E<I.ErroFixo(S.resposta_erro(status)), L.E<P.Mensagem(S.resposta_valor(S.resposta_erro(status)), bs),
      {R.cabe(R.limite_resposta(S.limites(c)), S.resposta_valor(S.resposta_erro(status))) == True{} : Bool}>>,
    I.ErroFixo(S.resposta_erro(status)), {R.cabe(R.limite_resposta(S.limites(c)), S.resposta_valor(S.resposta_erro(status))) == True{} : Bool},
    Preparacao.erro_preparavel(status, S.limites(c), Preparacao.limites_da_configuracao(c, configuracao), erro),
    payload => tamanho => L.Ambos{payload, L.Ambos{mensagem, tamanho}})

law preparo_fixo_com_causa_real_obedece_regra7:
  for ~c: S.Configuracao
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for -t: Nat
  for +status: S.Status
  for +bs: List<&2, U32>
  for configuracao: {I.configuracao(x) == c : S.Configuracao}
  for valida: {R.configuracao_valida(c) == True{} : Bool}
  for erro: Preparacao.Erro(status)
  for mensagem: P.Mensagem(S.resposta_valor(S.resposta_erro(status)), bs)
  for causa: I.RespostaJustificada(S.resposta_erro(status), a, k, x, t)
  K.Regra7(I.Preparou{S.resposta_erro(status), bs}, a, k, x, t)
def preparo_fixo_com_causa_real_obedece_regra7(c, a, k, x, t, status, bs, configuracao, valida, erro, mensagem, causa):
  F.com_par(K.Regra7(I.Preparou{S.resposta_erro(status), bs}, a, k, x, t),
    I.ErroFixo(S.resposta_erro(status)), L.E<P.Mensagem(S.resposta_valor(S.resposta_erro(status)), bs),
      {R.cabe(R.limite_resposta(S.limites(I.configuracao(x))), S.resposta_valor(S.resposta_erro(status))) == True{} : Bool}>,
    (%Equal.sym(S.Configuracao, I.configuracao(x), c, configuracao) :
      L.E<I.ErroFixo(S.resposta_erro(status)), L.E<P.Mensagem(S.resposta_valor(S.resposta_erro(status)), bs),
        {R.cabe(R.limite_resposta(S.limites(_)), S.resposta_valor(S.resposta_erro(status))) == True{} : Bool}>>
      dados_do_erro_preparado(c, status, bs, valida, erro, mensagem)),
    payload => resto => F.com_par(K.Regra7(I.Preparou{S.resposta_erro(status), bs}, a, k, x, t),
      P.Mensagem(S.resposta_valor(S.resposta_erro(status)), bs),
      {R.cabe(R.limite_resposta(S.limites(I.configuracao(x))), S.resposta_valor(S.resposta_erro(status))) == True{} : Bool}, resto,
      codificado => tamanho => L.Ambos{payload, L.Ambos{codificado, L.Ambos{tamanho, causa}}}))


# A equacao de preparar determina TODOS os campos, nao so o status.
law normalizar_preparada_real:
  for ~c: S.Configuracao
  for +w: D.Estado
  for +ts: List<&2, S.Evento>
  for +proposta: S.Resposta
  for +p: N.Preparada
  for obtida: {N.preparar(N.Parada{w, ts, proposta}, c) == Some{p} : Maybe<&2, N.Preparada>}
  L.E<{p == N.Preparada{w, ts, R.finalizar(proposta, c, w), Preparacao.bytes_preparados(p)} : N.Preparada},
    P.Mensagem(S.resposta_valor(R.finalizar(proposta, c, w)), Preparacao.bytes_preparados(p))>
def normalizar_preparada_real(c, w, ts, proposta, p, obtida):
  match p:
    case N.Preparada{pw, pts, pr, bs}:
      Preparacao.preparar_preserva_resposta_estado_eventos_e_bytes(N.Parada{w, ts, proposta}, c, N.Preparada{pw, pts, pr, bs}, obtida)


# O recibo do write refere-se aos bytes integrais daquela proposta real.
def PrefixoDaEscrita(c: N.Conclusao, en: H.Entrega) -> Type:
  match c:
    case N.Conclusao{s, r, bs}:
      match en:
        case H.Quebrada{prefixo}: L.Prefixo(U32, prefixo, bs)
        case _: Unit

def PrefixosDoFecho(q: Maybe<&2, Fechos.Fecho>) -> Type:
  match q:
    case None{}: Unit
    case Some{Fechos.Fecho{antes, c, fecha, en, origem}}: PrefixoDaEscrita(c, en)

type FatoEntrega is Data:
  CompletaObservada{bytes: List<&2, U32>}
  ParcialObservada{bytes: List<&2, U32>}

def fato_entrega(e: FatoEntrega) -> I.Fato:
  match e:
    case CompletaObservada{bs}: I.EntregouTudo{bs}
    case ParcialObservada{bs}: I.EntregaInterrompida{bs}

def quadro_entrega(e: FatoEntrega) -> Q.Quadro:
  match e:
    case CompletaObservada{bs}: Q.Entregue{bs}
    case ParcialObservada{bs}: Q.Interrompida{bs}

def entrega_sem_fecho_impossivel(-a: I.Ambiente, -k: String, -x: I.Cenario, +xs: List<&2, Q.Quadro>, +t: Nat, e: FatoEntrega,
  sem: L.E<{Fases.ausente(Fases.Completa{}, xs) == True{} : Bool}, {Fases.ausente(Fases.Interrompida{}, xs) == True{} : Bool}>,
  consulta: {Q.consultar(xs, t) == Some{quadro_entrega(e)} : Maybe<&2, Q.Quadro>}) -> K.Regra7(fato_entrega(e), a, k, x, t):
  match e:
    case CompletaObservada{+bs}: L.ex_falso(K.Regra7(I.EntregouTudo{bs}, a, k, x, t),
      Fases.ausente_exclui_consulta(Fases.Completa{}, xs, t, Q.Entregue{bs}, L.e_esquerda(
        {Fases.ausente(Fases.Completa{}, xs) == True{} : Bool}, {Fases.ausente(Fases.Interrompida{}, xs) == True{} : Bool}, sem), {==}, consulta))
    case ParcialObservada{+bs}: L.ex_falso(K.Regra7(I.EntregaInterrompida{bs}, a, k, x, t),
      Fases.ausente_exclui_consulta(Fases.Interrompida{}, xs, t, Q.Interrompida{bs}, L.e_direita(
        {Fases.ausente(Fases.Completa{}, xs) == True{} : Bool}, {Fases.ausente(Fases.Interrompida{}, xs) == True{} : Bool}, sem), {==}, consulta))

# A mesma inversao de sufixo decide completa, parcial ou ausencia de entrega.
def entrega_no_sufixo_obedece_regra7(-a: I.Ambiente, -k: String, -x: I.Cenario,
  +antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecho: Bool, +en: H.Entrega, +t: Nat, e: FatoEntrega,
  sem_completa: {Fases.ausente(Fases.Completa{}, antes) == True{} : Bool},
  sem_parcial: {Fases.ausente(Fases.Interrompida{}, antes) == True{} : Bool},
  prefixo_real: PrefixoDaEscrita(N.Conclusao{s, r, bs}, en),
  consulta: {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, en)), t) == Some{quadro_entrega(e)} : Maybe<&2, Q.Quadro>},
  preparar: @u: Nat -> @rp: S.Resposta -> @bytes: List<&2, U32> ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, en)), u) == Some{Q.Preparada{rp, bytes}} : Maybe<&2, Q.Quadro>} -> I.Acontece(a, k, x, u, I.Preparou{rp, bytes}),
  concluir: @u: Nat -> @rp: S.Resposta -> @w: D.Estado -> @fecha: Bool ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, en)), u) == Some{Q.Concluida{rp, w, fecha}} : Maybe<&2, Q.Quadro>} -> I.Acontece(a, k, x, u, I.Concluiu{rp, w, fecha}),
  completa: @u: Nat -> @bytes: List<&2, U32> -> I.Acontece(a, k, x, u, I.EntregouTudo{bytes}) ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, en)), u) == Some{Q.Entregue{bytes}} : Maybe<&2, Q.Quadro>},
  parcial: @u: Nat -> @bytes: List<&2, U32> -> I.Acontece(a, k, x, u, I.EntregaInterrompida{bytes}) ->
    {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, en)), u) == Some{Q.Interrompida{bytes}} : Maybe<&2, Q.Quadro>},
  falha: @u: Nat -> @prefixo: List<&2, U32> -> {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, en)), u) == Some{Q.Interrompida{prefixo}} : Maybe<&2, Q.Quadro>} -> I.FalhaEntregaReal(a, k, x, u)) ->
  K.Regra7(fato_entrega(e), a, k, x, t):
  match en:
    case H.Completa{+proxima}:
      match e:
        case CompletaObservada{outros}:
          entrega_completa_refletida_obedece_regra7(a, k, x, antes, s, r, bs, fecho, proxima, t, outros, consulta,
            sem_completa, sem_parcial, preparar, concluir, completa, parcial)
        case ParcialObservada{+prefixo}: L.ex_falso(K.Regra7(I.EntregaInterrompida{prefixo}, a, k, x, t),
          Fases.ausente_exclui_consulta(Fases.Interrompida{}, Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Completa{proxima})), t, Q.Interrompida{prefixo},
            fim_completo_sem_interrupcao(antes, s, r, bs, fecho, proxima, sem_parcial), {==}, consulta))
    case H.Quebrada{+prefixo}:
      match e:
        case CompletaObservada{+outros}: L.ex_falso(K.Regra7(I.EntregouTudo{outros}, a, k, x, t),
          Fases.ausente_exclui_consulta(Fases.Completa{}, Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), t, Q.Entregue{outros},
            fim_parcial_sem_completa(antes, s, r, bs, fecho, prefixo, sem_completa), {==}, consulta))
        case ParcialObservada{+outros}:
          F.com_par(K.Regra7(I.EntregaInterrompida{outros}, a, k, x, t),
            {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), t) == Some{Q.Interrompida{outros}} : Maybe<&2, Q.Quadro>},
            {Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), t) == Some{Q.Interrompida{outros}} : Maybe<&2, Q.Quadro>},
            Chamada.duplicar_igualdade(Maybe<&2, Q.Quadro>, Q.consultar(Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.Quebrada{prefixo})), t), Some{Q.Interrompida{outros}}, consulta),
            para_posicao => para_recibo => entrega_parcial_refletida_obedece_regra7(a, k, x, antes, s, r, bs, fecho, prefixo, t, outros, para_posicao, prefixo_real,
              falha(t, outros, para_recibo), sem_completa, sem_parcial, preparar, concluir, completa, parcial))
    case H.PendenteEntrega{}:
      match e:
        case CompletaObservada{+outros}: L.ex_falso(K.Regra7(I.EntregouTudo{outros}, a, k, x, t),
          Fases.ausente_exclui_consulta(Fases.Completa{}, Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.PendenteEntrega{})), t, Q.Entregue{outros},
            antes_da_entrega_sem_marca(Fases.Completa{}, antes, s, r, bs, fecho, sem_completa, {==}, {==}, {==}), {==}, consulta))
        case ParcialObservada{+outros}: L.ex_falso(K.Regra7(I.EntregaInterrompida{outros}, a, k, x, t),
          Fases.ausente_exclui_consulta(Fases.Interrompida{}, Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, H.PendenteEntrega{})), t, Q.Interrompida{outros},
            antes_da_entrega_sem_marca(Fases.Interrompida{}, antes, s, r, bs, fecho, sem_parcial, {==}, {==}, {==}), {==}, consulta))

def entrega_fonte_no_fecho(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +inicial: D.Estado, +rx: X.Recepcao,
  +antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecho: Bool, +en: H.Entrega, +t: Nat, +e: FatoEntrega,
  canonico: {I.Atender{mundo, c, inicial, rx} == Fonte.cenario(fonte, mundo) : I.Cenario},
  +mesma: {Vis.quadros_chamada(c, inicial, rx, Fonte.chamada(fonte, mundo)) == Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, en)) : List<&2, Q.Quadro>},
  limpas: L.E<{Fases.ausente(Fases.Completa{}, antes) == True{} : Bool}, {Fases.ausente(Fases.Interrompida{}, antes) == True{} : Bool}>,
  prefixo_real: PrefixoDaEscrita(N.Conclusao{s, r, bs}, en),
  falhas: Canal.FalhasDeEntregaReais(fonte, I.Atender{mundo, c, inicial, rx}, Vis.quadros_chamada(c, inicial, rx, Fonte.chamada(fonte, mundo))),
  consulta: {Q.consultar(Vis.quadros_chamada(c, inicial, rx, Fonte.chamada(fonte, mundo)), t) == Some{quadro_entrega(e)} : Maybe<&2, Q.Quadro>}) ->
  K.Regra7(fato_entrega(e), Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, t):
  F.com_par(K.Regra7(fato_entrega(e), Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, t),
    {I.Atender{mundo, c, inicial, rx} == Fonte.cenario(fonte, mundo) : I.Cenario}, {I.Atender{mundo, c, inicial, rx} == Fonte.cenario(fonte, mundo) : I.Cenario},
    Chamada.duplicar_igualdade(I.Cenario, I.Atender{mundo, c, inicial, rx}, Fonte.cenario(fonte, mundo), canonico),
    para_preparo => para_conclusao => F.com_par(K.Regra7(fato_entrega(e), Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, t),
      {Fases.ausente(Fases.Completa{}, antes) == True{} : Bool}, {Fases.ausente(Fases.Interrompida{}, antes) == True{} : Bool}, limpas,
      sem_completa => sem_parcial => entrega_no_sufixo_obedece_regra7(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx},
        antes, s, r, bs, fecho, en, t, e, sem_completa, sem_parcial, prefixo_real,
        (%mesma : {Q.consultar(_, t) == Some{quadro_entrega(e)} : Maybe<&2, Q.Quadro>} consulta),
        +u => +rp => +bytes => obtida => Lig.introduzir_na_lista(fonte, c, mundo, inicial, rx,
          Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, en)), u, Q.Preparada{rp, bytes}, I.Preparou{rp, bytes}, para_preparo, mesma, obtida, {==}, Unit{}),
        +u => +rp => +w => +fecha => obtida => Lig.introduzir_na_lista(fonte, c, mundo, inicial, rx,
          Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, en)), u, Q.Concluida{rp, w, fecha}, I.Concluiu{rp, w, fecha}, para_conclusao, mesma, obtida, {==}, Unit{}),
        +u => +bytes => fato => Lig.extrair_na_lista(fonte, c, mundo, inicial, rx,
          Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, en)), u, I.EntregouTudo{bytes}, mesma, Unit{}, fato),
        +u => +bytes => fato => Lig.extrair_na_lista(fonte, c, mundo, inicial, rx,
          Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, en)), u, I.EntregaInterrompida{bytes}, mesma, Unit{}, fato),
        +u => +bytes => obtida => falhas(u, bytes,
          (%Equal.sym(List<&2, Q.Quadro>, Vis.quadros_chamada(c, inicial, rx, Fonte.chamada(fonte, mundo)),
            Q.concatenar(antes, H.render_conclusao(N.Conclusao{s, r, bs}, fecho, en)), mesma) :
              {Q.consultar(_, u) == Some{Q.Interrompida{bytes}} : Maybe<&2, Q.Quadro>} obtida)))))

def consumir_entrega_selecionada(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +inicial: D.Estado,
  +rx: X.Recepcao, +caso: H.Caso, q: Maybe<&2, Fechos.Fecho>, +t: Nat, +e: FatoEntrega,
  canonico: {I.Atender{mundo, c, inicial, rx} == Fonte.cenario(fonte, mundo) : I.Cenario},
  forma: Fechos.Forma(Vis.quadros_chamada(c, inicial, rx, Fonte.chamada(fonte, mundo)), caso, q),
  limpas: Fechos.EntregasDaForma(Vis.quadros_chamada(c, inicial, rx, Fonte.chamada(fonte, mundo)), q),
  prefixo_real: PrefixosDoFecho(q),
  falhas: Canal.FalhasDeEntregaReais(fonte, I.Atender{mundo, c, inicial, rx}, Vis.quadros_chamada(c, inicial, rx, Fonte.chamada(fonte, mundo))),
  consulta: {Q.consultar(Vis.quadros_chamada(c, inicial, rx, Fonte.chamada(fonte, mundo)), t) == Some{quadro_entrega(e)} : Maybe<&2, Q.Quadro>}) ->
  K.Regra7(fato_entrega(e), Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, t):
  match q:
    case None{}: entrega_sem_fecho_impossivel(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx},
      Vis.quadros_chamada(c, inicial, rx, Fonte.chamada(fonte, mundo)), t, e, limpas, consulta)
    case Some{Fechos.Fecho{antes, N.Conclusao{w, r, bs}, fecho, en, origem}}:
      match forma:
        case L.Ambos{mesmo_caso, L.Ambos{traco, L.Ambos{pub, concl}}}:
          entrega_fonte_no_fecho(fonte, c, mundo, inicial, rx, antes, w, r, bs, fecho, en, t, e, canonico, traco, limpas, prefixo_real, falhas, consulta)

def consulta_da_entrega(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao,
  +t: Nat, e: FatoEntrega, obs: Fonte.da_rota(fonte, I.Atender{mundo, c, s, rx}, t, fato_entrega(e))) ->
  {Q.consultar(Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)), t) == Some{quadro_entrega(e)} : Maybe<&2, Q.Quadro>}:
  match e:
    case CompletaObservada{+bs}: Lig.quadro_da_observacao(fonte, c, s, rx, Fonte.chamada(fonte, mundo), t, I.EntregouTudo{bs}, Unit{}, obs)
    case ParcialObservada{+bs}: Lig.quadro_da_observacao(fonte, c, s, rx, Fonte.chamada(fonte, mundo), t, I.EntregaInterrompida{bs}, Unit{}, obs)

law entrega_da_chamada_obedece_regra7:
  for ~fonte: Fonte.Fonte
  for ~c: S.Configuracao
  for +mundo: Nat
  for +inicial: D.Estado
  for +rx: X.Recepcao
  for +t: Nat
  for +e: FatoEntrega
  for prefixo_real: PrefixosDoFecho(Fechos.fecho_do_caso(Lig.micro_dos_dados(Fonte.chamada(fonte, mundo)), inicial, Lig.caso_dos_dados(c, rx, Fonte.chamada(fonte, mundo))))
  for falhas: Canal.FalhasDeEntregaReais(fonte, I.Atender{mundo, c, inicial, rx}, Vis.quadros_chamada(c, inicial, rx, Fonte.chamada(fonte, mundo)))
  for observado: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, t, fato_entrega(e))
  K.Regra7(fato_entrega(e), Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, t)
def entrega_da_chamada_obedece_regra7(fonte, c, mundo, inicial, rx, t, e, prefixo_real, falhas, observado):
  F.com_par(K.Regra7(fato_entrega(e), Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, t),
    {Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
    L.E<{I.Atender{mundo, c, inicial, rx} == Fonte.cenario(fonte, mundo) : I.Cenario}, Fonte.da_rota(fonte, I.Atender{mundo, c, inicial, rx}, t, fato_entrega(e))>,
    Fonte.eliminar_fato_literal(fonte, Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, t, fato_entrega(e), observado),
    nome => origem => F.com_par(K.Regra7(fato_entrega(e), Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, t),
      {I.Atender{mundo, c, inicial, rx} == Fonte.cenario(fonte, mundo) : I.Cenario}, Fonte.da_rota(fonte, I.Atender{mundo, c, inicial, rx}, t, fato_entrega(e)), origem,
      canonico => obs => consumir_entrega_selecionada(fonte, c, mundo, inicial, rx, Lig.caso_dos_dados(c, rx, Fonte.chamada(fonte, mundo)),
        Fechos.fecho_do_caso(Lig.micro_dos_dados(Fonte.chamada(fonte, mundo)), inicial, Lig.caso_dos_dados(c, rx, Fonte.chamada(fonte, mundo))), t, e, canonico,
        (%Equal.sym(List<&2, Q.Quadro>, Vis.quadros_chamada(c, inicial, rx, Fonte.chamada(fonte, mundo)),
          H.render(Lig.micro_dos_dados(Fonte.chamada(fonte, mundo)), inicial, Lig.caso_dos_dados(c, rx, Fonte.chamada(fonte, mundo))),
          Lig.quadros_seguem_o_caso(c, inicial, rx, Fonte.chamada(fonte, mundo))) : Fechos.Forma(_, Lig.caso_dos_dados(c, rx, Fonte.chamada(fonte, mundo)),
            Fechos.fecho_do_caso(Lig.micro_dos_dados(Fonte.chamada(fonte, mundo)), inicial, Lig.caso_dos_dados(c, rx, Fonte.chamada(fonte, mundo))))
          Fechos.forma_da_rota(Lig.micro_dos_dados(Fonte.chamada(fonte, mundo)), inicial, Lig.caso_dos_dados(c, rx, Fonte.chamada(fonte, mundo)))),
        (%Equal.sym(List<&2, Q.Quadro>, Vis.quadros_chamada(c, inicial, rx, Fonte.chamada(fonte, mundo)),
          H.render(Lig.micro_dos_dados(Fonte.chamada(fonte, mundo)), inicial, Lig.caso_dos_dados(c, rx, Fonte.chamada(fonte, mundo))),
          Lig.quadros_seguem_o_caso(c, inicial, rx, Fonte.chamada(fonte, mundo))) : Fechos.EntregasDaForma(_,
            Fechos.fecho_do_caso(Lig.micro_dos_dados(Fonte.chamada(fonte, mundo)), inicial, Lig.caso_dos_dados(c, rx, Fonte.chamada(fonte, mundo))))
          Fechos.entregas_da_forma(Lig.micro_dos_dados(Fonte.chamada(fonte, mundo)), inicial, Lig.caso_dos_dados(c, rx, Fonte.chamada(fonte, mundo)))),
        prefixo_real, falhas, consulta_da_entrega(fonte, c, mundo, inicial, rx, t, e, obs))))


# Apenas o ramo real de entrada tem uma obrigacao de recusa de envelope.
def EntradaDoCaso(~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao, caso: H.Caso) -> Type:
  match caso:
    case H.EntradaRecusa{erro, fecha, en}: Causas.CausaEntrada(I.Atender{mundo, c, s, rx}, erro)
    case _: Unit

def sem_entrada_tem_causa(~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao, caso: H.Caso,
  nao: {eh_entrada(caso) == False{} : Bool}) -> EntradaDoCaso(c, mundo, s, rx, caso):
  match caso:
    case H.EntradaRecusa{+erro, fecha, en}: L.ex_falso(Causas.CausaEntrada(I.Atender{mundo, c, s, rx}, erro), F.falso_nao_verdadeiro(Equal.sym(Bool, True{}, False{}, nao)))
    case H.AutRecusa{r, en}: Unit{}
    case H.GateRecusa{r, ctx, en}: Unit{}
    case H.Executada{r, ctx, qs, p, en}: Unit{}
    case H.FalhaAntes{fase, etapa, id, fatal, en}: Unit{}
    case H.InicialOk{}: Unit{}
    case H.InicialRecusa{status}: Unit{}
    case H.InicialFalha{aceita, etapa, id, fatal}: Unit{}
    case H.SemResposta{}: Unit{}
    case H.FatalAposPublicacao{r, ctx, qs, p, etapa, id}: Unit{}
    case H.Pendente{fase}: Unit{}
    case H.InicialPendente{aceita}: Unit{}

# Os parametros sao as medidas e bytes reais, nao uma hipotese EntradaInvalida.
def CopiaDoCorpo(~c: S.Configuracao, +s: D.Estado, +rx: X.Recepcao, +be: List<&2, U32>, +br: List<&2, U32>, +bs: List<&2, U32>) -> Type:
  L.E<Causas.EstadoCopiado(c, s, be), L.E<Causas.CorpoCopiado(c, rx),
    L.E<{Transporte.juntar(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>},
      L.E<{B.octetos_validos(br) == True{} : Bool},
        L.E<{D.estrutura(S.esquema(c), s) == True{} : Bool},
          {X.decidir_recepcao(c, rx) == X.ProcessarCorpo{br} : X.Disposicao}>>>>>

def causa_com_medidas_do_corpo(~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao,
  +be: List<&2, U32>, +br: List<&2, U32>, +bs: List<&2, U32>, +status: S.Status, +ce: B.Numero64, +te: B.Numero64,
  cod_e: P.Codificacao(D.estado_valor(s), be), montagem: {Transporte.juntar(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>},
  medida_e: {B.nat64(B.comprimento(be)) == Some{ce} : Maybe<&2, B.Numero64>}, teto_e: {B.nat64(R.limite_estado(S.limites(c))) == Some{te} : Maybe<&2, B.Numero64>},
  cabe_e: {Codec.menor_igual64(ce, te) == True{} : Bool}, octetos_r: {B.octetos_validos(br) == True{} : Bool},
  estrutura: {D.estrutura(S.esquema(c), s) == True{} : Bool}, recebido: {X.decidir_recepcao(c, rx) == X.ProcessarCorpo{br} : X.Disposicao},
  real: {Entrada.decodificar(bs, S.esquema(c), S.limites(c)) == Entrada.ErroMensagem{status} : Entrada.PreAutenticacao},
  medidas: &cr: B.Numero64 -> &tr: B.Numero64 -> L.E<{B.nat64(B.comprimento(br)) == Some{cr} : Maybe<&2, B.Numero64>},
    L.E<{B.nat64(R.limite_mensagem(S.limites(c))) == Some{tr} : Maybe<&2, B.Numero64>}, {Codec.menor_igual64(cr, tr) == True{} : Bool}>>) ->
  Causas.CausaEntrada(I.Atender{mundo, c, s, rx}, H.erro_de_mensagem(status)):
  match medidas:
    case (+cr, +tr, L.Ambos{medida_r, L.Ambos{teto_r, cabe_r}}):
      +canon_e = {cod_e : {P.codificar(D.estado_valor(s)) == Some{be} : Maybe<&2, List<&2, U32>>}}
      Causas.erro_do_corpo_processado_tem_causa_original(c, mundo, s, rx, be, br, bs, ce, cr, te, tr, status,
        canon_e, montagem, Octetos.qualquer_codificacao_so_emite_octetos(D.estado_valor(s), be, canon_e), octetos_r,
        medida_e, medida_r, teto_e, teto_r, cabe_e, cabe_r, estrutura, recebido, real)

def causa_pela_copia(~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao,
  +be: List<&2, U32>, +br: List<&2, U32>, +bs: List<&2, U32>, +status: S.Status, copia: CopiaDoCorpo(c, s, rx, be, br, bs),
  real: {Entrada.decodificar(bs, S.esquema(c), S.limites(c)) == Entrada.ErroMensagem{status} : Entrada.PreAutenticacao}) ->
  Causas.CausaEntrada(I.Atender{mundo, c, s, rx}, H.erro_de_mensagem(status)):
  match copia:
    case L.Ambos{(+ce, +te, L.Ambos{cod_e, L.Ambos{medida_e, L.Ambos{teto_e, cabe_e}}}),
      L.Ambos{L.Ambos{recepcao_valida, medir}, L.Ambos{montagem, L.Ambos{octetos_r, L.Ambos{estrutura, +recebido}}}}}:
      causa_com_medidas_do_corpo(c, mundo, s, rx, be, br, bs, status, ce, te, cod_e, montagem,
        medida_e, teto_e, cabe_e, octetos_r, estrutura, recebido, real, medir(br, recebido))

def pre_tem_causa(~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao,
  +be: List<&2, U32>, +br: List<&2, U32>, +bs: List<&2, U32>, pre: Entrada.PreAutenticacao, +dados: H.DadosFerramentas,
  copia: CopiaDoCorpo(c, s, rx, be, br, bs), real: {Entrada.decodificar(bs, S.esquema(c), S.limites(c)) == pre : Entrada.PreAutenticacao}) ->
  EntradaDoCaso(c, mundo, s, rx, H.decidir_pre(pre, dados)):
  match pre:
    case Entrada.Pronta{+decodificado, +r}: sem_entrada_tem_causa(c, mundo, s, rx, H.decidir_autenticacao(H.preprocessamento(dados), decodificado, r, dados),
      autenticacao_nao_e_entrada(H.preprocessamento(dados), decodificado, r, dados))
    case Entrada.ErroMensagem{+status}:
      match dados:
        case H.DadosFerramentas{j, ex, li, en, pipe}: causa_pela_copia(c, mundo, s, rx, be, br, bs, status, copia, real)
    case Entrada.ErroTransporte{}:
      match dados:
        case H.DadosFerramentas{j, ex, li, en, pipe}: Unit{}

def decode_tem_causa(~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao,
  +be: List<&2, U32>, +br: List<&2, U32>, +bs: List<&2, U32>, pre: H.Preprocessamento, dados: H.DadosFerramentas,
  copia: CopiaDoCorpo(c, s, rx, be, br, bs)) -> EntradaDoCaso(c, mundo, s, rx, H.decidir_decode(pre, bs, S.esquema(c), S.limites(c), dados)):
  match pre:
    case H.FalhaDecode{id, fatal}: Unit{}
    case H.PendenteDecode{}: Unit{}
    case H.Normal{}: pre_tem_causa(c, mundo, s, rx, be, br, bs, Entrada.decodificar(bs, S.esquema(c), S.limites(c)), dados, copia, {==})
    case H.FalhaEnquadramento{id, fatal}: pre_tem_causa(c, mundo, s, rx, be, br, bs, Entrada.decodificar(bs, S.esquema(c), S.limites(c)), dados, copia, {==})
    case H.FalhaAuth{id, fatal}: pre_tem_causa(c, mundo, s, rx, be, br, bs, Entrada.decodificar(bs, S.esquema(c), S.limites(c)), dados, copia, {==})
    case H.PendenteEnquadramento{}: pre_tem_causa(c, mundo, s, rx, be, br, bs, Entrada.decodificar(bs, S.esquema(c), S.limites(c)), dados, copia, {==})
    case H.PendenteAuth{}: pre_tem_causa(c, mundo, s, rx, be, br, bs, Entrada.decodificar(bs, S.esquema(c), S.limites(c)), dados, copia, {==})

def pacote_tem_causa(~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao,
  +be: List<&2, U32>, +br: List<&2, U32>, pacote: Maybe<&2, List<&2, U32>>, +dados: H.DadosFerramentas,
  estado: Causas.EstadoCopiado(c, s, be), corpo: Causas.CorpoCopiado(c, rx),
  octetos_r: {B.octetos_validos(br) == True{} : Bool}, estrutura: {D.estrutura(S.esquema(c), s) == True{} : Bool},
  recebido: {X.decidir_recepcao(c, rx) == X.ProcessarCorpo{br} : X.Disposicao},
  montagem: {Transporte.juntar(be, br) == pacote : Maybe<&2, List<&2, U32>>}) ->
  EntradaDoCaso(c, mundo, s, rx, H.decidir_pacote(pacote, S.esquema(c), S.limites(c), dados)):
  match pacote:
    case None{}:
      match dados:
        case H.DadosFerramentas{j, ex, li, en, pipe}: Unit{}
    case Some{+bs}: decode_tem_causa(c, mundo, s, rx, be, br, bs, H.preprocessamento(dados), dados,
      L.Ambos{estado, L.Ambos{corpo, L.Ambos{montagem, L.Ambos{octetos_r, L.Ambos{estrutura, recebido}}}}})

# Os unicos status que o header real pode recusar sao Entrada e Limite.
def StatusDoHeader(status: S.Status) -> Type:
  match status:
    case S.Entrada{}: Unit
    case S.Limite{}: Unit
    case _: Empty

def HeaderReal(d: X.Disposicao) -> Type:
  match d:
    case X.RecusarEncerrar{status}: StatusDoHeader(status)
    case X.RecusarContinuar{status}: Empty
    case _: Unit

def header_truncado_real(acima: Bool) -> HeaderReal(X.truncado_casos(acima)):
  match acima:
    case False{}: Unit{}
    case True{}: Unit{}

def header_completo_real(acima: Bool, br: List<&2, U32>) -> HeaderReal(X.completo_casos(acima, br)):
  match acima:
    case False{}: Unit{}
    case True{}: Unit{}

def recepcao_tem_header_real(~c: S.Configuracao, rx: X.Recepcao) -> HeaderReal(X.decidir_recepcao(c, rx)):
  match rx:
    case X.EOFEntreMensagens{}: Unit{}
    case X.ParadaOperador{}: Unit{}
    case X.HeaderTruncado{bs}: Unit{}
    case X.BodyTruncado{a, b, bs}: header_truncado_real(X.declarado_maior(a, b, R.limite_mensagem(S.limites(c))))
    case X.CorpoRecebido{a, b, bs}: header_completo_real(X.declarado_maior(a, b, R.limite_mensagem(S.limites(c))), bs)

def disposicao_tem_causa(~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao,
  +be: List<&2, U32>, +d: X.Disposicao, +dados: H.DadosFerramentas,
  estado: Causas.EstadoCopiado(c, s, be), corpo: Causas.CorpoCopiado(c, rx),
  octetos_r: Dois.OctetosRecebidos(d), estrutura: {D.estrutura(S.esquema(c), s) == True{} : Bool},
  header: HeaderReal(d), recebido: {X.decidir_recepcao(c, rx) == d : X.Disposicao}) ->
  EntradaDoCaso(c, mundo, s, rx, H.decidir_disposicao(d, be, S.esquema(c), S.limites(c), dados)):
  match d:
    case X.EncerrarSemResposta{}: Unit{}
    case X.RecusarEncerrar{status}:
      match status:
        case S.Entrada{}:
          match dados:
            case H.DadosFerramentas{j, ex, li, en, pre}: L.Esquerda{L.Esquerda{recebido}}
        case S.Limite{}:
          match dados:
            case H.DadosFerramentas{j, ex, li, en, pre}: recebido
        case S.Sucesso{}: match header:
        case S.Recusa{}: match header:
        case S.Autenticacao{}: match header:
        case S.Certificado{}: match header:
        case S.Dados{}: match header:
        case S.Falha{}: match header:
    case X.RecusarContinuar{+status}: L.ex_falso(EntradaDoCaso(c, mundo, s, rx, H.decidir_disposicao(X.RecusarContinuar{status}, be, S.esquema(c), S.limites(c), dados)), header)
    case X.ProcessarCorpo{+br}: pacote_tem_causa(c, mundo, s, rx, be, br, Transporte.juntar(be, br), dados,
      estado, corpo, octetos_r, estrutura, recebido, {==})

def enquadramento_tem_causa(~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao,
  +be: List<&2, U32>, pre: H.Preprocessamento, +d: X.Disposicao, +dados: H.DadosFerramentas,
  estado: Causas.EstadoCopiado(c, s, be), corpo: Causas.CorpoCopiado(c, rx),
  octetos_r: Dois.OctetosRecebidos(d), estrutura: {D.estrutura(S.esquema(c), s) == True{} : Bool},
  header: HeaderReal(d), recebido: {X.decidir_recepcao(c, rx) == d : X.Disposicao}) ->
  EntradaDoCaso(c, mundo, s, rx, H.decidir_enquadramento(pre, d, be, S.esquema(c), S.limites(c), dados)):
  match pre:
    case H.FalhaEnquadramento{id, fatal}: Unit{}
    case H.PendenteEnquadramento{}: Unit{}
    case H.Normal{}: disposicao_tem_causa(c, mundo, s, rx, be, d, dados, estado, corpo, octetos_r, estrutura, header, recebido)
    case H.FalhaDecode{id, fatal}: disposicao_tem_causa(c, mundo, s, rx, be, d, dados, estado, corpo, octetos_r, estrutura, header, recebido)
    case H.FalhaAuth{id, fatal}: disposicao_tem_causa(c, mundo, s, rx, be, d, dados, estado, corpo, octetos_r, estrutura, header, recebido)
    case H.PendenteDecode{}: disposicao_tem_causa(c, mundo, s, rx, be, d, dados, estado, corpo, octetos_r, estrutura, header, recebido)
    case H.PendenteAuth{}: disposicao_tem_causa(c, mundo, s, rx, be, d, dados, estado, corpo, octetos_r, estrutura, header, recebido)

law entrada_da_decisao_tem_causa_original:
  for ~c: S.Configuracao
  for +mundo: Nat
  for +s: D.Estado
  for +rx: X.Recepcao
  for +be: List<&2, U32>
  for +dados: H.DadosFerramentas
  for estado: Causas.EstadoCopiado(c, s, be)
  for corpo: Causas.CorpoCopiado(c, rx)
  for octetos_r: Dois.OctetosRecebidos(X.decidir_recepcao(c, rx))
  for estrutura: {D.estrutura(S.esquema(c), s) == True{} : Bool}
  EntradaDoCaso(c, mundo, s, rx, H.decidir(c, rx, be, dados))
def entrada_da_decisao_tem_causa_original(c, mundo, s, rx, be, dados, estado, corpo, octetos_r, estrutura):
  %Equal.sym(H.Caso, H.decidir(c, rx, be, dados), H.decidir_enquadramento(H.preprocessamento(dados), X.decidir_recepcao(c, rx), be, S.esquema(c), S.limites(c), dados),
    Dois.decidir_por_recepcao(c, rx, be, dados)) : EntradaDoCaso(c, mundo, s, rx, _)
  enquadramento_tem_causa(c, mundo, s, rx, be, H.preprocessamento(dados), X.decidir_recepcao(c, rx), dados,
    estado, corpo, octetos_r, estrutura, recepcao_tem_header_real(c, rx), {==})


# A ultima avaliacao pertence ao prefixo fisico que precede preparar.
def prefixo_de_execucao_agrupado(+m: H.Micro, +req: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>) ->
  {Con{Q.Configurada{}, Fechos.antes_execucao(m, req, ctx, xs)} ==
    Lei5.subtraco(Con{Q.Configurada{}, H.render_comecada(m, req, ctx)}, Q.expandir_exec(req, ctx, xs), H.micro_saida(m)) : List<&2, Q.Quadro>}:
  Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, ys => Con{Q.Configurada{}, ys},
    Q.concatenar(Q.concatenar(H.render_comecada(m, req, ctx), Q.expandir_exec(req, ctx, xs)), H.micro_saida(m)),
    Q.concatenar(H.render_comecada(m, req, ctx), Q.concatenar(Q.expandir_exec(req, ctx, xs), H.micro_saida(m))),
    Q.concatenar_assoc(H.render_comecada(m, req, ctx), Q.expandir_exec(req, ctx, xs), H.micro_saida(m)))

def avaliacao_no_prefixo_nativo(+m: H.Micro, +req: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>,
  +w: D.Estado, +ts: List<&2, S.Evento>, +proposta: S.Resposta,
  indice: &i: Nat -> {Exec.consultar(xs, i) == Some{Q.Avaliacao{S.Final{w, ts, proposta}}} : Maybe<&2, Q.QuadroExec>}) ->
  &u: Nat -> {Q.consultar(Con{Q.Configurada{}, Fechos.antes_execucao(m, req, ctx, xs)}, u) == Some{Q.Avaliada{req, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>}:
  match indice:
    case (+i, presente):
      (Nat.add(Q.tamanho(Con{Q.Configurada{}, H.render_comecada(m, req, ctx)}), i),
        Equal.trans(Maybe<&2, Q.Quadro>,
          Q.consultar(Con{Q.Configurada{}, Fechos.antes_execucao(m, req, ctx, xs)}, Nat.add(Q.tamanho(Con{Q.Configurada{}, H.render_comecada(m, req, ctx)}), i)),
          Q.consultar(Lei5.subtraco(Con{Q.Configurada{}, H.render_comecada(m, req, ctx)}, Q.expandir_exec(req, ctx, xs), H.micro_saida(m)), Nat.add(Q.tamanho(Con{Q.Configurada{}, H.render_comecada(m, req, ctx)}), i)),
          Some{Q.Avaliada{req, ctx, S.Final{w, ts, proposta}}},
          Equal.cong(List<&2, Q.Quadro>, Maybe<&2, Q.Quadro>, ys => Q.consultar(ys, Nat.add(Q.tamanho(Con{Q.Configurada{}, H.render_comecada(m, req, ctx)}), i)),
            Con{Q.Configurada{}, Fechos.antes_execucao(m, req, ctx, xs)},
            Lei5.subtraco(Con{Q.Configurada{}, H.render_comecada(m, req, ctx)}, Q.expandir_exec(req, ctx, xs), H.micro_saida(m)), prefixo_de_execucao_agrupado(m, req, ctx, xs)),
          Lei5.consulta_do_subtraco(Con{Q.Configurada{}, H.render_comecada(m, req, ctx)}, Q.expandir_exec(req, ctx, xs), H.micro_saida(m), i, Q.Avaliada{req, ctx, S.Final{w, ts, proposta}},
            Exec.expandir_preserva_consulta(req, ctx, xs, i, Q.Avaliacao{S.Final{w, ts, proposta}}, presente))))

def preparo_codigo_com_campos_reais(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  -a: I.Ambiente, -k: String, -x: I.Cenario, +m: H.Micro, +antes: List<&2, Q.Quadro>, +depois: List<&2, Q.Quadro>,
  +s: D.Estado, +req: P.Requisicao, +ctx: D.Contexto, +codigo: Fonte.JuizoSintatico, +xs: List<&2, Q.QuadroExec>,
  +n: Nat, +w: D.Estado, +ts: List<&2, S.Evento>, +proposta: S.Resposta, +r: S.Resposta, +bs: List<&2, U32>,
  prefixo: {antes == Con{Q.Configurada{}, Fechos.antes_execucao(m, req, ctx, xs)} : List<&2, Q.Quadro>},
  sequencia: {xs == Exec.gerar(n, N.iniciar(Fonte.programa(fonte, codigo), ctx, I.argumentos(req), s), S.esquema(c)) : List<&2, Q.QuadroExec>},
  +resultado: {N.percorrer(n, N.iniciar(Fonte.programa(fonte, codigo), ctx, I.argumentos(req), s), S.esquema(c)) == S.Final{w, ts, proposta} : S.Percurso},
  obtida: {N.preparar(N.Parada{w, ts, proposta}, c) == Some{N.Preparada{w, ts, r, bs}} : Maybe<&2, N.Preparada>},
  configuracao: {I.configuracao(x) == c : S.Configuracao}, valida: {R.configuracao_valida(c) == True{} : Bool},
  avaliar: @u: Nat -> {Q.consultar(Q.concatenar(antes, Con{Q.Preparada{r, bs}, depois}), u) == Some{Q.Avaliada{req, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>} ->
    I.Acontece(a, k, x, u, I.Avaliou{req, ctx, Fonte.programa(fonte, codigo), S.Final{w, ts, proposta}})) ->
  K.Regra7(I.Preparou{r, bs}, a, k, x, Nat.add(Q.tamanho(antes), 0n)):
  preparo_de_programa_obedece_regra7(fonte, c, a, k, x, antes, Con{Q.Preparada{r, bs}, depois}, s, req, ctx, codigo, n, w, ts, proposta, r, bs,
    configuracao, valida, obtida, resultado,
    (%Equal.sym(List<&2, Q.Quadro>, antes, Con{Q.Configurada{}, Fechos.antes_execucao(m, req, ctx, xs)}, prefixo) :
      (&u: Nat -> {Q.consultar(_, u) == Some{Q.Avaliada{req, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>})
      avaliacao_no_prefixo_nativo(m, req, ctx, xs, w, ts, proposta, ultima_avaliacao_do_resultado_real(fonte, c, s, req, ctx, codigo, n, w, ts, proposta, xs, sequencia, resultado))), avaliar)

def trabalho_preparado(p: N.Preparada) -> D.Estado:
  match p:
    case N.Preparada{w, ts, r, bs}: w

def eventos_preparados(p: N.Preparada) -> List<&2, S.Evento>:
  match p:
    case N.Preparada{w, ts, r, bs}: ts

def campos_normalizados_preparada(+wp: D.Estado, +tsp: List<&2, S.Evento>, +rp: S.Resposta, +bs: List<&2, U32>,
  +w: D.Estado, +ts: List<&2, S.Evento>, +r: S.Resposta,
  +igual: {N.Preparada{wp, tsp, rp, bs} == N.Preparada{w, ts, r, bs} : N.Preparada}) ->
  L.E<{wp == w : D.Estado}, {tsp == ts : List<&2, S.Evento>}>:
  L.Ambos{Equal.cong(N.Preparada, D.Estado, trabalho_preparado, N.Preparada{wp, tsp, rp, bs}, N.Preparada{w, ts, r, bs}, igual),
    Equal.cong(N.Preparada, List<&2, S.Evento>, eventos_preparados, N.Preparada{wp, tsp, rp, bs}, N.Preparada{w, ts, r, bs}, igual)}

def preparo_codigo_reindexado(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  -a: I.Ambiente, -k: String, -x: I.Cenario, +m: H.Micro, +antes: List<&2, Q.Quadro>, +depois: List<&2, Q.Quadro>,
  +s: D.Estado, +req: P.Requisicao, +ctx: D.Contexto, +codigo: Fonte.JuizoSintatico, +xs: List<&2, Q.QuadroExec>,
  +n: Nat, +w: D.Estado, +ts: List<&2, S.Evento>, +proposta: S.Resposta,
  +wp: D.Estado, +tsp: List<&2, S.Evento>, +rp: S.Resposta, +bs: List<&2, U32>,
  prefixo: {antes == Con{Q.Configurada{}, Fechos.antes_execucao(m, req, ctx, xs)} : List<&2, Q.Quadro>},
  sequencia: {xs == Exec.gerar(n, N.iniciar(Fonte.programa(fonte, codigo), ctx, I.argumentos(req), s), S.esquema(c)) : List<&2, Q.QuadroExec>},
  resultado: {N.percorrer(n, N.iniciar(Fonte.programa(fonte, codigo), ctx, I.argumentos(req), s), S.esquema(c)) == S.Final{w, ts, proposta} : S.Percurso},
  obtida: {N.preparar(N.Parada{w, ts, proposta}, c) == Some{N.Preparada{wp, tsp, rp, bs}} : Maybe<&2, N.Preparada>},
  configuracao: {I.configuracao(x) == c : S.Configuracao}, valida: {R.configuracao_valida(c) == True{} : Bool},
  avaliar: @u: Nat -> {Q.consultar(Q.concatenar(antes, Con{Q.Preparada{rp, bs}, depois}), u) == Some{Q.Avaliada{req, ctx, S.Final{wp, tsp, proposta}}} : Maybe<&2, Q.Quadro>} ->
    I.Acontece(a, k, x, u, I.Avaliou{req, ctx, Fonte.programa(fonte, codigo), S.Final{wp, tsp, proposta}}),
  campos: L.E<{wp == w : D.Estado}, {tsp == ts : List<&2, S.Evento>}>) -> K.Regra7(I.Preparou{rp, bs}, a, k, x, Nat.add(Q.tamanho(antes), 0n)):
  match campos:
    case L.Ambos{+estado, +eventos}:
      preparo_codigo_com_campos_reais(fonte, c, a, k, x, m, antes, depois, s, req, ctx, codigo, xs, n, wp, tsp, proposta, rp, bs, prefixo, sequencia,
        (%Equal.sym(D.Estado, wp, w, estado) : {N.percorrer(n, N.iniciar(Fonte.programa(fonte, codigo), ctx, I.argumentos(req), s), S.esquema(c)) == S.Final{_, tsp, proposta} : S.Percurso}
          %Equal.sym(List<&2, S.Evento>, tsp, ts, eventos) : {N.percorrer(n, N.iniciar(Fonte.programa(fonte, codigo), ctx, I.argumentos(req), s), S.esquema(c)) == S.Final{w, _, proposta} : S.Percurso} resultado),
        (%Equal.sym(D.Estado, wp, w, estado) : {N.preparar(N.Parada{_, tsp, proposta}, c) == Some{N.Preparada{wp, tsp, rp, bs}} : Maybe<&2, N.Preparada>}
          %Equal.sym(List<&2, S.Evento>, tsp, ts, eventos) : {N.preparar(N.Parada{w, _, proposta}, c) == Some{N.Preparada{wp, tsp, rp, bs}} : Maybe<&2, N.Preparada>} obtida), configuracao, valida, avaliar)

def preparo_codigo_de_final_real(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  -a: I.Ambiente, -k: String, -x: I.Cenario, +m: H.Micro, +antes: List<&2, Q.Quadro>, +depois: List<&2, Q.Quadro>,
  +s: D.Estado, +req: P.Requisicao, +ctx: D.Contexto, +codigo: Fonte.JuizoSintatico, +xs: List<&2, Q.QuadroExec>, p: N.Preparada,
  prefixo: {antes == Con{Q.Configurada{}, Fechos.antes_execucao(m, req, ctx, xs)} : List<&2, Q.Quadro>},
  real: Fonte.FinalReal(fonte, c, s, req, ctx, codigo, xs, p),
  configuracao: {I.configuracao(x) == c : S.Configuracao}, valida: {R.configuracao_valida(c) == True{} : Bool},
  avaliar: @u: Nat -> @w: D.Estado -> @ts: List<&2, S.Evento> -> @proposta: S.Resposta ->
    {Q.consultar(Q.concatenar(antes, Con{H.quadro_preparada(p), depois}), u) == Some{Q.Avaliada{req, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>} ->
      I.Acontece(a, k, x, u, I.Avaliou{req, ctx, Fonte.programa(fonte, codigo), S.Final{w, ts, proposta}})) ->
  K.Regra7(I.Preparou{U.resposta(p), Preparacao.bytes_preparados(p)}, a, k, x, Nat.add(Q.tamanho(antes), 0n)):
  match p:
    case N.Preparada{+wp, +tsp, +rp, +bs}:
      match real:
        case (+n, +w, +ts, +proposta, L.Ambos{sequencia, L.Ambos{resultado, +obtida}}):
          preparo_codigo_reindexado(fonte, c, a, k, x, m, antes, depois, s, req, ctx, codigo, xs, n, w, ts, proposta, wp, tsp, rp, bs,
            prefixo, sequencia, resultado, obtida, configuracao, valida, +u => consulta => avaliar(u, wp, tsp, proposta, consulta),
            campos_normalizados_preparada(wp, tsp, rp, bs, w, ts, R.finalizar(proposta, c, w),
              L.e_esquerda(
                {N.Preparada{wp, tsp, rp, bs} == N.Preparada{w, ts, R.finalizar(proposta, c, w), bs} : N.Preparada},
                P.Mensagem(S.resposta_valor(R.finalizar(proposta, c, w)), bs),
                normalizar_preparada_real(c, w, ts, proposta, N.Preparada{wp, tsp, rp, bs}, obtida))))


def fato_preparo(q: Q.Quadro) -> I.Fato:
  match q:
    case Q.Preparada{r, bs}: I.Preparou{r, bs}
    case _: I.ProvaInicialAceita{}

def transportar_preparo7(-a: I.Ambiente, -k: String, -x: I.Cenario, +antes: List<&2, Q.Quadro>, -t: Nat,
  +r: S.Resposta, +bs: List<&2, U32>, +q: Q.Quadro,
  pos: {t == Nat.add(Q.tamanho(antes), 0n) : Nat}, igual: {Q.Preparada{r, bs} == q : Q.Quadro},
  canonica: K.Regra7(fato_preparo(q), a, k, x, Nat.add(Q.tamanho(antes), 0n))) -> K.Regra7(I.Preparou{r, bs}, a, k, x, t):
  %Equal.sym(Nat, t, Nat.add(Q.tamanho(antes), 0n), pos) : K.Regra7(I.Preparou{r, bs}, a, k, x, _)
  %Equal.sym(Q.Quadro, Q.Preparada{r, bs}, q, igual) : K.Regra7(fato_preparo(_), a, k, x, Nat.add(Q.tamanho(antes), 0n))
  canonica

# Esta funcao nao escolhe um programa alternativo: a raiz e a da mesma fonte.
def preparo_nativo_da_fonte(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +inicial: D.Estado, +rx: X.Recepcao,
  +m: H.Micro, +antes: List<&2, Q.Quadro>, +depois: List<&2, Q.Quadro>, +req: P.Requisicao, +ctx: D.Contexto,
  +codigo: Fonte.JuizoSintatico, +xs: List<&2, Q.QuadroExec>, +p: N.Preparada,
  canonico: {I.Atender{mundo, c, inicial, rx} == Fonte.cenario(fonte, mundo) : I.Cenario},
  +traco: {Vis.quadros_chamada(c, inicial, rx, Fonte.chamada(fonte, mundo)) == Q.concatenar(antes, Con{H.quadro_preparada(p), depois}) : List<&2, Q.Quadro>},
  prefixo: {antes == Con{Q.Configurada{}, Fechos.antes_execucao(m, req, ctx, xs)} : List<&2, Q.Quadro>},
  real: Fonte.FinalReal(fonte, c, inicial, req, ctx, codigo, xs, p), valida: {R.configuracao_valida(c) == True{} : Bool},
  mesma_raiz: {Fonte.programa(fonte, codigo) == Lei5.programa_do_mundo(fonte, mundo) : S.Programa}) ->
  K.Regra7(I.Preparou{U.resposta(p), Preparacao.bytes_preparados(p)}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, Nat.add(Q.tamanho(antes), 0n)):
  preparo_codigo_de_final_real(fonte, c, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, m, antes, depois,
    inicial, req, ctx, codigo, xs, p, prefixo, real, {==}, valida,
    +u => +w => +ts => +proposta => consulta =>
      (%Equal.sym(S.Programa, Fonte.programa(fonte, codigo), Lei5.programa_do_mundo(fonte, mundo), mesma_raiz) :
        I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, u, I.Avaliou{req, ctx, _, S.Final{w, ts, proposta}})
        Lig.introduzir_na_lista(fonte, c, mundo, inicial, rx, Q.concatenar(antes, Con{H.quadro_preparada(p), depois}), u,
          Q.Avaliada{req, ctx, S.Final{w, ts, proposta}}, I.Avaliou{req, ctx, Lei5.programa_do_mundo(fonte, mundo), S.Final{w, ts, proposta}},
          canonico, traco, consulta, {==}, Unit{})))

def fato_causal(q: Q.Quadro) -> I.Fato:
  match q:
    case Q.Autenticada{r, ctx}: I.Autenticou{r, ctx}
    case Q.Rejeitada{r, ctx}: I.CertificadoRejeitado{r, ctx}
    case Q.Falhou{etapa, id, fatal}: I.FalhouAmbiente{etapa, id, fatal}
    case _: I.ProvaInicialAceita{}

def quadro_causal_do_prefixo(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao,
  +antes: List<&2, Q.Quadro>, +depois: List<&2, Q.Quadro>, +u: Nat, +q: Q.Quadro,
  canonico: {I.Atender{mundo, c, s, rx} == Fonte.cenario(fonte, mundo) : I.Cenario},
  traco: {Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)) == Q.concatenar(antes, depois) : List<&2, Q.Quadro>},
  +presente: {Q.consultar(antes, u) == Some{q} : Maybe<&2, Q.Quadro>},
  relacao: Q.rel_fato(c, Lei5.programa_do_mundo(fonte, mundo), q, fato_causal(q)), marco: Lig.Marco(fato_causal(q))) ->
  I.Antes(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, Nat.add(Q.tamanho(antes), 0n), fato_causal(q)):
  (u, L.Ambos{menor_que_soma_por_direita(u, Q.tamanho(antes), 0n, Q.posicao_presente_dentro(antes, u, q, presente)),
    Lig.introduzir_na_lista(fonte, c, mundo, s, rx, Q.concatenar(antes, depois), u, q, fato_causal(q), canonico, traco,
      Adm.consulta_prefixo(antes, depois, u, q, presente), relacao, marco)})

# A origem fixa retida pela inversao impede usar uma causa de outro ramo.
def causa_fixa_do_caso(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao,
  +m: H.Micro, +antes: List<&2, Q.Quadro>, +depois: List<&2, Q.Quadro>, +e: Erros.Erro, caso: H.Caso,
  canonico: {I.Atender{mundo, c, s, rx} == Fonte.cenario(fonte, mundo) : I.Cenario},
  traco: {Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)) == Q.concatenar(antes, depois) : List<&2, Q.Quadro>},
  origem: Fechos.FixoDoCaso(e, caso), prefixo: Fechos.PrefixoFixo(m, caso, antes),
  entrada: EntradaDoCaso(c, mundo, s, rx, caso), pedido: Fonte.PedidoDoCaso(c, Fonte.Atendimento{mundo, s, rx}, caso)) ->
  I.RespostaJustificada(S.resposta_erro(Erros.status(e)), Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, Nat.add(Q.tamanho(antes), 0n)):
  match caso:
    case H.EntradaRecusa{H.Entrada{}, fecha, en}:
      %Equal.sym(Erros.Erro, e, Erros.Entrada{}, origem) :
        I.RespostaJustificada(S.resposta_erro(Erros.status(_)), Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, Nat.add(Q.tamanho(antes), 0n))
      entrada
    case H.EntradaRecusa{H.Limite{}, fecha, en}:
      %Equal.sym(Erros.Erro, e, Erros.Limite{}, origem) :
        I.RespostaJustificada(S.resposta_erro(Erros.status(_)), Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, Nat.add(Q.tamanho(antes), 0n))
      L.Esquerda{entrada}
    case H.AutRecusa{+req, en}:
      %Equal.sym(Erros.Erro, e, Erros.Autenticacao{}, origem) :
        I.RespostaJustificada(S.resposta_erro(Erros.status(_)), Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, Nat.add(Q.tamanho(antes), 0n))
      (req, L.Ambos{quadro_causal_do_prefixo(fonte, c, mundo, s, rx, antes, depois, Adm.indice_auth(m, req), Q.Autenticada{req, None{}},
        canonico, traco,
        (%Equal.sym(List<&2, Q.Quadro>, antes, Con{Q.Configurada{}, Fechos.antes_autenticacao(m, req)}, prefixo) :
          {Q.consultar(_, Adm.indice_auth(m, req)) == Some{Q.Autenticada{req, None{}}} : Maybe<&2, Q.Quadro>} Adm.consulta_auth(m, req, None{})), {==}, Unit{}), pedido})
    case H.GateRecusa{+req, +ctx, en}:
      %Equal.sym(Erros.Erro, e, Erros.Certificado{}, origem) :
        I.RespostaJustificada(S.resposta_erro(Erros.status(_)), Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, Nat.add(Q.tamanho(antes), 0n))
      (req, ctx, quadro_causal_do_prefixo(fonte, c, mundo, s, rx, antes, depois,
        Nat.add(Q.tamanho(Con{Q.Configurada{}, H.render_autenticada(m, req, ctx)}), 0n), Q.Rejeitada{req, ctx}, canonico, traco,
        (%Equal.sym(List<&2, Q.Quadro>, antes, Con{Q.Configurada{}, Fechos.antes_gate(m, req, ctx)}, prefixo) :
          {Q.consultar(_, Nat.add(Q.tamanho(Con{Q.Configurada{}, H.render_autenticada(m, req, ctx)}), 0n)) == Some{Q.Rejeitada{req, ctx}} : Maybe<&2, Q.Quadro>}
          Adm.consulta_da_marca(Con{Q.Configurada{}, H.render_autenticada(m, req, ctx)}, Q.Rejeitada{req, ctx})), {==}, Unit{}))
    case H.FalhaAntes{+fase, +etapa, +id, +fatal, en}:
      match origem:
        case L.Ambos{igual, nao_fatal}:
          %Equal.sym(Erros.Erro, e, Erros.Falha{}, igual) :
            I.RespostaJustificada(S.resposta_erro(Erros.status(_)), Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, Nat.add(Q.tamanho(antes), 0n))
          (etapa, id, fatal, quadro_causal_do_prefixo(fonte, c, mundo, s, rx, antes, depois,
            Nat.add(Q.tamanho(Con{Q.Configurada{}, H.render_fase(m, fase)}), 0n), Q.Falhou{etapa, id, fatal}, canonico, traco,
            (%Equal.sym(List<&2, Q.Quadro>, antes, Con{Q.Configurada{}, Fechos.antes_falha(m, fase, etapa, id, fatal)}, prefixo) :
              {Q.consultar(_, Nat.add(Q.tamanho(Con{Q.Configurada{}, H.render_fase(m, fase)}), 0n)) == Some{Q.Falhou{etapa, id, fatal}} : Maybe<&2, Q.Quadro>}
              Adm.consulta_da_marca(Con{Q.Configurada{}, H.render_fase(m, fase)}, Q.Falhou{etapa, id, fatal})), {==}, Unit{}))
    case H.InicialOk{}: match origem:
    case H.InicialRecusa{status}: match origem:
    case H.InicialFalha{aceita, etapa, id, fatal}: match origem:
    case H.SemResposta{}: match origem:
    case H.Executada{req, ctx, xs, p, en}: match origem:
    case H.FatalAposPublicacao{req, ctx, xs, p, etapa, id}: match origem:
    case H.Pendente{fase}: match origem:
    case H.InicialPendente{aceita}: match origem:

def artefato_fixo_tem_status_de_erro(e: Erros.Erro) -> Preparacao.Erro(Erros.status(e)):
  match e:
    case Erros.Entrada{}: Unit{}
    case Erros.Autenticacao{}: Unit{}
    case Erros.Certificado{}: Unit{}
    case Erros.Dados{}: Unit{}
    case Erros.Limite{}: Unit{}
    case Erros.Falha{}: Unit{}

def octetos_do_estado_copiado(~c: S.Configuracao, +s: D.Estado, +be: List<&2, U32>, estado: Causas.EstadoCopiado(c, s, be)) ->
  {B.octetos_validos(be) == True{} : Bool}:
  match estado:
    case (ce, te, L.Ambos{codigo, resto}): Octetos.qualquer_codificacao_so_emite_octetos(D.estado_valor(s), be, codigo)

def ConteudoFixo(~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao, +caso: H.Caso) -> Type:
  L.E<EntradaDoCaso(c, mundo, s, rx, caso), Fonte.PedidoDoCaso(c, Fonte.Atendimento{mundo, s, rx}, caso)>

def conteudo_fixo_sem_entrada(~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao,
  +be: List<&2, U32>, +dados: H.DadosFerramentas, +caso: H.Caso,
  nao: {eh_entrada(caso) == False{} : Bool}, selecionado: {caso == H.decidir(c, rx, be, dados) : H.Caso},
  estado: Causas.EstadoCopiado(c, s, be), octetos_r: Dois.OctetosRecebidos(X.decidir_recepcao(c, rx))) -> ConteudoFixo(c, mundo, s, rx, caso):
  L.Ambos{sem_entrada_tem_causa(c, mundo, s, rx, caso, nao),
    (%Equal.sym(H.Caso, caso, H.decidir(c, rx, be, dados), selecionado) : Fonte.PedidoDoCaso(c, Fonte.Atendimento{mundo, s, rx}, _)
      Dois.pedidos_da_decisao(c, mundo, s, rx, be, dados, octetos_do_estado_copiado(c, s, be, estado), octetos_r))}

def conteudo_fixo_da_decisao(~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao,
  +be: List<&2, U32>, +dados: H.DadosFerramentas, +caso: H.Caso,
  selecionado: {caso == H.decidir(c, rx, be, dados) : H.Caso},
  estado: Causas.EstadoCopiado(c, s, be), corpo: Causas.CorpoCopiado(c, rx),
  octetos_r: Dois.OctetosRecebidos(X.decidir_recepcao(c, rx)), estrutura: {D.estrutura(S.esquema(c), s) == True{} : Bool}) ->
  ConteudoFixo(c, mundo, s, rx, caso):
  match caso:
    case H.EntradaRecusa{+e, +fecha, +en}:
      L.Ambos{(%Equal.sym(H.Caso, H.EntradaRecusa{e, fecha, en}, H.decidir(c, rx, be, dados), selecionado) : EntradaDoCaso(c, mundo, s, rx, _)
        entrada_da_decisao_tem_causa_original(c, mundo, s, rx, be, dados, estado, corpo, octetos_r, estrutura)), Unit{}}
    case H.AutRecusa{+req, +en}: conteudo_fixo_sem_entrada(c, mundo, s, rx, be, dados, H.AutRecusa{req, en}, {==}, selecionado, estado, octetos_r)
    case H.GateRecusa{+req, +ctx, +en}: conteudo_fixo_sem_entrada(c, mundo, s, rx, be, dados, H.GateRecusa{req, ctx, en}, {==}, selecionado, estado, octetos_r)
    case H.Executada{+req, +ctx, +xs, +p, +en}: conteudo_fixo_sem_entrada(c, mundo, s, rx, be, dados, H.Executada{req, ctx, xs, p, en}, {==}, selecionado, estado, octetos_r)
    case H.FalhaAntes{+fase, +etapa, +id, +fatal, +en}: conteudo_fixo_sem_entrada(c, mundo, s, rx, be, dados, H.FalhaAntes{fase, etapa, id, fatal, en}, {==}, selecionado, estado, octetos_r)
    case H.InicialOk{}: conteudo_fixo_sem_entrada(c, mundo, s, rx, be, dados, H.InicialOk{}, {==}, selecionado, estado, octetos_r)
    case H.InicialRecusa{+status}: conteudo_fixo_sem_entrada(c, mundo, s, rx, be, dados, H.InicialRecusa{status}, {==}, selecionado, estado, octetos_r)
    case H.InicialFalha{+aceita, +etapa, +id, +fatal}: conteudo_fixo_sem_entrada(c, mundo, s, rx, be, dados, H.InicialFalha{aceita, etapa, id, fatal}, {==}, selecionado, estado, octetos_r)
    case H.SemResposta{}: conteudo_fixo_sem_entrada(c, mundo, s, rx, be, dados, H.SemResposta{}, {==}, selecionado, estado, octetos_r)
    case H.FatalAposPublicacao{+req, +ctx, +xs, +p, +etapa, +id}: conteudo_fixo_sem_entrada(c, mundo, s, rx, be, dados, H.FatalAposPublicacao{req, ctx, xs, p, etapa, id}, {==}, selecionado, estado, octetos_r)
    case H.Pendente{+fase}: conteudo_fixo_sem_entrada(c, mundo, s, rx, be, dados, H.Pendente{fase}, {==}, selecionado, estado, octetos_r)
    case H.InicialPendente{+aceita}: conteudo_fixo_sem_entrada(c, mundo, s, rx, be, dados, H.InicialPendente{aceita}, {==}, selecionado, estado, octetos_r)

def preparo_fixo_da_fonte(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao,
  +m: H.Micro, +antes: List<&2, Q.Quadro>, +depois: List<&2, Q.Quadro>, +e: Erros.Erro, +caso: H.Caso,
  canonico: {I.Atender{mundo, c, s, rx} == Fonte.cenario(fonte, mundo) : I.Cenario},
  traco: {Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)) == Q.concatenar(antes, Con{Fechos.marco_preparo(Fechos.Fixo{e}), depois}) : List<&2, Q.Quadro>},
  valida: {R.configuracao_valida(c) == True{} : Bool},
  origem: Fechos.FixoDoCaso(e, caso), prefixo: Fechos.PrefixoFixo(m, caso, antes), conteudo: ConteudoFixo(c, mundo, s, rx, caso)) ->
  K.Regra7(fato_preparo(Fechos.marco_preparo(Fechos.Fixo{e})), Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, Nat.add(Q.tamanho(antes), 0n)):
  F.com_par(K.Regra7(fato_preparo(Fechos.marco_preparo(Fechos.Fixo{e})), Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, Nat.add(Q.tamanho(antes), 0n)),
    EntradaDoCaso(c, mundo, s, rx, caso), Fonte.PedidoDoCaso(c, Fonte.Atendimento{mundo, s, rx}, caso), conteudo,
    entrada => pedido => preparo_fixo_com_causa_real_obedece_regra7(c, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, Nat.add(Q.tamanho(antes), 0n),
      Erros.status(e), Erros.bytes(e), {==}, valida, artefato_fixo_tem_status_de_erro(e), Erros.todos_os_erros_preparados_sao_exatamente_mensagens_originais(e),
      causa_fixa_do_caso(fonte, c, mundo, s, rx, m, antes, Con{Fechos.marco_preparo(Fechos.Fixo{e}), depois}, e, caso, canonico, traco, origem, prefixo, entrada, pedido)))

def marca_canonica_no_traco(+qs: List<&2, Q.Quadro>, +antes: List<&2, Q.Quadro>, +depois: List<&2, Q.Quadro>,
  +r: S.Resposta, +bs: List<&2, U32>, +origem: Fechos.OrigemPreparo,
  traco: {qs == Q.concatenar(antes, Con{Q.Preparada{r, bs}, depois}) : List<&2, Q.Quadro>},
  quadro: {Q.Preparada{r, bs} == Fechos.marco_preparo(origem) : Q.Quadro}) ->
  {qs == Q.concatenar(antes, Con{Fechos.marco_preparo(origem), depois}) : List<&2, Q.Quadro>}:
  Equal.trans(List<&2, Q.Quadro>, qs, Q.concatenar(antes, Con{Q.Preparada{r, bs}, depois}), Q.concatenar(antes, Con{Fechos.marco_preparo(origem), depois}), traco,
    Equal.cong(Q.Quadro, List<&2, Q.Quadro>, q => Q.concatenar(antes, Con{q, depois}), Q.Preparada{r, bs}, Fechos.marco_preparo(origem), quadro))

def consumir_origem_de_preparo(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +inicial: D.Estado, +rx: X.Recepcao,
  +m: H.Micro, +codigo: Fonte.JuizoSintatico, +caso: H.Caso, +t: Nat, +r: S.Resposta, +bs: List<&2, U32>,
  canonico: {I.Atender{mundo, c, inicial, rx} == Fonte.cenario(fonte, mundo) : I.Cenario},
  valida: {R.configuracao_valida(c) == True{} : Bool},
  mesma_raiz: {Fonte.programa(fonte, codigo) == Lei5.programa_do_mundo(fonte, mundo) : S.Programa},
  conteudo: ConteudoFixo(c, mundo, inicial, rx, caso),
  preparo: Fechos.PreparoNoTraco(fonte, c, m, inicial, codigo, caso, Vis.quadros_chamada(c, inicial, rx, Fonte.chamada(fonte, mundo)), t, r, bs)) ->
  K.Regra7(I.Preparou{r, bs}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, t):
  match preparo:
    case (+antes, +depois, Fechos.Nativo{+req, +ctx, +xs, N.Preparada{+w, +ts, +rp, +bytes}}, L.Ambos{traco, L.Ambos{pos, L.Ambos{+quadro, L.Ambos{prefixo, real}}}}):
      transportar_preparo7(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, antes, t, r, bs, Q.Preparada{rp, bytes}, pos, quadro,
        preparo_nativo_da_fonte(fonte, c, mundo, inicial, rx, m, antes, depois, req, ctx, codigo, xs, N.Preparada{w, ts, rp, bytes}, canonico,
          marca_canonica_no_traco(Vis.quadros_chamada(c, inicial, rx, Fonte.chamada(fonte, mundo)), antes, depois, r, bs, Fechos.Nativo{req, ctx, xs, N.Preparada{w, ts, rp, bytes}}, traco, quadro), prefixo, real, valida, mesma_raiz))
    case (+antes, +depois, Fechos.Fixo{+e}, L.Ambos{traco, L.Ambos{pos, L.Ambos{+quadro, L.Ambos{origem, prefixo}}}}):
      transportar_preparo7(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, inicial, rx}, antes, t, r, bs, Fechos.marco_preparo(Fechos.Fixo{e}), pos, quadro,
        preparo_fixo_da_fonte(fonte, c, mundo, inicial, rx, m, antes, depois, e, caso, canonico,
          marca_canonica_no_traco(Vis.quadros_chamada(c, inicial, rx, Fonte.chamada(fonte, mundo)), antes, depois, r, bs, Fechos.Fixo{e}, traco, quadro), valida, origem, prefixo, conteudo))

def EstadoDaChamada(~c: S.Configuracao, +s: D.Estado, dados: Fonte.ChamadaData) -> Type:
  match dados:
    case Fonte.ChamadaData{cf, pf, cert, termina, be, ferramentas, micro}: Causas.EstadoCopiado(c, s, be)

def preparo_dos_dados_da_fonte(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao,
  +dados: Fonte.ChamadaData, +t: Nat, +r: S.Resposta, +bs: List<&2, U32>,
  canonico: {I.Atender{mundo, c, s, rx} == Fonte.cenario(fonte, mundo) : I.Cenario},
  +mesma: {dados == Fonte.chamada(fonte, mundo) : Fonte.ChamadaData},
  real: Lei5.ChamadaReal(fonte, c, s, rx, dados), estado: EstadoDaChamada(c, s, dados), corpo: Causas.CorpoCopiado(c, rx),
  octetos_r: Dois.OctetosRecebidos(X.decidir_recepcao(c, rx)), estrutura: {D.estrutura(S.esquema(c), s) == True{} : Bool},
  valida: {R.configuracao_valida(c) == True{} : Bool},
  observado: Fonte.de_observacao(fonte, c, Fonte.construir_chamada(c, s, rx, dados), t, I.Preparou{r, bs})) ->
  K.Regra7(I.Preparou{r, bs}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t):
  match dados:
    case Fonte.ChamadaData{+cf, +codigo, +cert, +termina, +be, +ferramentas, +micro}:
      consumir_origem_de_preparo(fonte, c, mundo, s, rx, micro, codigo, H.decidir(c, rx, be, ferramentas), t, r, bs,
        canonico, valida, Lei5.mesma_raiz_da_chamada(fonte, mundo, Fonte.ChamadaData{cf, codigo, cert, termina, be, ferramentas, micro}, mesma),
        conteudo_fixo_da_decisao(c, mundo, s, rx, be, ferramentas, H.decidir(c, rx, be, ferramentas), {==}, estado, corpo, octetos_r, estrutura),
        (%Equal.cong(Fonte.ChamadaData, List<&2, Q.Quadro>, d => Vis.quadros_chamada(c, s, rx, d),
          Fonte.ChamadaData{cf, codigo, cert, termina, be, ferramentas, micro}, Fonte.chamada(fonte, mundo), mesma) :
            Fechos.PreparoNoTraco(fonte, c, micro, s, codigo, H.decidir(c, rx, be, ferramentas), _, t, r, bs)
          Fechos.inverter_preparo(fonte, c, micro, s, codigo, H.decidir(c, rx, be, ferramentas), t, r, bs,
            Lei5.execucao_da_decisao(fonte, c, s, codigo, be, ferramentas, rx, real),
            Q.observacao_quadro(c, Fonte.programa(fonte, codigo), H.gerar(c, rx, be, s, ferramentas, micro), t, I.Preparou{r, bs}, observado))))

law preparo_da_fonte_obedece_regra7:
  for ~fonte: Fonte.Fonte
  for ~c: S.Configuracao
  for +mundo: Nat
  for +s: D.Estado
  for +rx: X.Recepcao
  for +t: Nat
  for +r: S.Resposta
  for +bs: List<&2, U32>
  for real: Lei5.ChamadaReal(fonte, c, s, rx, Fonte.chamada(fonte, mundo))
  for estado: EstadoDaChamada(c, s, Fonte.chamada(fonte, mundo))
  for corpo: Causas.CorpoCopiado(c, rx)
  for octetos_r: Dois.OctetosRecebidos(X.decidir_recepcao(c, rx))
  for estrutura: {D.estrutura(S.esquema(c), s) == True{} : Bool}
  for valida: {R.configuracao_valida(c) == True{} : Bool}
  for observado: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t, I.Preparou{r, bs})
  K.Regra7(I.Preparou{r, bs}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t)
def preparo_da_fonte_obedece_regra7(fonte, c, mundo, s, rx, t, r, bs, real, estado, corpo, octetos_r, estrutura, valida, observado):
  F.com_par(K.Regra7(I.Preparou{r, bs}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t),
    {Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
    L.E<{I.Atender{mundo, c, s, rx} == Fonte.cenario(fonte, mundo) : I.Cenario}, Fonte.da_rota(fonte, I.Atender{mundo, c, s, rx}, t, I.Preparou{r, bs})>,
    Fonte.eliminar_fato_literal(fonte, Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t, I.Preparou{r, bs}, observado),
    nome => origem => F.com_par(K.Regra7(I.Preparou{r, bs}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t),
      {I.Atender{mundo, c, s, rx} == Fonte.cenario(fonte, mundo) : I.Cenario}, Fonte.da_rota(fonte, I.Atender{mundo, c, s, rx}, t, I.Preparou{r, bs}), origem,
      canonico => obs => preparo_dos_dados_da_fonte(fonte, c, mundo, s, rx, Fonte.chamada(fonte, mundo), t, r, bs, canonico, {==}, real, estado, corpo, octetos_r, estrutura, valida, obs)))
