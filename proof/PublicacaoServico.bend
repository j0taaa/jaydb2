# Publicacao deriva da execucao e do certificado reais; o pos-estado valido
# e uma conclusao, nao um campo da origem fornecida pelo ambiente.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Interface.bend as I
import ../contrato/LAWS.bend as K
import ../contrato/Logica.bend as L
import ../contrato/Protocolo.bend as P
import ../contrato/Requisitos.bend as Req
import ../contrato/Recursos.bend as X
import ../contrato/Semantica.bend as S
import ../src/Nucleo.bend as N
import ../src/Configuracao.bend as Config
import ./FonteServico.bend as Fonte
import ./ProtocoloServico.bend as Q
import ./RotasServico.bend as R
import ./FasesServico.bend as Fases
import ./ConclusaoServico.bend as Conclusao
import ./HistoricoServico.bend as Historico
import ./Fundamentos.bend as F
import ./Lei5Servico.bend as Cinco
import ./Lei34Servico.bend as Adm
import ./Preparacao.bend as Preparacao
import ./LigacaoServico.bend as Ligacao
import ./VisibilidadeServico.bend as Vis
import ./ExecucaoServico.bend as Exec
import ./CenariosServico.bend as Cenarios

# O sufixo pode ser entrega normal OU falha fatal apos o store.
def traco(+antes: List<&2, Q.Quadro>, +w: D.Estado, +v: D.Valor, +bs: List<&2, U32>, depois: List<&2, Q.Quadro>) -> List<&2, Q.Quadro>:
  Q.concatenar(antes, Con{Q.Preparada{S.Resposta{S.Sucesso{}, v}, bs}, Con{Q.Publicada{w}, depois}})

def no_par(+w: D.Estado, +v: D.Valor, +bs: List<&2, U32>, u: Nat, +publicado: D.Estado,
  consulta: {Q.consultar([Q.Preparada{S.Resposta{S.Sucesso{}, v}, bs}, Q.Publicada{w}], u) == Some{Q.Publicada{publicado}} : Maybe<&2, Q.Quadro>}) -> L.E<{u == 1n : Nat}, {publicado == w : D.Estado}>:
  match u:
    case 0n: L.ex_falso(L.E<{0n == 1n : Nat}, {publicado == w : D.Estado}>, Fases.ausente_exclui_consulta(Fases.Publicacao{}, [Q.Preparada{S.Resposta{S.Sucesso{}, v}, bs}], 0n, Q.Publicada{publicado}, {==}, {==}, consulta))
    case 1n: L.Ambos{{==}, Fases.publicadas_iguais(w, publicado, consulta)}
    case 2n+k: L.ex_falso(L.E<{2n+k == 1n : Nat}, {publicado == w : D.Estado}>, F.nenhum_nao_algum(Q.Quadro, Q.Publicada{publicado}, consulta))

def na_parte(+antes: List<&2, Q.Quadro>, +w: D.Estado, +v: D.Valor, +bs: List<&2, U32>, +depois: List<&2, Q.Quadro>, -t: Nat, +publicado: D.Estado,
  sem_depois: {Fases.ausente(Fases.Publicacao{}, depois) == True{} : Bool},
  parte: &u: Nat -> L.E<{t == Nat.add(Q.tamanho(antes), u) : Nat}, {Q.consultar(Con{Q.Preparada{S.Resposta{S.Sucesso{}, v}, bs}, Con{Q.Publicada{w}, depois}}, u) == Some{Q.Publicada{publicado}} : Maybe<&2, Q.Quadro>}>) ->
  L.E<{t == Nat.add(Q.tamanho(antes), 1n) : Nat}, {publicado == w : D.Estado}>:
  match parte:
    case (+u, L.Ambos{posicao, consulta}):
      F.com_par(L.E<{t == Nat.add(Q.tamanho(antes), 1n) : Nat}, {publicado == w : D.Estado}>, {u == 1n : Nat}, {publicado == w : D.Estado},
        no_par(w, v, bs, u, publicado, Cinco.retirar_sufixo_sem_quadro([Q.Preparada{S.Resposta{S.Sucesso{}, v}, bs}, Q.Publicada{w}], depois, u, Q.Publicada{publicado},
          i => outra => Fases.ausente_exclui_consulta(Fases.Publicacao{}, depois, i, Q.Publicada{publicado}, sem_depois, {==}, outra), consulta)),
        local => estado => L.Ambos{Equal.trans(Nat, t, Nat.add(Q.tamanho(antes), u), Nat.add(Q.tamanho(antes), 1n), posicao, Equal.cong(Nat, Nat, x => Nat.add(Q.tamanho(antes), x), u, 1n, local)), estado})

law publicacao_no_frame_e_unica:
  for +antes: List<&2, Q.Quadro>
  for +w: D.Estado
  for +v: D.Valor
  for +bs: List<&2, U32>
  for +depois: List<&2, Q.Quadro>
  for +t: Nat
  for +publicado: D.Estado
  for sem_antes: {Fases.ausente(Fases.Publicacao{}, antes) == True{} : Bool}
  for sem_depois: {Fases.ausente(Fases.Publicacao{}, depois) == True{} : Bool}
  for consulta: {Q.consultar(traco(antes, w, v, bs, depois), t) == Some{Q.Publicada{publicado}} : Maybe<&2, Q.Quadro>}
  L.E<{t == Nat.add(Q.tamanho(antes), 1n) : Nat}, {publicado == w : D.Estado}>
def publicacao_no_frame_e_unica(antes, w, v, bs, depois, t, publicado, sem_antes, sem_depois, consulta):
  na_parte(antes, w, v, bs, depois, t, publicado, sem_depois,
    Fases.localizar_no_sufixo(Fases.Publicacao{}, antes, Con{Q.Preparada{S.Resposta{S.Sucesso{}, v}, bs}, Con{Q.Publicada{w}, depois}}, t, Q.Publicada{publicado}, sem_antes, {==}, consulta))

# Todos os portos abaixo sao consultas/intros da mesma rota, demonstrados
# pela LigacaoServico. Nao recebem validade publicada ou Regra6.
def frame_canonico(~fonte: Fonte.Fonte, ~c: S.Configuracao, -a: I.Ambiente, -k: String, -x: I.Cenario,
  +antes: List<&2, Q.Quadro>, +s: D.Estado, +req: P.Requisicao, +ctx: D.Contexto, +origem: Fonte.JuizoSintatico,
  +n: Nat, +w: D.Estado, +ts: List<&2, S.Evento>, +proposta: S.Resposta, +v: D.Valor, +bs: List<&2, U32>, +depois: List<&2, Q.Quadro>,
  configuracao: {I.configuracao(x) == c : S.Configuracao}, inicial: {s == I.inicial(x) : D.Estado}, valido: Req.Valido(c, I.inicial(x)),
  verificada: Conclusao.OrigemDaFonte(fonte, c, s, origem, Historico.Registro{req, ctx, n, w, ts, proposta, N.Preparada{w, ts, S.Resposta{S.Sucesso{}, v}, bs}}),
  finalizada: {Req.finalizar(proposta, I.configuracao(x), w) == S.Resposta{S.Sucesso{}, v} : S.Resposta},
  indice: &i: Nat -> {Q.consultar(antes, i) == Some{Q.Avaliada{req, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>},
  sem_antes: {Fases.ausente(Fases.Publicacao{}, antes) == True{} : Bool}, sem_depois: {Fases.ausente(Fases.Publicacao{}, depois) == True{} : Bool},
  preparar: @u: Nat -> {Q.consultar(traco(antes, w, v, bs, depois), u) == Some{Q.Preparada{S.Resposta{S.Sucesso{}, v}, bs}} : Maybe<&2, Q.Quadro>} -> I.Acontece(a, k, x, u, I.Preparou{S.Resposta{S.Sucesso{}, v}, bs}),
  avaliar: @u: Nat -> {Q.consultar(traco(antes, w, v, bs, depois), u) == Some{Q.Avaliada{req, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>} -> I.Acontece(a, k, x, u, I.Avaliou{req, ctx, Fonte.programa(fonte, origem), S.Final{w, ts, proposta}}),
  publicar: @u: Nat -> @estado: D.Estado -> I.Acontece(a, k, x, u, I.Publicou{estado}) -> {Q.consultar(traco(antes, w, v, bs, depois), u) == Some{Q.Publicada{estado}} : Maybe<&2, Q.Quadro>}) ->
  K.Regra6(I.Publicou{w}, a, k, x, Nat.add(Q.tamanho(antes), 1n)):
  L.Ambos{(%Equal.sym(S.Configuracao, I.configuracao(x), c, configuracao) : Req.Valido(_, w)
      Historico.passo_preserva_validade(c, s, Historico.Registro{req, ctx, n, w, ts, proposta, N.Preparada{w, ts, S.Resposta{S.Sucesso{}, v}, bs}},
        (%Equal.sym(D.Estado, s, I.inicial(x), inicial) : Req.Valido(c, _) valido), Conclusao.historico_da_fonte(fonte, c, s, origem, Historico.Registro{req, ctx, n, w, ts, proposta, N.Preparada{w, ts, S.Resposta{S.Sucesso{}, v}, bs}}, verificada))),
    L.Ambos{(v, bs, L.Ambos{(Nat.add(Q.tamanho(antes), 0n), L.Ambos{Q.ordem_deslocada(Q.tamanho(antes), 0n, 1n, {==}), preparar(Nat.add(Q.tamanho(antes), 0n), Q.consultar_apos_prefixo(antes, Con{Q.Preparada{S.Resposta{S.Sucesso{}, v}, bs}, Con{Q.Publicada{w}, depois}}, 0n))}),
      Conclusao.resposta_final_tem_causa_na_avaliacao_real(fonte, a, k, x, antes, Con{Q.Preparada{S.Resposta{S.Sucesso{}, v}, bs}, Con{Q.Publicada{w}, depois}}, 1n, req, ctx, origem, w, ts, proposta, S.Resposta{S.Sucesso{}, v}, finalizada, indice, avaliar)}),
      +u => +estado => fato => publicacao_no_frame_e_unica(antes, w, v, bs, depois, u, estado, sem_antes, sem_depois, publicar(u, estado, fato))}}

def frame_refletido(~fonte: Fonte.Fonte, ~c: S.Configuracao, -a: I.Ambiente, -k: String, -x: I.Cenario,
  +antes: List<&2, Q.Quadro>, +s: D.Estado, +req: P.Requisicao, +ctx: D.Contexto, +origem: Fonte.JuizoSintatico,
  +n: Nat, +w: D.Estado, +ts: List<&2, S.Evento>, +proposta: S.Resposta, +v: D.Valor, +bs: List<&2, U32>, +depois: List<&2, Q.Quadro>, +t: Nat, +publicado: D.Estado,
  configuracao: {I.configuracao(x) == c : S.Configuracao}, inicial: {s == I.inicial(x) : D.Estado}, valido: Req.Valido(c, I.inicial(x)),
  verificada: Conclusao.OrigemDaFonte(fonte, c, s, origem, Historico.Registro{req, ctx, n, w, ts, proposta, N.Preparada{w, ts, S.Resposta{S.Sucesso{}, v}, bs}}),
  finalizada: {Req.finalizar(proposta, I.configuracao(x), w) == S.Resposta{S.Sucesso{}, v} : S.Resposta},
  indice: &i: Nat -> {Q.consultar(antes, i) == Some{Q.Avaliada{req, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>},
  sem_antes: {Fases.ausente(Fases.Publicacao{}, antes) == True{} : Bool}, sem_depois: {Fases.ausente(Fases.Publicacao{}, depois) == True{} : Bool},
  preparar: @u: Nat -> {Q.consultar(traco(antes, w, v, bs, depois), u) == Some{Q.Preparada{S.Resposta{S.Sucesso{}, v}, bs}} : Maybe<&2, Q.Quadro>} -> I.Acontece(a, k, x, u, I.Preparou{S.Resposta{S.Sucesso{}, v}, bs}),
  avaliar: @u: Nat -> {Q.consultar(traco(antes, w, v, bs, depois), u) == Some{Q.Avaliada{req, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>} -> I.Acontece(a, k, x, u, I.Avaliou{req, ctx, Fonte.programa(fonte, origem), S.Final{w, ts, proposta}}),
  publicar: @u: Nat -> @estado: D.Estado -> I.Acontece(a, k, x, u, I.Publicou{estado}) -> {Q.consultar(traco(antes, w, v, bs, depois), u) == Some{Q.Publicada{estado}} : Maybe<&2, Q.Quadro>},
  consulta: {Q.consultar(traco(antes, w, v, bs, depois), t) == Some{Q.Publicada{publicado}} : Maybe<&2, Q.Quadro>}) -> K.Regra6(I.Publicou{publicado}, a, k, x, t):
  F.com_par(K.Regra6(I.Publicou{publicado}, a, k, x, t), {Fases.ausente(Fases.Publicacao{}, antes) == True{} : Bool}, {Fases.ausente(Fases.Publicacao{}, antes) == True{} : Bool},
    Q.igualdade_reabrivel(Bool, Fases.ausente(Fases.Publicacao{}, antes), True{}, sem_antes), antes_atual => antes_todas =>
      F.com_par(K.Regra6(I.Publicou{publicado}, a, k, x, t), {Fases.ausente(Fases.Publicacao{}, depois) == True{} : Bool}, {Fases.ausente(Fases.Publicacao{}, depois) == True{} : Bool},
        Q.igualdade_reabrivel(Bool, Fases.ausente(Fases.Publicacao{}, depois), True{}, sem_depois), depois_atual => depois_todas =>
          Conclusao.transportar_publicacao6(a, k, x, antes, w, t, publicado,
            publicacao_no_frame_e_unica(antes, w, v, bs, depois, t, publicado, antes_atual, depois_atual, consulta),
            frame_canonico(fonte, c, a, k, x, antes, s, req, ctx, origem, n, w, ts, proposta, v, bs, depois,
              configuracao, inicial, valido, verificada, finalizada, indice, antes_todas, depois_todas, preparar, avaliar, publicar))))

# Prefixo real comum ao sucesso e a falha apos o store.
def antes(+m: R.Micro, +req: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>) -> List<&2, Q.Quadro>:
  Con{Q.Configurada{}, Q.concatenar(R.render_execucao(m, req, ctx, xs), R.micro_saida(m))}

def antes_sem_publicacao(+m: R.Micro, +req: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>) -> {Fases.ausente(Fases.Publicacao{}, antes(m, req, ctx, xs)) == True{} : Bool}:
  Fases.concatenar_ausencia(Fases.Publicacao{}, R.render_execucao(m, req, ctx, xs), R.micro_saida(m), Fases.execucao_host_sem_macros(Fases.Publicacao{}, m, req, ctx, xs), Fases.micro_saida_sem_macros(Fases.Publicacao{}, m))

def indice_no_prefixo(+m: R.Micro, +req: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>, +w: D.Estado, +ts: List<&2, S.Evento>, +proposta: S.Resposta,
  indice: &i: Nat -> {Exec.consultar(xs, i) == Some{Q.Avaliacao{S.Final{w, ts, proposta}}} : Maybe<&2, Q.QuadroExec>}) ->
  &u: Nat -> {Q.consultar(antes(m, req, ctx, xs), u) == Some{Q.Avaliada{req, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>}:
  match indice:
    case (+i, consulta): (Nat.add(Q.tamanho(Con{Q.Configurada{}, R.render_comecada(m, req, ctx)}), i),
      Adm.consulta_prefixo(Con{Q.Configurada{}, R.render_execucao(m, req, ctx, xs)}, R.micro_saida(m), Nat.add(Q.tamanho(Con{Q.Configurada{}, R.render_comecada(m, req, ctx)}), i), Q.Avaliada{req, ctx, S.Final{w, ts, proposta}},
        Equal.trans(Maybe<&2, Q.Quadro>, Q.consultar(Con{Q.Configurada{}, R.render_execucao(m, req, ctx, xs)}, Nat.add(Q.tamanho(Con{Q.Configurada{}, R.render_comecada(m, req, ctx)}), i)), Q.consultar(Q.expandir_exec(req, ctx, xs), i), Some{Q.Avaliada{req, ctx, S.Final{w, ts, proposta}}},
          Q.consultar_apos_prefixo(Con{Q.Configurada{}, R.render_comecada(m, req, ctx)}, Q.expandir_exec(req, ctx, xs), i), Exec.expandir_preserva_consulta(req, ctx, xs, i, Q.Avaliacao{S.Final{w, ts, proposta}}, consulta))))

# Extrai somente o certificado checado; nao o transforma em Valido do resultado.
def certificado_da_fonte(~fonte: Fonte.Fonte, -c: S.Configuracao, -req: P.Requisicao, -ctx: D.Contexto, +origem: Fonte.JuizoSintatico,
  fonte_aceita: Fonte.JuizoAceito(fonte, c, req, ctx, origem)) -> Req.Certifica(c, I.codigo(req), Fonte.programa(fonte, origem), ctx, I.argumentos(req)):
  match fonte_aceita:
    case L.Ambos{elabora, L.Ambos{deriva, L.Ambos{certificado, resto}}}: certificado

# Portos de consulta do mesmo trace. Sao construidos por igualdade de listas
# e pela LigacaoServico, nao assumidos como comportamento do controlador.
def Prepara(~fonte: Fonte.Fonte, ~c: S.Configuracao, -mundo: Nat, -s: D.Estado, -rx: X.Recepcao, -qs: List<&2, Q.Quadro>) -> Type:
  @u: Nat -> @r: S.Resposta -> @bs: List<&2, U32> -> {Q.consultar(qs, u) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>} -> I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, u, I.Preparou{r, bs})
def Avalia(~fonte: Fonte.Fonte, ~c: S.Configuracao, -mundo: Nat, -s: D.Estado, -rx: X.Recepcao, +origem: Fonte.JuizoSintatico, -req: P.Requisicao, -ctx: D.Contexto, -qs: List<&2, Q.Quadro>) -> Type:
  @u: Nat -> @p: S.Percurso -> {Q.consultar(qs, u) == Some{Q.Avaliada{req, ctx, p}} : Maybe<&2, Q.Quadro>} -> I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, u, I.Avaliou{req, ctx, Fonte.programa(fonte, origem), p})
def Extrai(~fonte: Fonte.Fonte, ~c: S.Configuracao, -mundo: Nat, -s: D.Estado, -rx: X.Recepcao, -qs: List<&2, Q.Quadro>) -> Type:
  @u: Nat -> @w: D.Estado -> I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, u, I.Publicou{w}) -> {Q.consultar(qs, u) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>}
def Portos(~fonte: Fonte.Fonte, ~c: S.Configuracao, -mundo: Nat, -s: D.Estado, -rx: X.Recepcao, +origem: Fonte.JuizoSintatico, -req: P.Requisicao, -ctx: D.Contexto, -qs: List<&2, Q.Quadro>) -> Type:
  L.E<Prepara(fonte, c, mundo, s, rx, qs), L.E<Avalia(fonte, c, mundo, s, rx, origem, req, ctx, qs), Extrai(fonte, c, mundo, s, rx, qs)>>

def preparar_na_fonte(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao, +qs: List<&2, Q.Quadro>, +u: Nat, +r: S.Resposta, +bs: List<&2, U32>,
  canonico: {I.Atender{mundo, c, s, rx} == Fonte.cenario(fonte, mundo) : I.Cenario},
  trace: {Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)) == qs : List<&2, Q.Quadro>}, consulta: {Q.consultar(qs, u) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>}) ->
  I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, u, I.Preparou{r, bs}):
  Ligacao.introduzir_quadro(fonte, c, mundo, s, rx, u, Q.Preparada{r, bs}, I.Preparou{r, bs}, canonico,
    (%Equal.sym(List<&2, Q.Quadro>, Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)), qs, trace) : {Q.consultar(_, u) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>} consulta), {==}, Unit{})

def avaliar_na_fonte(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao, +origem: Fonte.JuizoSintatico, +req: P.Requisicao, +ctx: D.Contexto,
  +qs: List<&2, Q.Quadro>, +u: Nat, +percurso: S.Percurso, canonico: {I.Atender{mundo, c, s, rx} == Fonte.cenario(fonte, mundo) : I.Cenario},
  trace: {Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)) == qs : List<&2, Q.Quadro>}, raiz: {Fonte.programa(fonte, origem) == Cinco.programa_do_mundo(fonte, mundo) : S.Programa},
  consulta: {Q.consultar(qs, u) == Some{Q.Avaliada{req, ctx, percurso}} : Maybe<&2, Q.Quadro>}) -> I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, u, I.Avaliou{req, ctx, Fonte.programa(fonte, origem), percurso}):
  Ligacao.introduzir_quadro(fonte, c, mundo, s, rx, u, Q.Avaliada{req, ctx, percurso}, I.Avaliou{req, ctx, Fonte.programa(fonte, origem), percurso}, canonico,
    (%Equal.sym(List<&2, Q.Quadro>, Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)), qs, trace) : {Q.consultar(_, u) == Some{Q.Avaliada{req, ctx, percurso}} : Maybe<&2, Q.Quadro>} consulta),
    (%raiz : Q.rel_fato(c, _, Q.Avaliada{req, ctx, percurso}, I.Avaliou{req, ctx, Fonte.programa(fonte, origem), percurso}) {==}), Unit{})

def extrair_da_fonte(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao, +qs: List<&2, Q.Quadro>, +u: Nat, +w: D.Estado,
  trace: {Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)) == qs : List<&2, Q.Quadro>}, fato: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, u, I.Publicou{w})) -> {Q.consultar(qs, u) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>}:
  %trace : {Q.consultar(_, u) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>}
  Ligacao.extrair_quadro(fonte, c, mundo, s, rx, u, I.Publicou{w}, Unit{}, fato)

def portos_da_fonte(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao, +origem: Fonte.JuizoSintatico, +req: P.Requisicao, +ctx: D.Contexto, +qs: List<&2, Q.Quadro>,
  canonico: {I.Atender{mundo, c, s, rx} == Fonte.cenario(fonte, mundo) : I.Cenario},
  trace: {Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)) == qs : List<&2, Q.Quadro>}, raiz: {Fonte.programa(fonte, origem) == Cinco.programa_do_mundo(fonte, mundo) : S.Programa}) -> Portos(fonte, c, mundo, s, rx, origem, req, ctx, qs):
  F.com_par(Portos(fonte, c, mundo, s, rx, origem, req, ctx, qs), {I.Atender{mundo, c, s, rx} == Fonte.cenario(fonte, mundo) : I.Cenario}, {I.Atender{mundo, c, s, rx} == Fonte.cenario(fonte, mundo) : I.Cenario},
    Q.igualdade_reabrivel(I.Cenario, I.Atender{mundo, c, s, rx}, Fonte.cenario(fonte, mundo), canonico), c_pre => c_aval =>
      F.com_par(Portos(fonte, c, mundo, s, rx, origem, req, ctx, qs), {Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)) == qs : List<&2, Q.Quadro>}, {Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)) == qs : List<&2, Q.Quadro>},
        Q.igualdade_reabrivel(List<&2, Q.Quadro>, Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)), qs, trace), para_intros => para_extrair =>
          F.com_par(Portos(fonte, c, mundo, s, rx, origem, req, ctx, qs), {Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)) == qs : List<&2, Q.Quadro>}, {Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)) == qs : List<&2, Q.Quadro>},
            Q.igualdade_reabrivel(List<&2, Q.Quadro>, Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)), qs, para_intros), para_preparo => para_avaliar =>
              L.Ambos{+u => +r => +bs => consulta => preparar_na_fonte(fonte, c, mundo, s, rx, qs, u, r, bs, c_pre, para_preparo, consulta),
                L.Ambos{+u => +percurso => consulta => avaliar_na_fonte(fonte, c, mundo, s, rx, origem, req, ctx, qs, u, percurso, c_aval, para_avaliar, raiz, consulta),
                  +u => +w => fato => extrair_da_fonte(fonte, c, mundo, s, rx, qs, u, w, para_extrair, fato)}})))

def fim(conclusao: N.Conclusao, depois: List<&2, Q.Quadro>) -> List<&2, Q.Quadro>:
  match conclusao:
    case N.Conclusao{+w, +r, bs}: Con{Q.Preparada{r, bs}, Q.concatenar(R.render_publicacao(r, w), depois)}
def quadro_final(+m: R.Micro, +req: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>, +p: N.Preparada, +s: D.Estado, depois: List<&2, Q.Quadro>) -> List<&2, Q.Quadro>:
  Q.concatenar(antes(m, req, ctx, xs), fim(N.concluir(p, s), depois))

def sucesso_com_portos(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao,
  +m: R.Micro, +req: P.Requisicao, +ctx: D.Contexto, +origem: Fonte.JuizoSintatico, +xs: List<&2, Q.QuadroExec>, +n: Nat,
  +w: D.Estado, +ts: List<&2, S.Evento>, +proposta: S.Resposta, +v: D.Valor, +bs: List<&2, U32>, +depois: List<&2, Q.Quadro>, +t: Nat, +publicado: D.Estado,
  valido: Req.Valido(c, s), verificada: Conclusao.OrigemDaFonte(fonte, c, s, origem, Historico.Registro{req, ctx, n, w, ts, proposta, N.Preparada{w, ts, S.Resposta{S.Sucesso{}, v}, bs}}),
  finalizada: {Req.finalizar(proposta, c, w) == S.Resposta{S.Sucesso{}, v} : S.Resposta},
  indice: &i: Nat -> {Q.consultar(antes(m, req, ctx, xs), i) == Some{Q.Avaliada{req, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>},
  sem_depois: {Fases.ausente(Fases.Publicacao{}, depois) == True{} : Bool},
  portos: Portos(fonte, c, mundo, s, rx, origem, req, ctx, traco(antes(m, req, ctx, xs), w, v, bs, depois)),
  consulta: {Q.consultar(traco(antes(m, req, ctx, xs), w, v, bs, depois), t) == Some{Q.Publicada{publicado}} : Maybe<&2, Q.Quadro>}) ->
  K.Regra6(I.Publicou{publicado}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t):
  match portos:
    case L.Ambos{preparar, L.Ambos{avaliar, publicar}}:
      frame_refletido(fonte, c, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, antes(m, req, ctx, xs), s, req, ctx, origem, n, w, ts, proposta, v, bs, depois, t, publicado,
        {==}, {==}, valido, verificada, finalizada, indice, antes_sem_publicacao(m, req, ctx, xs), sem_depois,
        +u => h => preparar(u, S.Resposta{S.Sucesso{}, v}, bs, h),
        +u => h => avaliar(u, S.Final{w, ts, proposta}, h), publicar, consulta)

def resposta_do_resultado(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao,
  +m: R.Micro, +req: P.Requisicao, +ctx: D.Contexto, +origem: Fonte.JuizoSintatico, +xs: List<&2, Q.QuadroExec>, +n: Nat,
  +w: D.Estado, +ts: List<&2, S.Evento>, +proposta: S.Resposta, r: S.Resposta, +bs: List<&2, U32>, +depois: List<&2, Q.Quadro>, +t: Nat, +publicado: D.Estado,
  valido: Req.Valido(c, s), verificada: Conclusao.OrigemDaFonte(fonte, c, s, origem, Historico.Registro{req, ctx, n, w, ts, proposta, N.Preparada{w, ts, r, bs}}),
  finalizada: {Req.finalizar(proposta, c, w) == r : S.Resposta},
  indice: &i: Nat -> {Q.consultar(antes(m, req, ctx, xs), i) == Some{Q.Avaliada{req, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>},
  sem_depois: {Fases.ausente(Fases.Publicacao{}, depois) == True{} : Bool},
  portos: Portos(fonte, c, mundo, s, rx, origem, req, ctx, quadro_final(m, req, ctx, xs, N.Preparada{w, ts, r, bs}, s, depois)),
  consulta: {Q.consultar(quadro_final(m, req, ctx, xs, N.Preparada{w, ts, r, bs}, s, depois), t) == Some{Q.Publicada{publicado}} : Maybe<&2, Q.Quadro>}) ->
  K.Regra6(I.Publicou{publicado}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t):
  match r:
    case S.Resposta{S.Sucesso{}, +v}: sucesso_com_portos(fonte, c, mundo, s, rx, m, req, ctx, origem, xs, n, w, ts, proposta, v, bs, depois, t, publicado, valido, verificada, finalizada, indice, sem_depois, portos, consulta)
    case S.Resposta{S.Recusa{}, +v}: L.ex_falso(K.Regra6(I.Publicou{publicado}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t),
      Fases.ausente_exclui_consulta(Fases.Publicacao{}, Q.concatenar(antes(m, req, ctx, xs), Con{Q.Preparada{S.Resposta{S.Recusa{}, v}, bs}, depois}), t, Q.Publicada{publicado},
        Fases.concatenar_ausencia(Fases.Publicacao{}, antes(m, req, ctx, xs), Con{Q.Preparada{S.Resposta{S.Recusa{}, v}, bs}, depois}, antes_sem_publicacao(m, req, ctx, xs), sem_depois), {==}, consulta))
    case S.Resposta{S.Entrada{}, +v}: L.ex_falso(K.Regra6(I.Publicou{publicado}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t),
      Fases.ausente_exclui_consulta(Fases.Publicacao{}, Q.concatenar(antes(m, req, ctx, xs), Con{Q.Preparada{S.Resposta{S.Entrada{}, v}, bs}, depois}), t, Q.Publicada{publicado},
        Fases.concatenar_ausencia(Fases.Publicacao{}, antes(m, req, ctx, xs), Con{Q.Preparada{S.Resposta{S.Entrada{}, v}, bs}, depois}, antes_sem_publicacao(m, req, ctx, xs), sem_depois), {==}, consulta))
    case S.Resposta{S.Autenticacao{}, +v}: L.ex_falso(K.Regra6(I.Publicou{publicado}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t),
      Fases.ausente_exclui_consulta(Fases.Publicacao{}, Q.concatenar(antes(m, req, ctx, xs), Con{Q.Preparada{S.Resposta{S.Autenticacao{}, v}, bs}, depois}), t, Q.Publicada{publicado},
        Fases.concatenar_ausencia(Fases.Publicacao{}, antes(m, req, ctx, xs), Con{Q.Preparada{S.Resposta{S.Autenticacao{}, v}, bs}, depois}, antes_sem_publicacao(m, req, ctx, xs), sem_depois), {==}, consulta))
    case S.Resposta{S.Certificado{}, +v}: L.ex_falso(K.Regra6(I.Publicou{publicado}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t),
      Fases.ausente_exclui_consulta(Fases.Publicacao{}, Q.concatenar(antes(m, req, ctx, xs), Con{Q.Preparada{S.Resposta{S.Certificado{}, v}, bs}, depois}), t, Q.Publicada{publicado},
        Fases.concatenar_ausencia(Fases.Publicacao{}, antes(m, req, ctx, xs), Con{Q.Preparada{S.Resposta{S.Certificado{}, v}, bs}, depois}, antes_sem_publicacao(m, req, ctx, xs), sem_depois), {==}, consulta))
    case S.Resposta{S.Dados{}, +v}: L.ex_falso(K.Regra6(I.Publicou{publicado}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t),
      Fases.ausente_exclui_consulta(Fases.Publicacao{}, Q.concatenar(antes(m, req, ctx, xs), Con{Q.Preparada{S.Resposta{S.Dados{}, v}, bs}, depois}), t, Q.Publicada{publicado},
        Fases.concatenar_ausencia(Fases.Publicacao{}, antes(m, req, ctx, xs), Con{Q.Preparada{S.Resposta{S.Dados{}, v}, bs}, depois}, antes_sem_publicacao(m, req, ctx, xs), sem_depois), {==}, consulta))
    case S.Resposta{S.Limite{}, +v}: L.ex_falso(K.Regra6(I.Publicou{publicado}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t),
      Fases.ausente_exclui_consulta(Fases.Publicacao{}, Q.concatenar(antes(m, req, ctx, xs), Con{Q.Preparada{S.Resposta{S.Limite{}, v}, bs}, depois}), t, Q.Publicada{publicado},
        Fases.concatenar_ausencia(Fases.Publicacao{}, antes(m, req, ctx, xs), Con{Q.Preparada{S.Resposta{S.Limite{}, v}, bs}, depois}, antes_sem_publicacao(m, req, ctx, xs), sem_depois), {==}, consulta))
    case S.Resposta{S.Falha{}, +v}: L.ex_falso(K.Regra6(I.Publicou{publicado}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t),
      Fases.ausente_exclui_consulta(Fases.Publicacao{}, Q.concatenar(antes(m, req, ctx, xs), Con{Q.Preparada{S.Resposta{S.Falha{}, v}, bs}, depois}), t, Q.Publicada{publicado},
        Fases.concatenar_ausencia(Fases.Publicacao{}, antes(m, req, ctx, xs), Con{Q.Preparada{S.Resposta{S.Falha{}, v}, bs}, depois}, antes_sem_publicacao(m, req, ctx, xs), sem_depois), {==}, consulta))

# A igualdade de N.preparar transporta o conjunto inteiro de argumentos,
# inclusive os portos de observacao do resultado realmente recebido.
def normalizado(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao,
  +m: R.Micro, +req: P.Requisicao, +ctx: D.Contexto, +origem: Fonte.JuizoSintatico, +xs: List<&2, Q.QuadroExec>, +n: Nat,
  +w: D.Estado, +ts: List<&2, S.Evento>, +proposta: S.Resposta, +p: N.Preparada, +bs: List<&2, U32>, +depois: List<&2, Q.Quadro>, +t: Nat, +publicado: D.Estado,
  valido: Req.Valido(c, s), indice: &i: Nat -> {Q.consultar(antes(m, req, ctx, xs), i) == Some{Q.Avaliada{req, ctx, S.Final{w, ts, proposta}}} : Maybe<&2, Q.Quadro>},
  sem_depois: {Fases.ausente(Fases.Publicacao{}, depois) == True{} : Bool}, normalizacao: {p == N.Preparada{w, ts, Req.finalizar(proposta, c, w), bs} : N.Preparada}) ->
  Conclusao.OrigemDaFonte(fonte, c, s, origem, Historico.Registro{req, ctx, n, w, ts, proposta, p}) ->
    Portos(fonte, c, mundo, s, rx, origem, req, ctx, quadro_final(m, req, ctx, xs, p, s, depois)) ->
      {Q.consultar(quadro_final(m, req, ctx, xs, p, s, depois), t) == Some{Q.Publicada{publicado}} : Maybe<&2, Q.Quadro>} ->
        K.Regra6(I.Publicou{publicado}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t):
  %Equal.sym(N.Preparada, p, N.Preparada{w, ts, Req.finalizar(proposta, c, w), bs}, normalizacao) :
    (Conclusao.OrigemDaFonte(fonte, c, s, origem, Historico.Registro{req, ctx, n, w, ts, proposta, _}) ->
      Portos(fonte, c, mundo, s, rx, origem, req, ctx, quadro_final(m, req, ctx, xs, _, s, depois)) ->
        {Q.consultar(quadro_final(m, req, ctx, xs, _, s, depois), t) == Some{Q.Publicada{publicado}} : Maybe<&2, Q.Quadro>} ->
          K.Regra6(I.Publicou{publicado}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t))
  verificada => portos => consulta => resposta_do_resultado(fonte, c, mundo, s, rx, m, req, ctx, origem, xs, n, w, ts, proposta, Req.finalizar(proposta, c, w), bs, depois, t, publicado,
    valido, verificada, {==}, indice, sem_depois, portos, consulta)

def publicacao_final_real(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao,
  +m: R.Micro, +req: P.Requisicao, +ctx: D.Contexto, +origem: Fonte.JuizoSintatico, +xs: List<&2, Q.QuadroExec>, +p: N.Preparada, +depois: List<&2, Q.Quadro>, +t: Nat, +publicado: D.Estado,
  valido: Req.Valido(c, s), aut: {D.autenticar(s, I.credencial(req)) == Some{ctx} : Maybe<&2, D.Contexto>}, juizo: Fonte.JuizoAceito(fonte, c, req, ctx, origem),
  real: Fonte.FinalReal(fonte, c, s, req, ctx, origem, xs, p), sem_depois: {Fases.ausente(Fases.Publicacao{}, depois) == True{} : Bool},
  portos: Portos(fonte, c, mundo, s, rx, origem, req, ctx, quadro_final(m, req, ctx, xs, p, s, depois)),
  consulta: {Q.consultar(quadro_final(m, req, ctx, xs, p, s, depois), t) == Some{Q.Publicada{publicado}} : Maybe<&2, Q.Quadro>}) ->
  K.Regra6(I.Publicou{publicado}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t):
  match real:
    case (+n, +w, +ts, +proposta, L.Ambos{sequencia, L.Ambos{resultado, obtida}}):
      F.com_par(K.Regra6(I.Publicou{publicado}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t),
        {N.percorrer(n, N.iniciar(Fonte.programa(fonte, origem), ctx, I.argumentos(req), s), S.esquema(c)) == S.Final{w, ts, proposta} : S.Percurso},
        {N.percorrer(n, N.iniciar(Fonte.programa(fonte, origem), ctx, I.argumentos(req), s), S.esquema(c)) == S.Final{w, ts, proposta} : S.Percurso},
        Q.igualdade_reabrivel(S.Percurso, N.percorrer(n, N.iniciar(Fonte.programa(fonte, origem), ctx, I.argumentos(req), s), S.esquema(c)), S.Final{w, ts, proposta}, resultado), para_origem => para_indice =>
          F.com_par(K.Regra6(I.Publicou{publicado}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t),
            {N.preparar(N.Parada{w, ts, proposta}, c) == Some{p} : Maybe<&2, N.Preparada>}, {N.preparar(N.Parada{w, ts, proposta}, c) == Some{p} : Maybe<&2, N.Preparada>},
            Q.igualdade_reabrivel(Maybe<&2, N.Preparada>, N.preparar(N.Parada{w, ts, proposta}, c), Some{p}, obtida), para_origem_preparo => para_normalizar =>
              normalizado(fonte, c, mundo, s, rx, m, req, ctx, origem, xs, n, w, ts, proposta, p, Preparacao.bytes_preparados(p), depois, t, publicado, valido,
                indice_no_prefixo(m, req, ctx, xs, w, ts, proposta, Conclusao.ultima_avaliacao_do_resultado_real(fonte, c, s, req, ctx, origem, n, w, ts, proposta, xs, sequencia, para_indice)), sem_depois,
                L.e_esquerda({p == N.Preparada{w, ts, Req.finalizar(proposta, c, w), Preparacao.bytes_preparados(p)} : N.Preparada},
                  P.Mensagem(S.resposta_valor(Req.finalizar(proposta, c, w)), Preparacao.bytes_preparados(p)), Conclusao.normalizar_preparada_real(c, w, ts, proposta, p, para_normalizar)))(L.Ambos{certificado_da_fonte(fonte, c, req, ctx, origem, juizo), L.Ambos{aut, L.Ambos{para_origem, para_origem_preparo}}}, portos, consulta)))

def depois_normal(conclusao: N.Conclusao, entrega: R.Entrega) -> List<&2, Q.Quadro>:
  match conclusao:
    case N.Conclusao{+w, +r, +bs}: Con{Q.Concluida{r, w, False{}}, R.render_entrega(w, bs, False{}, entrega)}
def depois_normal_sem_publicacao(conclusao: N.Conclusao, entrega: R.Entrega) -> {Fases.ausente(Fases.Publicacao{}, depois_normal(conclusao, entrega)) == True{} : Bool}:
  match conclusao:
    case N.Conclusao{w, r, bs}: Fases.entrega_sem_publicacao(w, bs, False{}, entrega)

def forma_normal(+conclusao: N.Conclusao, +entrega: R.Entrega) -> {R.render_conclusao(conclusao, False{}, entrega) == fim(conclusao, depois_normal(conclusao, entrega)) : List<&2, Q.Quadro>}:
  match conclusao:
    case N.Conclusao{w, r, bs}: {==}
def forma_fatal(+conclusao: N.Conclusao, +etapa: X.Etapa, +id: String) -> {R.render_fatal_publicada(conclusao, etapa, id) == fim(conclusao, [Q.Falhou{etapa, id, True{}}, Q.Fechada{}]) : List<&2, Q.Quadro>}:
  match conclusao:
    case N.Conclusao{w, r, bs}: {==}

def associar_antes(+m: R.Micro, +req: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>, +fim: List<&2, Q.Quadro>) ->
  {Con{Q.Configurada{}, Q.concatenar(R.render_execucao(m, req, ctx, xs), Q.concatenar(R.micro_saida(m), fim))} == Q.concatenar(antes(m, req, ctx, xs), fim) : List<&2, Q.Quadro>}:
  Equal.sym(List<&2, Q.Quadro>, Q.concatenar(antes(m, req, ctx, xs), fim),
    Con{Q.Configurada{}, Q.concatenar(R.render_execucao(m, req, ctx, xs), Q.concatenar(R.micro_saida(m), fim))},
    Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, qs => Con{Q.Configurada{}, qs},
      Q.concatenar(Q.concatenar(R.render_execucao(m, req, ctx, xs), R.micro_saida(m)), fim),
      Q.concatenar(R.render_execucao(m, req, ctx, xs), Q.concatenar(R.micro_saida(m), fim)), Q.concatenar_assoc(R.render_execucao(m, req, ctx, xs), R.micro_saida(m), fim)))

def erro_enquadrado_sem_publicacao(q: Maybe<&2, List<&2, U32>>, -r: S.Resposta, +s: D.Estado, +fecha: Bool, entrega: R.Entrega) -> {Fases.ausente(Fases.Publicacao{}, R.render_erro_enquadrado(q, r, s, fecha, entrega)) == True{} : Bool}:
  match q:
    case None{}: {==}
    case Some{bs}: Fases.entrega_sem_publicacao(s, bs, fecha, entrega)
def erro_sem_publicacao(+status: S.Status, +s: D.Estado, +fecha: Bool, entrega: R.Entrega) -> {Fases.ausente(Fases.Publicacao{}, R.render_erro(status, s, fecha, entrega)) == True{} : Bool}:
  erro_enquadrado_sem_publicacao(P.enquadrar(S.resposta_valor(S.resposta_erro(status))), S.resposta_erro(status), s, fecha, entrega)
def falha_sem_publicacao(+s: D.Estado, -etapa: X.Etapa, -id: String, fatal: Bool, entrega: R.Entrega) -> {Fases.ausente(Fases.Publicacao{}, R.render_falha(s, etapa, id, fatal, entrega)) == True{} : Bool}:
  match fatal:
    case True{}: {==}
    case False{}: erro_sem_publicacao(S.Falha{}, s, False{}, entrega)

def ForaFinal(-m: R.Micro, -s: D.Estado, caso: R.Caso) -> Type:
  match caso:
    case R.Executada{r, ctx, xs, p, entrega}: Unit
    case R.FatalAposPublicacao{r, ctx, xs, p, etapa, id}: Unit
    case _: {Fases.ausente(Fases.Publicacao{}, R.render(m, s, caso)) == True{} : Bool}

def fora_final_nao_publica(+m: R.Micro, +s: D.Estado, caso: R.Caso) -> ForaFinal(m, s, caso):
  match caso:
    case R.InicialOk{}: Fases.inicializacao_sem_publicacao(m, s)
    case R.InicialRecusa{status}: {==}
    case R.InicialFalha{+aceita, +etapa, +id, +fatal}:
      Fases.concatenar_ausencia(Fases.Publicacao{}, R.prefixo_inicial(m, aceita), [Q.Falhou{etapa, id, fatal}, Q.InicialRecusada{S.Falha{}}],
        L.e_esquerda({Fases.ausente(Fases.Publicacao{}, R.prefixo_inicial(m, aceita)) == True{} : Bool}, {Fases.ausente(Fases.Inicializacao{}, R.prefixo_inicial(m, aceita)) == True{} : Bool}, Fases.prefixo_inicial_sem_store(m, aceita)), {==})
    case R.SemResposta{}: {==}
    case R.EntradaRecusa{+erro, +fecha, +entrega}:
      Fases.concatenar_ausencia(Fases.Publicacao{}, R.micro_entrada(m), R.render_erro(R.status_entrada(erro), s, fecha, entrega), Fases.micro_entrada_sem_macros(Fases.Publicacao{}, m), erro_sem_publicacao(R.status_entrada(erro), s, fecha, entrega))
    case R.AutRecusa{+r, +entrega}:
      Fases.concatenar_ausencia(Fases.Publicacao{}, R.render_recebida(m, r), Q.concatenar(R.micro_autenticacao(m), Con{Q.Autenticada{r, None{}}, R.render_erro(S.Autenticacao{}, s, False{}, entrega)}), Fases.recebida_sem_macros(Fases.Publicacao{}, m, r),
        Fases.concatenar_ausencia(Fases.Publicacao{}, R.micro_autenticacao(m), Con{Q.Autenticada{r, None{}}, R.render_erro(S.Autenticacao{}, s, False{}, entrega)}, Fases.micro_autenticacao_sem_macros(Fases.Publicacao{}, m), erro_sem_publicacao(S.Autenticacao{}, s, False{}, entrega)))
    case R.GateRecusa{+r, +ctx, +entrega}:
      Fases.concatenar_ausencia(Fases.Publicacao{}, R.render_autenticada(m, r, ctx), Con{Q.Rejeitada{r, ctx}, R.render_erro(S.Certificado{}, s, False{}, entrega)}, Fases.autenticada_sem_macros(Fases.Publicacao{}, m, r, ctx), erro_sem_publicacao(S.Certificado{}, s, False{}, entrega))
    case R.Executada{r, ctx, xs, p, entrega}: Unit{}
    case R.FalhaAntes{+fase, +etapa, +id, +fatal, +entrega}:
      Fases.concatenar_ausencia(Fases.Publicacao{}, R.render_fase(m, fase), R.render_falha(s, etapa, id, fatal, entrega), Fases.fase_anterior_sem_macros(Fases.Publicacao{}, m, fase), falha_sem_publicacao(s, etapa, id, fatal, entrega))
    case R.FatalAposPublicacao{r, ctx, xs, p, etapa, id}: Unit{}
    case R.Pendente{fase}: Fases.fase_anterior_sem_macros(Fases.Publicacao{}, m, fase)
    case R.InicialPendente{+aceita}: L.e_esquerda({Fases.ausente(Fases.Publicacao{}, R.prefixo_inicial(m, aceita)) == True{} : Bool}, {Fases.ausente(Fases.Inicializacao{}, R.prefixo_inicial(m, aceita)) == True{} : Bool}, Fases.prefixo_inicial_sem_store(m, aceita))

def final_ligado(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao,
  +m: R.Micro, +req: P.Requisicao, +ctx: D.Contexto, +origem: Fonte.JuizoSintatico, +xs: List<&2, Q.QuadroExec>, +p: N.Preparada, +depois: List<&2, Q.Quadro>, +t: Nat, +publicado: D.Estado,
  valido: Req.Valido(c, s), aut: {D.autenticar(s, I.credencial(req)) == Some{ctx} : Maybe<&2, D.Contexto>}, juizo: Fonte.JuizoAceito(fonte, c, req, ctx, origem), real: Fonte.FinalReal(fonte, c, s, req, ctx, origem, xs, p),
  sem_depois: {Fases.ausente(Fases.Publicacao{}, depois) == True{} : Bool}, canonico: {I.Atender{mundo, c, s, rx} == Fonte.cenario(fonte, mundo) : I.Cenario},
  raiz: {Fonte.programa(fonte, origem) == Cinco.programa_do_mundo(fonte, mundo) : S.Programa},
  trace: {Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)) == quadro_final(m, req, ctx, xs, p, s, depois) : List<&2, Q.Quadro>},
  consulta: {Q.consultar(Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)), t) == Some{Q.Publicada{publicado}} : Maybe<&2, Q.Quadro>}) ->
  K.Regra6(I.Publicou{publicado}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t):
  F.com_par(K.Regra6(I.Publicou{publicado}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t),
    {Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)) == quadro_final(m, req, ctx, xs, p, s, depois) : List<&2, Q.Quadro>}, {Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)) == quadro_final(m, req, ctx, xs, p, s, depois) : List<&2, Q.Quadro>},
    Q.igualdade_reabrivel(List<&2, Q.Quadro>, Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)), quadro_final(m, req, ctx, xs, p, s, depois), trace), para_portos => para_consulta =>
      publicacao_final_real(fonte, c, mundo, s, rx, m, req, ctx, origem, xs, p, depois, t, publicado, valido, aut, juizo, real, sem_depois,
        portos_da_fonte(fonte, c, mundo, s, rx, origem, req, ctx, quadro_final(m, req, ctx, xs, p, s, depois), canonico, para_portos, raiz),
        (%para_consulta : {Q.consultar(_, t) == Some{Q.Publicada{publicado}} : Maybe<&2, Q.Quadro>} consulta)))

def caso_impossivel(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao,
  +m: R.Micro, +caso: R.Caso, +t: Nat, +publicado: D.Estado,
  sem: {Fases.ausente(Fases.Publicacao{}, R.render(m, s, caso)) == True{} : Bool},
  trace: {Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)) == R.render(m, s, caso) : List<&2, Q.Quadro>},
  consulta: {Q.consultar(Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)), t) == Some{Q.Publicada{publicado}} : Maybe<&2, Q.Quadro>}) ->
  K.Regra6(I.Publicou{publicado}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t):
  L.ex_falso(K.Regra6(I.Publicou{publicado}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t), Fases.ausente_exclui_consulta(Fases.Publicacao{}, R.render(m, s, caso), t, Q.Publicada{publicado}, sem, {==},
    (%trace : {Q.consultar(_, t) == Some{Q.Publicada{publicado}} : Maybe<&2, Q.Quadro>} consulta)))

def publicacao_do_caso(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao,
  +m: R.Micro, +origem: Fonte.JuizoSintatico, caso: R.Caso, +t: Nat, +publicado: D.Estado,
  valido: Req.Valido(c, s), real: Cinco.CasoReal(fonte, c, s, origem, caso), aut: Cinco.AuthDoCaso(s, caso), juizo: Fonte.JuizoDoCaso(fonte, c, origem, caso),
  canonico: {I.Atender{mundo, c, s, rx} == Fonte.cenario(fonte, mundo) : I.Cenario}, raiz: {Fonte.programa(fonte, origem) == Cinco.programa_do_mundo(fonte, mundo) : S.Programa},
  trace: {Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)) == R.render(m, s, caso) : List<&2, Q.Quadro>},
  consulta: {Q.consultar(Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)), t) == Some{Q.Publicada{publicado}} : Maybe<&2, Q.Quadro>}) ->
  K.Regra6(I.Publicou{publicado}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t):
  match caso:
    case R.Executada{+req, +ctx, +xs, +p, +entrega}:
      final_ligado(fonte, c, mundo, s, rx, m, req, ctx, origem, xs, p, depois_normal(N.concluir(p, s), entrega), t, publicado,
        valido, aut, juizo, real, depois_normal_sem_publicacao(N.concluir(p, s), entrega), canonico, raiz,
        Equal.trans(List<&2, Q.Quadro>, Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)), R.render(m, s, R.Executada{req, ctx, xs, p, entrega}), quadro_final(m, req, ctx, xs, p, s, depois_normal(N.concluir(p, s), entrega)), trace,
          Equal.trans(List<&2, Q.Quadro>, R.render(m, s, R.Executada{req, ctx, xs, p, entrega}), Q.concatenar(antes(m, req, ctx, xs), R.render_final(p, s, False{}, entrega)), quadro_final(m, req, ctx, xs, p, s, depois_normal(N.concluir(p, s), entrega)),
            associar_antes(m, req, ctx, xs, R.render_final(p, s, False{}, entrega)),
            Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, resto => Q.concatenar(antes(m, req, ctx, xs), resto), R.render_final(p, s, False{}, entrega), fim(N.concluir(p, s), depois_normal(N.concluir(p, s), entrega)), forma_normal(N.concluir(p, s), entrega)))), consulta)
    case R.FatalAposPublicacao{+req, +ctx, +xs, +p, +etapa, +id}:
      final_ligado(fonte, c, mundo, s, rx, m, req, ctx, origem, xs, p, [Q.Falhou{etapa, id, True{}}, Q.Fechada{}], t, publicado,
        valido, aut, juizo, real, {==}, canonico, raiz,
        Equal.trans(List<&2, Q.Quadro>, Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)), R.render(m, s, R.FatalAposPublicacao{req, ctx, xs, p, etapa, id}), quadro_final(m, req, ctx, xs, p, s, [Q.Falhou{etapa, id, True{}}, Q.Fechada{}]), trace,
          Equal.trans(List<&2, Q.Quadro>, R.render(m, s, R.FatalAposPublicacao{req, ctx, xs, p, etapa, id}), Q.concatenar(antes(m, req, ctx, xs), R.render_fatal_publicada(N.concluir(p, s), etapa, id)), quadro_final(m, req, ctx, xs, p, s, [Q.Falhou{etapa, id, True{}}, Q.Fechada{}]),
            associar_antes(m, req, ctx, xs, R.render_fatal_publicada(N.concluir(p, s), etapa, id)),
            Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, resto => Q.concatenar(antes(m, req, ctx, xs), resto), R.render_fatal_publicada(N.concluir(p, s), etapa, id), fim(N.concluir(p, s), [Q.Falhou{etapa, id, True{}}, Q.Fechada{}]), forma_fatal(N.concluir(p, s), etapa, id)))), consulta)
    case R.InicialOk{}: caso_impossivel(fonte, c, mundo, s, rx, m, R.InicialOk{}, t, publicado, fora_final_nao_publica(m, s, R.InicialOk{}), trace, consulta)
    case R.InicialRecusa{+a0}: caso_impossivel(fonte, c, mundo, s, rx, m, R.InicialRecusa{a0}, t, publicado, fora_final_nao_publica(m, s, R.InicialRecusa{a0}), trace, consulta)
    case R.InicialFalha{+a0, +a1, +a2, +a3}: caso_impossivel(fonte, c, mundo, s, rx, m, R.InicialFalha{a0, a1, a2, a3}, t, publicado, fora_final_nao_publica(m, s, R.InicialFalha{a0, a1, a2, a3}), trace, consulta)
    case R.SemResposta{}: caso_impossivel(fonte, c, mundo, s, rx, m, R.SemResposta{}, t, publicado, fora_final_nao_publica(m, s, R.SemResposta{}), trace, consulta)
    case R.EntradaRecusa{+a0, +a1, +a2}: caso_impossivel(fonte, c, mundo, s, rx, m, R.EntradaRecusa{a0, a1, a2}, t, publicado, fora_final_nao_publica(m, s, R.EntradaRecusa{a0, a1, a2}), trace, consulta)
    case R.AutRecusa{+a0, +a1}: caso_impossivel(fonte, c, mundo, s, rx, m, R.AutRecusa{a0, a1}, t, publicado, fora_final_nao_publica(m, s, R.AutRecusa{a0, a1}), trace, consulta)
    case R.GateRecusa{+a0, +a1, +a2}: caso_impossivel(fonte, c, mundo, s, rx, m, R.GateRecusa{a0, a1, a2}, t, publicado, fora_final_nao_publica(m, s, R.GateRecusa{a0, a1, a2}), trace, consulta)
    case R.FalhaAntes{+a0, +a1, +a2, +a3, +a4}: caso_impossivel(fonte, c, mundo, s, rx, m, R.FalhaAntes{a0, a1, a2, a3, a4}, t, publicado, fora_final_nao_publica(m, s, R.FalhaAntes{a0, a1, a2, a3, a4}), trace, consulta)
    case R.Pendente{+a0}: caso_impossivel(fonte, c, mundo, s, rx, m, R.Pendente{a0}, t, publicado, fora_final_nao_publica(m, s, R.Pendente{a0}), trace, consulta)
    case R.InicialPendente{+a0}: caso_impossivel(fonte, c, mundo, s, rx, m, R.InicialPendente{a0}, t, publicado, fora_final_nao_publica(m, s, R.InicialPendente{a0}), trace, consulta)

def JuizoDaChamada(~fonte: Fonte.Fonte, ~c: S.Configuracao, +rx: X.Recepcao, dados: Fonte.ChamadaData) -> Type:
  match dados:
    case Fonte.ChamadaData{cf, +origem, pf, tf, +estado, +ferramentas, micro}:
      Fonte.JuizoDoCaso(fonte, c, origem, R.decidir(c, rx, estado, ferramentas))

def publicacao_dados(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao, dados: Fonte.ChamadaData, +t: Nat, +publicado: D.Estado,
  valido: Req.Valido(c, s), canonico: {I.Atender{mundo, c, s, rx} == Fonte.cenario(fonte, mundo) : I.Cenario},
  metadata: {Fonte.chamada(fonte, mundo) == dados : Fonte.ChamadaData}, real: Cinco.ChamadaReal(fonte, c, s, rx, dados), juizo: JuizoDaChamada(fonte, c, rx, dados),
  consulta: {Q.consultar(Vis.quadros_chamada(c, s, rx, Fonte.chamada(fonte, mundo)), t) == Some{Q.Publicada{publicado}} : Maybe<&2, Q.Quadro>}) ->
  K.Regra6(I.Publicou{publicado}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t):
  match dados:
    case Fonte.ChamadaData{+cf, +origem, +pf, +tf, +estado, +ferramentas, +micro}:
      F.com_par(K.Regra6(I.Publicou{publicado}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t),
        {Fonte.chamada(fonte, mundo) == Fonte.ChamadaData{cf, origem, pf, tf, estado, ferramentas, micro} : Fonte.ChamadaData}, {Fonte.chamada(fonte, mundo) == Fonte.ChamadaData{cf, origem, pf, tf, estado, ferramentas, micro} : Fonte.ChamadaData},
        Q.igualdade_reabrivel(Fonte.ChamadaData, Fonte.chamada(fonte, mundo), Fonte.ChamadaData{cf, origem, pf, tf, estado, ferramentas, micro}, metadata), para_raiz => para_trace =>
          F.com_par(K.Regra6(I.Publicou{publicado}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t),
            Cinco.CasoReal(fonte, c, s, origem, R.decidir(c, rx, estado, ferramentas)), L.E<Cinco.AuthDoCaso(s, R.decidir(c, rx, estado, ferramentas)), Cinco.GateDoCaso(R.juizo_de(ferramentas), R.decidir(c, rx, estado, ferramentas))>,
            Cinco.rota_real_decidida(fonte, c, s, origem, estado, ferramentas, rx, real), origem_final => admissao =>
              F.com_par(K.Regra6(I.Publicou{publicado}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t), Cinco.AuthDoCaso(s, R.decidir(c, rx, estado, ferramentas)), Cinco.GateDoCaso(R.juizo_de(ferramentas), R.decidir(c, rx, estado, ferramentas)), admissao,
                aut => gate => publicacao_do_caso(fonte, c, mundo, s, rx, micro, origem, R.decidir(c, rx, estado, ferramentas), t, publicado, valido, origem_final, aut, juizo, canonico,
                  Cinco.mesma_raiz_da_chamada(fonte, mundo, Fonte.ChamadaData{cf, origem, pf, tf, estado, ferramentas, micro}, Equal.sym(Fonte.ChamadaData, Fonte.chamada(fonte, mundo), Fonte.ChamadaData{cf, origem, pf, tf, estado, ferramentas, micro}, para_raiz)),
                  Equal.cong(Fonte.ChamadaData, List<&2, Q.Quadro>, d => Vis.quadros_chamada(c, s, rx, d), Fonte.chamada(fonte, mundo), Fonte.ChamadaData{cf, origem, pf, tf, estado, ferramentas, micro}, para_trace), consulta))))

law publicacao_da_chamada:
  for ~fonte: Fonte.Fonte
  for ~c: S.Configuracao
  for +mundo: Nat
  for +s: D.Estado
  for +rx: X.Recepcao
  for +t: Nat
  for +w: D.Estado
  for valido: Req.Valido(c, s)
  for real: Cinco.ChamadaReal(fonte, c, s, rx, Fonte.chamada(fonte, mundo))
  for juizo: JuizoDaChamada(fonte, c, rx, Fonte.chamada(fonte, mundo))
  for fato: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t, I.Publicou{w})
  K.Regra6(I.Publicou{w}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t)
def publicacao_da_chamada(fonte, c, mundo, s, rx, t, w, valido, real, juizo, fato):
  F.com_par(K.Regra6(I.Publicou{w}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t), {Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
    L.E<{I.Atender{mundo, c, s, rx} == Fonte.cenario(fonte, mundo) : I.Cenario}, Fonte.da_rota(fonte, I.Atender{mundo, c, s, rx}, t, I.Publicou{w})>,
    Fonte.eliminar_fato_literal(fonte, Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t, I.Publicou{w}, fato), nome => literal =>
      F.com_par(K.Regra6(I.Publicou{w}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t), {I.Atender{mundo, c, s, rx} == Fonte.cenario(fonte, mundo) : I.Cenario}, Fonte.da_rota(fonte, I.Atender{mundo, c, s, rx}, t, I.Publicou{w}), literal,
        canonico => obs => publicacao_dados(fonte, c, mundo, s, rx, Fonte.chamada(fonte, mundo), t, w, valido, canonico, {==}, real, juizo,
          Ligacao.quadro_da_observacao(fonte, c, s, rx, Fonte.chamada(fonte, mundo), t, I.Publicou{w}, Unit{}, obs))))

# A inicializacao nao realiza uma transacao/publicacao.
def inicial_sem_publicacao(+m: R.Micro, +s: D.Estado, j: R.Juizo, resultado: R.ResultadoInicial, +valida: Bool) -> {Fases.ausente(Fases.Publicacao{}, R.render(m, s, R.decidir_juizo_inicial(j, resultado, valida))) == True{} : Bool}:
  match j:
    case R.Aceitou{}:
      match resultado:
        case R.Finalizada{}:
          match valida:
            case False{}: {==}
            case True{}: Fases.inicializacao_sem_publicacao(m, s)
        case R.FalhouInicial{+aceita, +etapa, +id, +fatal}: fora_final_nao_publica(m, s, R.InicialFalha{aceita && valida, etapa, id, fatal})
        case R.PendenteInicial{aceita}: fora_final_nao_publica(m, s, R.InicialPendente{aceita && valida})
    case R.Recusou{}: {==}
    case R.ErroJuizo{id, fatal}: {==}
    case R.PendenteJuizo{}: {==}

def inicial_dados_sem_publicacao(~fonte: Fonte.Fonte, ~c: S.Configuracao, +s: D.Estado, dados: Fonte.InicialData) -> {Fases.ausente(Fases.Publicacao{}, Vis.quadros_inicial(fonte, c, s, dados)) == True{} : Bool}:
  match dados:
    case Fonte.InicialData{cf, sf, pf, +j, +resultado, +micro}: inicial_sem_publicacao(micro, s, j, resultado, Config.valida(c, Fonte.identidade(fonte)))

law publicacao_inicial_impossivel:
  for ~fonte: Fonte.Fonte
  for ~c: S.Configuracao
  for +mundo: Nat
  for +s: D.Estado
  for +pi: String
  for +t: Nat
  for +w: D.Estado
  for fato: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t, I.Publicou{w})
  Empty
def publicacao_inicial_impossivel(fonte, c, mundo, s, pi, t, w, fato):
  Fases.ausente_exclui_consulta(Fases.Publicacao{}, Vis.quadros_inicial(fonte, c, s, Fonte.inicial(fonte, mundo)), t, Q.Publicada{w}, inicial_dados_sem_publicacao(fonte, c, s, Fonte.inicial(fonte, mundo)), {==},
    Vis.eliminar_publicacao_fonte_inicial(fonte, c, mundo, s, pi, t, w, fato))

def OrigemDoMomento(~fonte: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, +mundo: Nat, momento: Cenarios.Momento) -> Type:
  match momento:
    case Cenarios.Inicializacao{}: Unit
    case Cenarios.Atendimento{+rx}: L.E<Cinco.OrigemDoMomento(fonte, c, seed, historico, mundo, Cenarios.Atendimento{rx}),
      JuizoDaChamada(fonte, c, rx, Fonte.chamada(fonte, mundo))>

law publicacao_por_momento:
  for ~fonte: Fonte.Fonte
  for ~c: S.Configuracao
  for ~seed: Unit -> D.Estado
  for ~historico: Nat -> List<&2, Historico.Registro>
  for ~pi: String
  for +mundo: Nat
  for momento: Cenarios.Momento
  for +t: Nat
  for +w: D.Estado
  for origem: OrigemDoMomento(fonte, c, seed, historico, mundo, momento)
  for fato: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), Cenarios.de_momento(c, seed, historico, pi, momento, mundo), t, I.Publicou{w})
  K.Regra6(I.Publicou{w}, Fonte.ambiente(fonte), Fonte.artefato(fonte), Cenarios.de_momento(c, seed, historico, pi, momento, mundo), t)
def publicacao_por_momento(fonte, c, seed, historico, pi, mundo, momento, t, w, origem, fato):
  match momento:
    case Cenarios.Inicializacao{}: L.ex_falso(K.Regra6(I.Publicou{w}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, seed(Unit{}), pi}, t), publicacao_inicial_impossivel(fonte, c, mundo, seed(Unit{}), pi, t, w, fato))
    case Cenarios.Atendimento{+rx}:
      match origem:
        case L.Ambos{L.Ambos{cfg, L.Ambos{seed_valido, L.Ambos{fontes, real}}}, juizo}:
          publicacao_da_chamada(fonte, c, mundo, Historico.estado(historico(mundo), seed(Unit{})), rx, t, w,
            Historico.historico_preserva_validade(c, historico(mundo), seed(Unit{}), seed_valido, fontes), real, juizo, fato)
