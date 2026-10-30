# Causas do encerramento do canal na rota gerada e fatos reais de IO.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Interface.bend as I
import ../contrato/LAWS.bend as K
import ../contrato/Logica.bend as L
import ../contrato/Protocolo.bend as P
import ../contrato/Recursos.bend as X
import ../contrato/Semantica.bend as S
import ../src/Nucleo.bend as N
import ../src/Entrada.bend as Entrada
import ../src/Configuracao.bend as Config
import ../src/Transporte.bend as Transporte
import ./FonteServico.bend as Fonte
import ./ProtocoloServico.bend as Q
import ./RotasServico.bend as R
import ./PrimitivasServico.bend as M
import ./Lei5Servico.bend as Cinco
import ./Lei34Servico.bend as Adm
import ./LigacaoServico.bend as Ligacao
import ./VisibilidadeServico.bend as Vis
import ./Fundamentos.bend as F

# Esses sao os efeitos externos reais por incidencia, nao respostas/leis.
def FalhasReais(~fonte: Fonte.Fonte, -x: I.Cenario, -qs: List<&2, Q.Quadro>) -> Type:
  @t: Nat -> @etapa: X.Etapa -> @id: String -> @fatal: Bool ->
    {Q.consultar(qs, t) == Some{Q.Falhou{etapa, id, fatal}} : Maybe<&2, Q.Quadro>} ->
      I.FalhaReal(Fonte.ambiente(fonte), Fonte.artefato(fonte), x, t, etapa, id, fatal)

def FalhasDeEntregaReais(~fonte: Fonte.Fonte, -x: I.Cenario, -qs: List<&2, Q.Quadro>) -> Type:
  @t: Nat -> @prefixo: List<&2, U32> -> {Q.consultar(qs, t) == Some{Q.Interrompida{prefixo}} : Maybe<&2, Q.Quadro>} ->
    I.FalhaEntregaReal(Fonte.ambiente(fonte), Fonte.artefato(fonte), x, t)

def fechada(q: Q.Quadro) -> Bool:
  match q:
    case Q.Fechada{}: True{}
    case _: False{}

def NaoFecha(-qs: List<&2, Q.Quadro>) -> Type:
  Cinco.SemQuadro(qs, Q.Fechada{})

def vazio() -> NaoFecha(Nil{}):
  Cinco.vazio_sem_quadro(Q.Fechada{})

def frente(+q: Q.Quadro, -qs: List<&2, Q.Quadro>, neutra: {fechada(q) == False{} : Bool}, resto: NaoFecha(qs)) -> NaoFecha(Con{q, qs}):
  Cinco.cabeca_por_tag(fechada, q, Q.Fechada{}, qs, neutra, {==}, resto)

def concatenar(+xs: List<&2, Q.Quadro>, -ys: List<&2, Q.Quadro>, a: NaoFecha(xs), b: NaoFecha(ys)) -> NaoFecha(Q.concatenar(xs, ys)):
  Cinco.concatenar_sem_quadro(xs, ys, Q.Fechada{}, a, b)

def micro_entrada(m: R.Micro) -> NaoFecha(R.micro_entrada(m)):
  match m:
    case R.Micro{+a, b, c, d}: Cinco.internas_nao_contem(M.expandir_primitivas(a), Q.Fechada{}, M.primitivas_so_geram_internas(a), {==})
def micro_auth(m: R.Micro) -> NaoFecha(R.micro_autenticacao(m)):
  match m:
    case R.Micro{a, +b, c, d}: Cinco.internas_nao_contem(M.expandir_primitivas(b), Q.Fechada{}, M.primitivas_so_geram_internas(b), {==})
def micro_exec(m: R.Micro) -> NaoFecha(R.micro_execucao(m)):
  match m:
    case R.Micro{a, b, +c, d}: Cinco.internas_nao_contem(M.expandir_primitivas(c), Q.Fechada{}, M.primitivas_so_geram_internas(c), {==})
def micro_saida(m: R.Micro) -> NaoFecha(R.micro_saida(m)):
  match m:
    case R.Micro{a, b, c, +d}: Cinco.internas_nao_contem(M.expandir_primitivas(d), Q.Fechada{}, M.primitivas_so_geram_internas(d), {==})

def recebida(+m: R.Micro, +r: P.Requisicao) -> NaoFecha(R.render_recebida(m, r)):
  concatenar(R.micro_entrada(m), [Q.Recebida{r}], micro_entrada(m), frente(Q.Recebida{r}, Nil{}, {==}, vazio()))
def autenticada(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto) -> NaoFecha(R.render_autenticada(m, r, ctx)):
  concatenar(R.render_recebida(m, r), Q.concatenar(R.micro_autenticacao(m), [Q.Autenticada{r, Some{ctx}}]), recebida(m, r),
    concatenar(R.micro_autenticacao(m), [Q.Autenticada{r, Some{ctx}}], micro_auth(m), frente(Q.Autenticada{r, Some{ctx}}, Nil{}, {==}, vazio())))
def verificada(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto) -> NaoFecha(R.render_verificada(m, r, ctx)):
  concatenar(R.render_autenticada(m, r, ctx), [Q.Aceita{r, ctx}], autenticada(m, r, ctx), frente(Q.Aceita{r, ctx}, Nil{}, {==}, vazio()))
def comecada(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto) -> NaoFecha(R.render_comecada(m, r, ctx)):
  concatenar(R.render_verificada(m, r, ctx), Q.concatenar(R.micro_execucao(m), [Q.Comecada{r, ctx}]), verificada(m, r, ctx),
    concatenar(R.micro_execucao(m), [Q.Comecada{r, ctx}], micro_exec(m), frente(Q.Comecada{r, ctx}, Nil{}, {==}, vazio())))
def quadros_exec(+r: P.Requisicao, +ctx: D.Contexto, xs: List<&2, Q.QuadroExec>) -> NaoFecha(Q.expandir_exec(r, ctx, xs)):
  match xs:
    case Nil{}: vazio()
    case Con{Q.Avaliacao{+p}, t}: frente(Q.Avaliada{r, ctx, p}, Q.expandir_exec(r, ctx, t), {==}, quadros_exec(r, ctx, t))
    case Con{Q.Operacao{+e, +s, +o, +res}, t}: frente(Q.Operada{e, s, o, res}, Q.expandir_exec(r, ctx, t), {==}, quadros_exec(r, ctx, t))
def execucao(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>) -> NaoFecha(R.render_execucao(m, r, ctx, xs)):
  concatenar(R.render_comecada(m, r, ctx), Q.expandir_exec(r, ctx, xs), comecada(m, r, ctx), quadros_exec(r, ctx, xs))
def preparada(p: N.Preparada) -> {fechada(R.quadro_preparada(p)) == False{} : Bool}:
  match p:
    case N.Preparada{w, ts, r, bs}: {==}
def fase(+m: R.Micro, f: R.FaseAntes) -> NaoFecha(R.render_fase(m, f)):
  match f:
    case R.AntesEntrada{}: micro_entrada(m)
    case R.AposReceber{+r}: recebida(m, r)
    case R.AposAutenticar{+r, +ctx}: autenticada(m, r, ctx)
    case R.AposVerificar{+r, +ctx}: verificada(m, r, ctx)
    case R.Executando{+r, +ctx, +xs}: execucao(m, r, ctx, xs)
    case R.AposPreparar{+r, +ctx, +xs, +p}:
      concatenar(R.render_execucao(m, r, ctx, xs), Q.concatenar(R.micro_saida(m), [R.quadro_preparada(p)]), execucao(m, r, ctx, xs),
        concatenar(R.micro_saida(m), [R.quadro_preparada(p)], micro_saida(m), frente(R.quadro_preparada(p), Nil{}, preparada(p), vazio())))

# As tres causas anteriores sao consultas da MESMA lista; a quarta causa
# e a disposicao SemResposta, cuja origem no seletor e demonstrada depois.
def Causa(-xs: List<&2, Q.Quadro>, -t: Nat, -caso: R.Caso) -> Type:
  L.Ou<{caso == R.SemResposta{} : R.Caso},
    L.Ou<&etapa: X.Etapa -> &id: String -> Adm.Antes(xs, t, Q.Falhou{etapa, id, True{}}),
      L.Ou<&r: S.Resposta -> &s: D.Estado -> Adm.Antes(xs, t, Q.Concluida{r, s, True{}}),
        &bs: List<&2, U32> -> Adm.Antes(xs, t, Q.Interrompida{bs})>>>

def antes_deslocado(+xs: List<&2, Q.Quadro>, +ys: List<&2, Q.Quadro>, +t: Nat, -q: Q.Quadro, antes: Adm.Antes(ys, t, q)) -> Adm.Antes(Q.concatenar(xs, ys), Nat.add(Q.tamanho(xs), t), q):
  match antes:
    case (+u, L.Ambos{ordem, consulta}): (Nat.add(Q.tamanho(xs), u), L.Ambos{Q.ordem_deslocada(Q.tamanho(xs), u, t, ordem),
      Equal.trans(Maybe<&2, Q.Quadro>, Q.consultar(Q.concatenar(xs, ys), Nat.add(Q.tamanho(xs), u)), Q.consultar(ys, u), Some{q}, Q.consultar_apos_prefixo(xs, ys, u), consulta)})

def causa_deslocada(+xs: List<&2, Q.Quadro>, +ys: List<&2, Q.Quadro>, +t: Nat, -caso: R.Caso, causa: Causa(ys, t, caso)) -> Causa(Q.concatenar(xs, ys), Nat.add(Q.tamanho(xs), t), caso):
  match causa:
    case L.Esquerda{sem}: L.Esquerda{sem}
    case L.Direita{L.Esquerda{(etapa, id, antes)}}: L.Direita{L.Esquerda{(etapa, id, antes_deslocado(xs, ys, t, Q.Falhou{etapa, id, True{}}, antes))}}
    case L.Direita{L.Direita{L.Esquerda{(r, s, antes)}}}: L.Direita{L.Direita{L.Esquerda{(r, s, antes_deslocado(xs, ys, t, Q.Concluida{r, s, True{}}, antes))}}}
    case L.Direita{L.Direita{L.Direita{(bs, antes)}}}: L.Direita{L.Direita{L.Direita{(bs, antes_deslocado(xs, ys, t, Q.Interrompida{bs}, antes))}}}

def causa_no_sufixo(+xs: List<&2, Q.Quadro>, +ys: List<&2, Q.Quadro>, -caso: R.Caso, +t: Nat,
  causa: @u: Nat -> {Q.consultar(ys, u) == Some{Q.Fechada{}} : Maybe<&2, Q.Quadro>} -> Causa(ys, u, caso),
  parte: &u: Nat -> L.E<{t == Nat.add(Q.tamanho(xs), u) : Nat}, {Q.consultar(ys, u) == Some{Q.Fechada{}} : Maybe<&2, Q.Quadro>}>) -> Causa(Q.concatenar(xs, ys), t, caso):
  match parte:
    case (+u, L.Ambos{posicao, consulta}):
      %Equal.sym(Nat, t, Nat.add(Q.tamanho(xs), u), posicao) : Causa(Q.concatenar(xs, ys), _, caso)
      causa_deslocada(xs, ys, u, caso, causa(u, consulta))

def prefixar_causa(+xs: List<&2, Q.Quadro>, +ys: List<&2, Q.Quadro>, -caso: R.Caso, +t: Nat, sem: NaoFecha(xs),
  causa: @u: Nat -> {Q.consultar(ys, u) == Some{Q.Fechada{}} : Maybe<&2, Q.Quadro>} -> Causa(ys, u, caso),
  consulta: {Q.consultar(Q.concatenar(xs, ys), t) == Some{Q.Fechada{}} : Maybe<&2, Q.Quadro>}) -> Causa(Q.concatenar(xs, ys), t, caso):
  causa_no_sufixo(xs, ys, caso, t, causa, Cinco.retirar_prefixo_sem_quadro(xs, ys, t, Q.Fechada{}, sem, consulta))

def Causas(-xs: List<&2, Q.Quadro>, -caso: R.Caso) -> Type:
  @t: Nat -> {Q.consultar(xs, t) == Some{Q.Fechada{}} : Maybe<&2, Q.Quadro>} -> Causa(xs, t, caso)

def trocar_causas(-xs: List<&2, Q.Quadro>, -ys: List<&2, Q.Quadro>, -caso: R.Caso,
  igual: {xs == ys : List<&2, Q.Quadro>}, prova: Causas(xs, caso)) -> Causas(ys, caso):
  %igual : Causas(_, caso) prova

def prefixar(+xs: List<&2, Q.Quadro>, +ys: List<&2, Q.Quadro>, -caso: R.Caso, sem: NaoFecha(xs), prova: Causas(ys, caso)) -> Causas(Q.concatenar(xs, ys), caso):
  +t => consulta => prefixar_causa(xs, ys, caso, t, sem, prova, consulta)

def sem_fecho(+xs: List<&2, Q.Quadro>, -caso: R.Caso, sem: NaoFecha(xs)) -> Causas(xs, caso):
  +t => consulta => L.ex_falso(Causa(xs, t, caso), sem(t, consulta))

def par_antecede(+q: Q.Quadro, t: Nat, nao_fecha: {fechada(q) == False{} : Bool},
  consulta: {Q.consultar([q, Q.Fechada{}], t) == Some{Q.Fechada{}} : Maybe<&2, Q.Quadro>}) -> Adm.Antes([q, Q.Fechada{}], t, q):
  match t:
    case 0n: L.ex_falso(Adm.Antes([q, Q.Fechada{}], 0n, q), frente(q, Nil{}, nao_fecha, vazio())(0n, consulta))
    case 1n: (0n, L.Ambos{{==}, {==}})
    case 2n+k: L.ex_falso(Adm.Antes([q, Q.Fechada{}], 2n+k, q), F.nenhum_nao_algum(Q.Quadro, Q.Fechada{}, consulta))

def par_fatal(+etapa: X.Etapa, +id: String, -caso: R.Caso) -> Causas([Q.Falhou{etapa, id, True{}}, Q.Fechada{}], caso):
  +t => consulta => L.Direita{L.Esquerda{(etapa, id, par_antecede(Q.Falhou{etapa, id, True{}}, t, {==}, consulta))}}

def par_interrompido(+bs: List<&2, U32>, -caso: R.Caso) -> Causas([Q.Interrompida{bs}, Q.Fechada{}], caso):
  +t => consulta => L.Direita{L.Direita{L.Direita{(bs, par_antecede(Q.Interrompida{bs}, t, {==}, consulta))}}}

def antes_de_todo_sufixo(+xs: List<&2, Q.Quadro>, -ys: List<&2, Q.Quadro>, -t: Nat, +j: Nat, -q: Q.Quadro, +i: Nat,
  posicao: {t == Nat.add(Q.tamanho(xs), j) : Nat}, presente: {Q.consultar(xs, i) == Some{q} : Maybe<&2, Q.Quadro>}) -> Adm.Antes(Q.concatenar(xs, ys), t, q):
  F.com_par(Adm.Antes(Q.concatenar(xs, ys), t, q), {Q.consultar(xs, i) == Some{q} : Maybe<&2, Q.Quadro>}, {Q.consultar(xs, i) == Some{q} : Maybe<&2, Q.Quadro>},
    Q.igualdade_reabrivel(Maybe<&2, Q.Quadro>, Q.consultar(xs, i), Some{q}, presente), uma => duas =>
      (i, L.Ambos{(%Equal.sym(Nat, t, Nat.add(Q.tamanho(xs), j), posicao) : {Nat.is_lt(i, _) == True{} : Bool}
        Cinco.menor_permanece_com_acrescimo(i, Q.tamanho(xs), j, Q.posicao_presente_dentro(xs, i, q, uma))), Adm.consulta_prefixo(xs, ys, i, q, duas)}))

def conclusao_antecede_na_parte(+xs: List<&2, Q.Quadro>, -ys: List<&2, Q.Quadro>, -t: Nat, -caso: R.Caso,
  +r: S.Resposta, +s: D.Estado, +i: Nat, presente: {Q.consultar(xs, i) == Some{Q.Concluida{r, s, True{}}} : Maybe<&2, Q.Quadro>},
  parte: &u: Nat -> L.E<{t == Nat.add(Q.tamanho(xs), u) : Nat}, {Q.consultar(ys, u) == Some{Q.Fechada{}} : Maybe<&2, Q.Quadro>}>) -> Causa(Q.concatenar(xs, ys), t, caso):
  match parte:
    case (+u, L.Ambos{posicao, consulta}): L.Direita{L.Direita{L.Esquerda{(r, s,
      antes_de_todo_sufixo(xs, ys, t, u, Q.Concluida{r, s, True{}}, i, posicao, presente))}}}

def parte_impossivel(-xs: List<&2, Q.Quadro>, -ys: List<&2, Q.Quadro>, -t: Nat, sem: NaoFecha(ys),
  parte: &u: Nat -> L.E<{t == Nat.add(Q.tamanho(xs), u) : Nat}, {Q.consultar(ys, u) == Some{Q.Fechada{}} : Maybe<&2, Q.Quadro>}>) -> Empty:
  match parte:
    case (u, L.Ambos{posicao, consulta}): sem(u, consulta)

def depois_false_sem_fechar(+s: D.Estado, proxima: Bool) -> NaoFecha(R.depois_entrega(False{}, s, proxima)):
  match proxima:
    case False{}: vazio()
    case True{}: frente(Q.Seguinte{s, s}, Nil{}, {==}, vazio())

def causa_da_entrega(+xs: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, entrega: R.Entrega, +fecha: Bool, +t: Nat, -caso: R.Caso,
  +i: Nat, concluiu: {Q.consultar(xs, i) == Some{Q.Concluida{r, s, fecha}} : Maybe<&2, Q.Quadro>},
  parte: &u: Nat -> L.E<{t == Nat.add(Q.tamanho(xs), u) : Nat}, {Q.consultar(R.render_entrega(s, bs, fecha, entrega), u) == Some{Q.Fechada{}} : Maybe<&2, Q.Quadro>}>) -> Causa(Q.concatenar(xs, R.render_entrega(s, bs, fecha, entrega)), t, caso):
  match entrega:
    case R.Completa{+proxima}:
      match fecha:
        case True{}: conclusao_antecede_na_parte(xs, R.render_entrega(s, bs, True{}, R.Completa{proxima}), t, caso, r, s, i, concluiu, parte)
        case False{}: L.ex_falso(Causa(Q.concatenar(xs, R.render_entrega(s, bs, False{}, R.Completa{proxima})), t, caso),
          parte_impossivel(xs, R.render_entrega(s, bs, False{}, R.Completa{proxima}), t, frente(Q.Entregue{bs}, R.depois_entrega(False{}, s, proxima), {==}, depois_false_sem_fechar(s, proxima)), parte))
    case R.Quebrada{+prefixo}: causa_no_sufixo(xs, [Q.Interrompida{prefixo}, Q.Fechada{}], caso, t, par_interrompido(prefixo, caso), parte)
    case R.PendenteEntrega{}: L.ex_falso(Causa(Q.concatenar(xs, Nil{}), t, caso), parte_impossivel(xs, Nil{}, t, vazio(), parte))

def apos_conclusao(+antes: List<&2, Q.Quadro>, +s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecha: Bool, +entrega: R.Entrega, -caso: R.Caso,
  sem: NaoFecha(antes)) -> Causas(Q.concatenar(Q.concatenar(antes, [Q.Concluida{r, s, fecha}]), R.render_entrega(s, bs, fecha, entrega)), caso):
  +t => consulta => causa_da_entrega(Q.concatenar(antes, [Q.Concluida{r, s, fecha}]), s, r, bs, entrega, fecha, t, caso,
    Nat.add(Q.tamanho(antes), 0n), Adm.consulta_da_marca(antes, Q.Concluida{r, s, fecha}),
    Cinco.retirar_prefixo_sem_quadro(Q.concatenar(antes, [Q.Concluida{r, s, fecha}]), R.render_entrega(s, bs, fecha, entrega), t, Q.Fechada{},
      concatenar(antes, [Q.Concluida{r, s, fecha}], sem, frente(Q.Concluida{r, s, fecha}, Nil{}, {==}, vazio())), consulta))

def publicacao_sem_fechar(r: S.Resposta, +s: D.Estado) -> NaoFecha(R.render_publicacao(r, s)):
  match r:
    case S.Resposta{S.Entrada{}, v}: vazio()
    case S.Resposta{S.Autenticacao{}, v}: vazio()
    case S.Resposta{S.Certificado{}, v}: vazio()
    case S.Resposta{S.Dados{}, v}: vazio()
    case S.Resposta{S.Limite{}, v}: vazio()
    case S.Resposta{S.Falha{}, v}: vazio()
    case S.Resposta{S.Recusa{}, v}: vazio()
    case S.Resposta{S.Sucesso{}, v}: frente(Q.Publicada{s}, Nil{}, {==}, vazio())

def causas_conclusao(conclusao: N.Conclusao, +fecha: Bool, +entrega: R.Entrega, -caso: R.Caso) -> Causas(R.render_conclusao(conclusao, fecha, entrega), caso):
  match conclusao:
    case N.Conclusao{+s, +r, +bs}:
      trocar_causas(Q.concatenar(Q.concatenar(Con{Q.Preparada{r, bs}, R.render_publicacao(r, s)}, [Q.Concluida{r, s, fecha}]), R.render_entrega(s, bs, fecha, entrega)),
        R.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega), caso,
        Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, qs => Con{Q.Preparada{r, bs}, qs},
          Q.concatenar(Q.concatenar(R.render_publicacao(r, s), [Q.Concluida{r, s, fecha}]), R.render_entrega(s, bs, fecha, entrega)),
          Q.concatenar(R.render_publicacao(r, s), Con{Q.Concluida{r, s, fecha}, R.render_entrega(s, bs, fecha, entrega)}),
          Q.concatenar_assoc(R.render_publicacao(r, s), [Q.Concluida{r, s, fecha}], R.render_entrega(s, bs, fecha, entrega))),
        apos_conclusao(Con{Q.Preparada{r, bs}, R.render_publicacao(r, s)}, s, r, bs, fecha, entrega, caso,
          frente(Q.Preparada{r, bs}, R.render_publicacao(r, s), {==}, publicacao_sem_fechar(r, s))))

def causas_erro_enquadrado(resultado: Maybe<&2, List<&2, U32>>, +r: S.Resposta, +s: D.Estado, +fecha: Bool, +entrega: R.Entrega, -caso: R.Caso) -> Causas(R.render_erro_enquadrado(resultado, r, s, fecha, entrega), caso):
  match resultado:
    case None{}: sem_fecho(Nil{}, caso, vazio())
    case Some{+bs}: apos_conclusao([Q.Preparada{r, bs}], s, r, bs, fecha, entrega, caso, frente(Q.Preparada{r, bs}, Nil{}, {==}, vazio()))

def causas_erro(+status: S.Status, +s: D.Estado, +fecha: Bool, +entrega: R.Entrega, -caso: R.Caso) -> Causas(R.render_erro(status, s, fecha, entrega), caso):
  causas_erro_enquadrado(P.enquadrar(S.resposta_valor(S.resposta_erro(status))), S.resposta_erro(status), s, fecha, entrega, caso)

def causas_falha(+s: D.Estado, +etapa: X.Etapa, +id: String, fatal: Bool, +entrega: R.Entrega, -caso: R.Caso) -> Causas(R.render_falha(s, etapa, id, fatal, entrega), caso):
  match fatal:
    case True{}: par_fatal(etapa, id, caso)
    case False{}: prefixar([Q.Falhou{etapa, id, False{}}], R.render_erro(S.Falha{}, s, False{}, entrega), caso,
      frente(Q.Falhou{etapa, id, False{}}, Nil{}, {==}, vazio()), causas_erro(S.Falha{}, s, False{}, entrega, caso))

def causas_fatal_publicada(conclusao: N.Conclusao, +etapa: X.Etapa, +id: String, -caso: R.Caso) -> Causas(R.render_fatal_publicada(conclusao, etapa, id), caso):
  match conclusao:
    case N.Conclusao{+s, +r, +bs}: prefixar(Con{Q.Preparada{r, bs}, R.render_publicacao(r, s)}, [Q.Falhou{etapa, id, True{}}, Q.Fechada{}], caso,
      frente(Q.Preparada{r, bs}, R.render_publicacao(r, s), {==}, publicacao_sem_fechar(r, s)), par_fatal(etapa, id, caso))

def inicial_sem_fechar(q: Maybe<&2, List<&2, U32>>, +s: D.Estado) -> NaoFecha(R.render_inicial(q, s)):
  match q:
    case None{}: frente(Q.Codificada{D.estado_valor(s), None{}}, Nil{}, {==}, vazio())
    case Some{+bs}: frente(Q.Codificada{D.estado_valor(s), Some{bs}}, [Q.Guardada{s, bs, s}, Q.Iniciada{s}], {==},
      frente(Q.Guardada{s, bs, s}, [Q.Iniciada{s}], {==}, frente(Q.Iniciada{s}, Nil{}, {==}, vazio())))

def prefixo_inicial_sem_fechar(+m: R.Micro, aceita: Bool) -> NaoFecha(R.prefixo_inicial(m, aceita)):
  match aceita:
    case False{}: vazio()
    case True{}: frente(Q.InicialAceita{}, R.micro_saida(m), {==}, micro_saida(m))

def auth_none_sem_fechar(+m: R.Micro, +r: P.Requisicao) -> NaoFecha(Q.concatenar(R.render_recebida(m, r), Q.concatenar(R.micro_autenticacao(m), [Q.Autenticada{r, None{}}]))):
  concatenar(R.render_recebida(m, r), Q.concatenar(R.micro_autenticacao(m), [Q.Autenticada{r, None{}}]), recebida(m, r),
    concatenar(R.micro_autenticacao(m), [Q.Autenticada{r, None{}}], micro_auth(m), frente(Q.Autenticada{r, None{}}, Nil{}, {==}, vazio())))

# A raiz do renderer, nao uma lista de eventos arbitraria.
def causas_sem_config(+m: R.Micro, +s: D.Estado, caso: R.Caso) -> Causas(R.render_caso(m, s, caso), caso):
  match caso:
    case R.InicialOk{}: sem_fecho(R.render_caso(m, s, R.InicialOk{}), R.InicialOk{},
      frente(Q.InicialAceita{}, Q.concatenar(R.micro_saida(m), R.render_inicial(P.codificar(D.estado_valor(s)), s)), {==},
        concatenar(R.micro_saida(m), R.render_inicial(P.codificar(D.estado_valor(s)), s), micro_saida(m), inicial_sem_fechar(P.codificar(D.estado_valor(s)), s))))
    case R.InicialRecusa{+status}: sem_fecho([Q.InicialRecusada{status}], R.InicialRecusa{status}, frente(Q.InicialRecusada{status}, Nil{}, {==}, vazio()))
    case R.InicialFalha{+aceita, +etapa, +id, +fatal}: sem_fecho(R.render_caso(m, s, R.InicialFalha{aceita, etapa, id, fatal}), R.InicialFalha{aceita, etapa, id, fatal},
      concatenar(R.prefixo_inicial(m, aceita), [Q.Falhou{etapa, id, fatal}, Q.InicialRecusada{S.Falha{}}], prefixo_inicial_sem_fechar(m, aceita),
        frente(Q.Falhou{etapa, id, fatal}, [Q.InicialRecusada{S.Falha{}}], {==}, frente(Q.InicialRecusada{S.Falha{}}, Nil{}, {==}, vazio()))))
    case R.SemResposta{}: t => consulta => L.Esquerda{{==}}
    case R.EntradaRecusa{+erro, +fecha, +entrega}: prefixar(R.micro_entrada(m), R.render_erro(R.status_entrada(erro), s, fecha, entrega), R.EntradaRecusa{erro, fecha, entrega},
      micro_entrada(m), causas_erro(R.status_entrada(erro), s, fecha, entrega, R.EntradaRecusa{erro, fecha, entrega}))
    case R.AutRecusa{+r, +entrega}:
      trocar_causas(Q.concatenar(Q.concatenar(R.render_recebida(m, r), Q.concatenar(R.micro_autenticacao(m), [Q.Autenticada{r, None{}}])), R.render_erro(S.Autenticacao{}, s, False{}, entrega)),
        R.render_caso(m, s, R.AutRecusa{r, entrega}), R.AutRecusa{r, entrega},
        Adm.duas_associacoes(R.render_recebida(m, r), R.micro_autenticacao(m), Q.Autenticada{r, None{}}, R.render_erro(S.Autenticacao{}, s, False{}, entrega)),
        prefixar(Q.concatenar(R.render_recebida(m, r), Q.concatenar(R.micro_autenticacao(m), [Q.Autenticada{r, None{}}])), R.render_erro(S.Autenticacao{}, s, False{}, entrega), R.AutRecusa{r, entrega}, auth_none_sem_fechar(m, r), causas_erro(S.Autenticacao{}, s, False{}, entrega, R.AutRecusa{r, entrega})))
    case R.GateRecusa{+r, +ctx, +entrega}:
      trocar_causas(Q.concatenar(Q.concatenar(R.render_autenticada(m, r, ctx), [Q.Rejeitada{r, ctx}]), R.render_erro(S.Certificado{}, s, False{}, entrega)),
        R.render_caso(m, s, R.GateRecusa{r, ctx, entrega}), R.GateRecusa{r, ctx, entrega},
        Q.concatenar_assoc(R.render_autenticada(m, r, ctx), [Q.Rejeitada{r, ctx}], R.render_erro(S.Certificado{}, s, False{}, entrega)),
        prefixar(Q.concatenar(R.render_autenticada(m, r, ctx), [Q.Rejeitada{r, ctx}]), R.render_erro(S.Certificado{}, s, False{}, entrega), R.GateRecusa{r, ctx, entrega},
          concatenar(R.render_autenticada(m, r, ctx), [Q.Rejeitada{r, ctx}], autenticada(m, r, ctx), frente(Q.Rejeitada{r, ctx}, Nil{}, {==}, vazio())), causas_erro(S.Certificado{}, s, False{}, entrega, R.GateRecusa{r, ctx, entrega})))
    case R.Executada{+r, +ctx, +xs, +p, +entrega}: prefixar(R.render_execucao(m, r, ctx, xs), Q.concatenar(R.micro_saida(m), R.render_final(p, s, False{}, entrega)), R.Executada{r, ctx, xs, p, entrega}, execucao(m, r, ctx, xs),
      prefixar(R.micro_saida(m), R.render_final(p, s, False{}, entrega), R.Executada{r, ctx, xs, p, entrega}, micro_saida(m), causas_conclusao(N.concluir(p, s), False{}, entrega, R.Executada{r, ctx, xs, p, entrega})))
    case R.FalhaAntes{+f, +etapa, +id, +fatal, +entrega}: prefixar(R.render_fase(m, f), R.render_falha(s, etapa, id, fatal, entrega), R.FalhaAntes{f, etapa, id, fatal, entrega}, fase(m, f), causas_falha(s, etapa, id, fatal, entrega, R.FalhaAntes{f, etapa, id, fatal, entrega}))
    case R.FatalAposPublicacao{+r, +ctx, +xs, +p, +etapa, +id}: prefixar(R.render_execucao(m, r, ctx, xs), Q.concatenar(R.micro_saida(m), R.render_fatal_publicada(N.concluir(p, s), etapa, id)), R.FatalAposPublicacao{r, ctx, xs, p, etapa, id}, execucao(m, r, ctx, xs),
      prefixar(R.micro_saida(m), R.render_fatal_publicada(N.concluir(p, s), etapa, id), R.FatalAposPublicacao{r, ctx, xs, p, etapa, id}, micro_saida(m), causas_fatal_publicada(N.concluir(p, s), etapa, id, R.FatalAposPublicacao{r, ctx, xs, p, etapa, id})))
    case R.Pendente{+f}: sem_fecho(R.render_fase(m, f), R.Pendente{f}, fase(m, f))
    case R.InicialPendente{+aceita}: sem_fecho(R.prefixo_inicial(m, aceita), R.InicialPendente{aceita}, prefixo_inicial_sem_fechar(m, aceita))

def causas_do_caso(+m: R.Micro, +s: D.Estado, +caso: R.Caso) -> Causas(R.render(m, s, caso), caso):
  prefixar([Q.Configurada{}], R.render_caso(m, s, caso), caso, frente(Q.Configurada{}, Nil{}, {==}, vazio()), causas_sem_config(m, s, caso))

# Substitui apenas o ramo SemResposta pela inversao do seletor real.
def CausaSemantica(~c: S.Configuracao, -mundo: Nat, -s: D.Estado, -recepcao: X.Recepcao,
  -xs: List<&2, Q.Quadro>, -t: Nat) -> Type:
  L.Ou<K.SemRespostaEsperada(I.Atender{mundo, c, s, recepcao}),
    L.Ou<&etapa: X.Etapa -> &id: String -> Adm.Antes(xs, t, Q.Falhou{etapa, id, True{}}),
      L.Ou<&r: S.Resposta -> &w: D.Estado -> Adm.Antes(xs, t, Q.Concluida{r, w, True{}}),
        &bs: List<&2, U32> -> Adm.Antes(xs, t, Q.Interrompida{bs})>>>

def aplicar_semantica(~c: S.Configuracao, -mundo: Nat, -s: D.Estado, -recepcao: X.Recepcao,
  -xs: List<&2, Q.Quadro>, -t: Nat, -caso: R.Caso,
  seletor: {caso == R.SemResposta{} : R.Caso} -> K.SemRespostaEsperada(I.Atender{mundo, c, s, recepcao}),
  causa: Causa(xs, t, caso)) -> CausaSemantica(c, mundo, s, recepcao, xs, t):
  match causa:
    case L.Esquerda{sem}: L.Esquerda{seletor(sem)}
    case L.Direita{resto}: L.Direita{resto}

def antes_no_servico(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +recepcao: X.Recepcao,
  -t: Nat, +q: Q.Quadro, f: I.Fato, relacao: Q.rel_fato(c, Cinco.programa_do_mundo(fonte, mundo), q, f), marco: Ligacao.Marco(f),
  canonico: {I.Atender{mundo, c, s, recepcao} == Fonte.cenario(fonte, mundo) : I.Cenario},
  antes: Adm.Antes(Vis.quadros_chamada(c, s, recepcao, Fonte.chamada(fonte, mundo)), t, q)) ->
  I.Antes(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t, f):
  match antes:
    case (+u, L.Ambos{ordem, consulta}): (u, L.Ambos{ordem,
      Ligacao.introduzir_quadro(fonte, c, mundo, s, recepcao, u, q, f, canonico, consulta, relacao, marco)})

def encerro_da_causa(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +recepcao: X.Recepcao, +t: Nat,
  canonico: {I.Atender{mundo, c, s, recepcao} == Fonte.cenario(fonte, mundo) : I.Cenario},
  causa: CausaSemantica(c, mundo, s, recepcao, Vis.quadros_chamada(c, s, recepcao, Fonte.chamada(fonte, mundo)), t)) ->
  K.Regra7(I.EncerrouCanal{}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t):
  match causa:
    case L.Esquerda{sem}: L.Esquerda{sem}
    case L.Direita{L.Esquerda{(+etapa, +id, antes)}}:
      L.Direita{L.Esquerda{(etapa, id, antes_no_servico(fonte, c, mundo, s, recepcao, t, Q.Falhou{etapa, id, True{}}, I.FalhouAmbiente{etapa, id, True{}}, {==}, Unit{}, canonico, antes))}}
    case L.Direita{L.Direita{L.Esquerda{(+r, +w, antes)}}}:
      L.Direita{L.Direita{L.Esquerda{(r, w, antes_no_servico(fonte, c, mundo, s, recepcao, t, Q.Concluida{r, w, True{}}, I.Concluiu{r, w, True{}}, {==}, Unit{}, canonico, antes))}}}
    case L.Direita{L.Direita{L.Direita{(+bs, antes)}}}:
      L.Direita{L.Direita{L.Direita{(bs, antes_no_servico(fonte, c, mundo, s, recepcao, t, Q.Interrompida{bs}, I.EntregaInterrompida{bs}, {==}, Unit{}, canonico, antes))}}}

law falha_real_da_chamada:
  for ~fonte: Fonte.Fonte
  for ~c: S.Configuracao
  for +mundo: Nat
  for +s: D.Estado
  for +recepcao: X.Recepcao
  for +t: Nat
  for +etapa: X.Etapa
  for +id: String
  for +fatal: Bool
  for reais: FalhasReais(fonte, I.Atender{mundo, c, s, recepcao}, Vis.quadros_chamada(c, s, recepcao, Fonte.chamada(fonte, mundo)))
  for fato: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t, I.FalhouAmbiente{etapa, id, fatal})
  K.Regra7(I.FalhouAmbiente{etapa, id, fatal}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t)
def falha_real_da_chamada(fonte, c, mundo, s, recepcao, t, etapa, id, fatal, reais, fato):
  reais(t, etapa, id, fatal, Ligacao.extrair_quadro(fonte, c, mundo, s, recepcao, t, I.FalhouAmbiente{etapa, id, fatal}, Unit{}, fato))

# Inversao da mesma decisao pura: nenhum resultado tecnico fabrica EOF.
def sem_resposta(caso: R.Caso) -> Bool:
  match caso:
    case R.SemResposta{}: True{}
    case _: False{}

def limpeza_nao_sem(+r: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>, +p: N.Preparada, limpeza: R.Limpeza, +entrega: R.Entrega) -> {sem_resposta(R.decidir_limpeza(r, ctx, xs, p, limpeza, entrega)) == False{} : Bool}:
  match limpeza:
    case R.Limpa{}: {==}
    case R.ErroLimpeza{id, fatal}: {==}
    case R.FatalAposStore{etapa, id}: {==}
    case R.PendenteLimpeza{}: {==}

def execucao_nao_sem(+r: P.Requisicao, +ctx: D.Contexto, saida: R.SaidaExecucao, +limpeza: R.Limpeza, +entrega: R.Entrega) -> {sem_resposta(R.decidir_execucao(r, ctx, saida, limpeza, entrega)) == False{} : Bool}:
  match saida:
    case R.Finalizou{+xs, +p}: limpeza_nao_sem(r, ctx, xs, p, limpeza, entrega)
    case R.ErroExecucao{ponto, etapa, id, fatal}: {==}
    case R.PendenteExecucao{ponto}: {==}

def juizo_nao_sem(+r: P.Requisicao, +ctx: D.Contexto, dados: R.DadosFerramentas) -> {sem_resposta(R.decidir_juizo(r, ctx, dados)) == False{} : Bool}:
  match dados:
    case R.DadosFerramentas{j, +ex, +li, +en, pre}:
      match j:
        case R.Aceitou{}: execucao_nao_sem(r, ctx, ex, li, en)
        case R.Recusou{}: {==}
        case R.ErroJuizo{id, fatal}: {==}
        case R.PendenteJuizo{}: {==}

def identidade_nao_sem(ctx: Maybe<&2, D.Contexto>, +r: P.Requisicao, +dados: R.DadosFerramentas) -> {sem_resposta(R.decidir_identidade(ctx, r, dados)) == False{} : Bool}:
  match ctx:
    case None{}:
      match dados:
        case R.DadosFerramentas{j, ex, li, en, pre}: {==}
    case Some{+c}: juizo_nao_sem(r, c, dados)

def auth_nao_sem(pre: R.Preprocessamento, +estado: D.Estado, +r: P.Requisicao, +dados: R.DadosFerramentas) -> {sem_resposta(R.decidir_autenticacao(pre, estado, r, dados)) == False{} : Bool}:
  match pre:
    case R.Normal{}: identidade_nao_sem(D.autenticar(estado, I.credencial(r)), r, dados)
    case R.FalhaEnquadramento{id, fatal}: identidade_nao_sem(D.autenticar(estado, I.credencial(r)), r, dados)
    case R.FalhaDecode{id, fatal}: identidade_nao_sem(D.autenticar(estado, I.credencial(r)), r, dados)
    case R.FalhaAuth{id, fatal}: {==}
    case R.PendenteEnquadramento{}: identidade_nao_sem(D.autenticar(estado, I.credencial(r)), r, dados)
    case R.PendenteDecode{}: identidade_nao_sem(D.autenticar(estado, I.credencial(r)), r, dados)
    case R.PendenteAuth{}: {==}

def pre_nao_sem(entrada: Entrada.PreAutenticacao, +dados: R.DadosFerramentas) -> {sem_resposta(R.decidir_pre(entrada, dados)) == False{} : Bool}:
  match entrada:
    case Entrada.Pronta{+s, +r}: auth_nao_sem(R.preprocessamento(dados), s, r, dados)
    case Entrada.ErroMensagem{status}:
      match dados:
        case R.DadosFerramentas{j, ex, li, en, pre}: {==}
    case Entrada.ErroTransporte{}:
      match dados:
        case R.DadosFerramentas{j, ex, li, en, pre}: {==}

def decode_nao_sem(pre: R.Preprocessamento, +bytes: List<&2, U32>, +e: D.Esquema, +lim: S.Limites, +dados: R.DadosFerramentas) -> {sem_resposta(R.decidir_decode(pre, bytes, e, lim, dados)) == False{} : Bool}:
  match pre:
    case R.Normal{}: pre_nao_sem(Entrada.decodificar(bytes, e, lim), dados)
    case R.FalhaEnquadramento{id, fatal}: pre_nao_sem(Entrada.decodificar(bytes, e, lim), dados)
    case R.FalhaDecode{id, fatal}: {==}
    case R.FalhaAuth{id, fatal}: pre_nao_sem(Entrada.decodificar(bytes, e, lim), dados)
    case R.PendenteEnquadramento{}: pre_nao_sem(Entrada.decodificar(bytes, e, lim), dados)
    case R.PendenteDecode{}: {==}
    case R.PendenteAuth{}: pre_nao_sem(Entrada.decodificar(bytes, e, lim), dados)

def pacote_nao_sem(pacote: Maybe<&2, List<&2, U32>>, +e: D.Esquema, +lim: S.Limites, +dados: R.DadosFerramentas) -> {sem_resposta(R.decidir_pacote(pacote, e, lim, dados)) == False{} : Bool}:
  match pacote:
    case None{}:
      match dados:
        case R.DadosFerramentas{j, ex, li, en, pre}: {==}
    case Some{+bs}: decode_nao_sem(R.preprocessamento(dados), bs, e, lim, dados)

def dispo_sem_resposta(d: X.Disposicao, +estado: List<&2, U32>, +e: D.Esquema, +lim: S.Limites, +dados: R.DadosFerramentas,
  marca: {sem_resposta(R.decidir_disposicao(d, estado, e, lim, dados)) == True{} : Bool}) -> {d == X.EncerrarSemResposta{} : X.Disposicao}:
  match d:
    case X.EncerrarSemResposta{}: {==}
    case X.RecusarEncerrar{+status}:
      match dados:
        case R.DadosFerramentas{j, ex, li, en, pre}: F.absurdo_booleano({X.RecusarEncerrar{status} == X.EncerrarSemResposta{} : X.Disposicao}, marca)
    case X.RecusarContinuar{+status}:
      match dados:
        case R.DadosFerramentas{j, ex, li, en, pre}: F.absurdo_booleano({X.RecusarContinuar{status} == X.EncerrarSemResposta{} : X.Disposicao}, marca)
    case X.ProcessarCorpo{+corpo}:
      L.ex_falso({X.ProcessarCorpo{corpo} == X.EncerrarSemResposta{} : X.Disposicao},
        F.falso_nao_verdadeiro(Equal.trans(Bool, False{}, sem_resposta(R.decidir_pacote(Transporte.juntar(estado, corpo), e, lim, dados)), True{},
          Equal.sym(Bool, sem_resposta(R.decidir_pacote(Transporte.juntar(estado, corpo), e, lim, dados)), False{}, pacote_nao_sem(Transporte.juntar(estado, corpo), e, lim, dados)), marca)))

def enq_sem_resposta(pre: R.Preprocessamento, +d: X.Disposicao, +estado: List<&2, U32>, +e: D.Esquema, +lim: S.Limites, +dados: R.DadosFerramentas,
  marca: {sem_resposta(R.decidir_enquadramento(pre, d, estado, e, lim, dados)) == True{} : Bool}) -> {d == X.EncerrarSemResposta{} : X.Disposicao}:
  match pre:
    case R.Normal{}: dispo_sem_resposta(d, estado, e, lim, dados, marca)
    case R.FalhaEnquadramento{id, fatal}: F.absurdo_booleano({d == X.EncerrarSemResposta{} : X.Disposicao}, marca)
    case R.FalhaDecode{id, fatal}: dispo_sem_resposta(d, estado, e, lim, dados, marca)
    case R.FalhaAuth{id, fatal}: dispo_sem_resposta(d, estado, e, lim, dados, marca)
    case R.PendenteEnquadramento{}: F.absurdo_booleano({d == X.EncerrarSemResposta{} : X.Disposicao}, marca)
    case R.PendenteDecode{}: dispo_sem_resposta(d, estado, e, lim, dados, marca)
    case R.PendenteAuth{}: dispo_sem_resposta(d, estado, e, lim, dados, marca)

# Nao usa Processavel nem sucesso da ferramenta: so inverte R.decidir.
law sem_resposta_exige_fim_da_entrada:
  for ~c: S.Configuracao
  for +recepcao: X.Recepcao
  for +estado: List<&2, U32>
  for +dados: R.DadosFerramentas
  for mesma: {R.decidir(c, recepcao, estado, dados) == R.SemResposta{} : R.Caso}
  {X.decidir_recepcao(c, recepcao) == X.EncerrarSemResposta{} : X.Disposicao}
def sem_resposta_exige_fim_da_entrada(c, recepcao, estado, dados, mesma):
  enq_sem_resposta(R.preprocessamento(dados), X.decidir_recepcao_em(S.limites(c), recepcao), estado, S.esquema(c), S.limites(c), dados,
    Equal.trans(Bool, sem_resposta(R.decidir_enquadramento(R.preprocessamento(dados), X.decidir_recepcao_em(S.limites(c), recepcao), estado, S.esquema(c), S.limites(c), dados)),
      sem_resposta(R.decidir(c, recepcao, estado, dados)), True{},
      Equal.cong(R.Caso, Bool, sem_resposta, R.decidir_enquadramento(R.preprocessamento(dados), X.decidir_recepcao_em(S.limites(c), recepcao), estado, S.esquema(c), S.limites(c), dados), R.decidir(c, recepcao, estado, dados),
        Equal.sym(R.Caso, R.decidir(c, recepcao, estado, dados), R.decidir_enquadramento(R.preprocessamento(dados), X.decidir_recepcao_em(S.limites(c), recepcao), estado, S.esquema(c), S.limites(c), dados), Cinco.decidir_por_projecoes(c, recepcao, estado, dados))),
      Equal.cong(R.Caso, Bool, sem_resposta, R.decidir(c, recepcao, estado, dados), R.SemResposta{}, mesma)))

def CausasDaChamada(~c: S.Configuracao, -mundo: Nat, +s: D.Estado, +recepcao: X.Recepcao, +dados: Fonte.ChamadaData) -> Type:
  @t: Nat -> {Q.consultar(Vis.quadros_chamada(c, s, recepcao, dados), t) == Some{Q.Fechada{}} : Maybe<&2, Q.Quadro>} ->
    CausaSemantica(c, mundo, s, recepcao, Vis.quadros_chamada(c, s, recepcao, dados), t)

def causas_semanticas_da_chamada(~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +recepcao: X.Recepcao, dados: Fonte.ChamadaData) -> CausasDaChamada(c, mundo, s, recepcao, dados):
  match dados:
    case Fonte.ChamadaData{cf, ps, pf, tf, +estado, +ferramentas, +micro}:
      +t => consulta => aplicar_semantica(c, mundo, s, recepcao, R.gerar(c, recepcao, estado, s, ferramentas, micro), t, R.decidir(c, recepcao, estado, ferramentas),
        mesma => sem_resposta_exige_fim_da_entrada(c, recepcao, estado, ferramentas, mesma),
        causas_do_caso(micro, s, R.decidir(c, recepcao, estado, ferramentas))(t, consulta))

law encerramento_real_da_chamada:
  for ~fonte: Fonte.Fonte
  for ~c: S.Configuracao
  for +mundo: Nat
  for +s: D.Estado
  for +recepcao: X.Recepcao
  for +t: Nat
  for canonico: {I.Atender{mundo, c, s, recepcao} == Fonte.cenario(fonte, mundo) : I.Cenario}
  for fato: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t, I.EncerrouCanal{})
  K.Regra7(I.EncerrouCanal{}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t)
def encerramento_real_da_chamada(fonte, c, mundo, s, recepcao, t, canonico, fato):
  encerro_da_causa(fonte, c, mundo, s, recepcao, t, canonico,
    causas_semanticas_da_chamada(c, mundo, s, recepcao, Fonte.chamada(fonte, mundo))(t,
      Ligacao.extrair_quadro(fonte, c, mundo, s, recepcao, t, I.EncerrouCanal{}, Unit{}, fato)))

# A inicializacao so tem os seus fatos, inclusive quando o worker falha.
def extrair_inicial_dados(~fonte: Fonte.Fonte, ~c: S.Configuracao, +s: D.Estado, dados: Fonte.InicialData, +t: Nat, f: I.Fato,
  marco: Ligacao.Marco(f), obs: Fonte.de_observacao(fonte, c, Fonte.construir_inicial(Fonte.identidade(fonte), c, s, dados), t, f)) ->
  {Q.consultar(Vis.quadros_inicial(fonte, c, s, dados), t) == Some{Q.quadro_do_fato(f)} : Maybe<&2, Q.Quadro>}:
  match dados:
    case Fonte.InicialData{cf, sf, pf, +j, +resultado, +micro}:
      Q.observacao_quadro(c, Fonte.sem_programa(), R.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, j, resultado, micro), t, f,
        Ligacao.selecionar_marco(c, Fonte.sem_programa(), None{}, R.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, j, resultado, micro), t, f, marco, obs))

def extrair_inicial(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +pi: String, +t: Nat, f: I.Fato,
  marco: Ligacao.Marco(f), literal: L.E<{Fonte.artefato(fonte) == Fonte.artefato(fonte) : String}, L.E<{I.Inicializar{mundo, c, s, pi} == Fonte.cenario(fonte, mundo) : I.Cenario},
    Fonte.da_rota(fonte, I.Inicializar{mundo, c, s, pi}, t, f)>>) ->
  {Q.consultar(Vis.quadros_inicial(fonte, c, s, Fonte.inicial(fonte, mundo)), t) == Some{Q.quadro_do_fato(f)} : Maybe<&2, Q.Quadro>}:
  match literal:
    case L.Ambos{nome, L.Ambos{canonico, obs}}: extrair_inicial_dados(fonte, c, s, Fonte.inicial(fonte, mundo), t, f, marco, obs)

law falha_real_da_inicializacao:
  for ~fonte: Fonte.Fonte
  for ~c: S.Configuracao
  for +mundo: Nat
  for +s: D.Estado
  for +pi: String
  for +t: Nat
  for +etapa: X.Etapa
  for +id: String
  for +fatal: Bool
  for reais: FalhasReais(fonte, I.Inicializar{mundo, c, s, pi}, Vis.quadros_inicial(fonte, c, s, Fonte.inicial(fonte, mundo)))
  for fato: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t, I.FalhouAmbiente{etapa, id, fatal})
  K.Regra7(I.FalhouAmbiente{etapa, id, fatal}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t)
def falha_real_da_inicializacao(fonte, c, mundo, s, pi, t, etapa, id, fatal, reais, fato):
  reais(t, etapa, id, fatal, extrair_inicial(fonte, c, mundo, s, pi, t, I.FalhouAmbiente{etapa, id, fatal}, Unit{},
    Fonte.eliminar_fato_literal(fonte, Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t, I.FalhouAmbiente{etapa, id, fatal}, fato)))

def inicial_nao_fecha(+m: R.Micro, +s: D.Estado, j: R.Juizo, resultado: R.ResultadoInicial, +valida: Bool) -> NaoFecha(R.render(m, s, R.decidir_juizo_inicial(j, resultado, valida))):
  match j:
    case R.Aceitou{}:
      match resultado:
        case R.Finalizada{}:
          match valida:
            case False{}: frente(Q.Configurada{}, [Q.InicialRecusada{S.Dados{}}], {==}, frente(Q.InicialRecusada{S.Dados{}}, Nil{}, {==}, vazio()))
            case True{}: frente(Q.Configurada{}, R.render_caso(m, s, R.InicialOk{}), {==},
              frente(Q.InicialAceita{}, Q.concatenar(R.micro_saida(m), R.render_inicial(P.codificar(D.estado_valor(s)), s)), {==}, concatenar(R.micro_saida(m), R.render_inicial(P.codificar(D.estado_valor(s)), s), micro_saida(m), inicial_sem_fechar(P.codificar(D.estado_valor(s)), s))))
        case R.FalhouInicial{+aceita, +etapa, +id, +fatal}:
          frente(Q.Configurada{}, R.render_caso(m, s, R.InicialFalha{aceita && valida, etapa, id, fatal}), {==},
            concatenar(R.prefixo_inicial(m, aceita && valida), [Q.Falhou{etapa, id, fatal}, Q.InicialRecusada{S.Falha{}}], prefixo_inicial_sem_fechar(m, aceita && valida),
              frente(Q.Falhou{etapa, id, fatal}, [Q.InicialRecusada{S.Falha{}}], {==}, frente(Q.InicialRecusada{S.Falha{}}, Nil{}, {==}, vazio()))))
        case R.PendenteInicial{+aceita}: frente(Q.Configurada{}, R.prefixo_inicial(m, aceita && valida), {==}, prefixo_inicial_sem_fechar(m, aceita && valida))
    case R.Recusou{}: frente(Q.Configurada{}, [Q.InicialRecusada{S.Certificado{}}], {==}, frente(Q.InicialRecusada{S.Certificado{}}, Nil{}, {==}, vazio()))
    case R.ErroJuizo{+id, +fatal}: frente(Q.Configurada{}, [Q.Falhou{X.Verificar{}, id, fatal}, Q.InicialRecusada{S.Falha{}}], {==},
      frente(Q.Falhou{X.Verificar{}, id, fatal}, [Q.InicialRecusada{S.Falha{}}], {==}, frente(Q.InicialRecusada{S.Falha{}}, Nil{}, {==}, vazio())))
    case R.PendenteJuizo{}: frente(Q.Configurada{}, Nil{}, {==}, vazio())

def dados_iniciais_nao_fecham(~fonte: Fonte.Fonte, ~c: S.Configuracao, +s: D.Estado, dados: Fonte.InicialData) -> NaoFecha(Vis.quadros_inicial(fonte, c, s, dados)):
  match dados:
    case Fonte.InicialData{cf, sf, pf, +j, +resultado, +micro}: inicial_nao_fecha(micro, s, j, resultado, Config.valida(c, Fonte.identidade(fonte)))

law encerramento_da_inicializacao_impossivel:
  for ~fonte: Fonte.Fonte
  for ~c: S.Configuracao
  for +mundo: Nat
  for +s: D.Estado
  for +pi: String
  for +t: Nat
  for fato: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t, I.EncerrouCanal{})
  Empty
def encerramento_da_inicializacao_impossivel(fonte, c, mundo, s, pi, t, fato):
  dados_iniciais_nao_fecham(fonte, c, s, Fonte.inicial(fonte, mundo))(t,
    extrair_inicial(fonte, c, mundo, s, pi, t, I.EncerrouCanal{}, Unit{}, Fonte.eliminar_fato_literal(fonte, Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t, I.EncerrouCanal{}, fato)))
