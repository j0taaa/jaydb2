# Progresso a partir dos retornos reais de primitivas, sem prazo ou quota.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Interface.bend as I
import ../contrato/LAWS.bend as K
import ../contrato/Logica.bend as L
import ../contrato/Protocolo.bend as P
import ../contrato/Recursos.bend as X
import ../contrato/Requisitos.bend as R
import ../contrato/Semantica.bend as S
import ../src/Entrada.bend as Entrada
import ../src/Codec.bend as Codec
import ../src/Configuracao.bend as Config
import ../src/Nucleo.bend as N
import ../src/Transporte.bend as Transporte
import ./FonteServico.bend as Fonte
import ./RotasServico.bend as H
import ./ProtocoloServico.bend as Q
import ./Fundamentos.bend as F
import ./Chamada.bend as Chamada
import ./Preparacao.bend as Preparacao
import ./ConclusaoServico.bend as Conclusao
import ./Lei2Servico.bend as Dois
import ./Lei5Servico.bend as Cinco
import ./Entrada.bend as EntradaCompleta
import ./EntradaServico.bend as Copia
import ./ModeloServico.bend as Modelo
import ./CenariosServico.bend as Cenarios
import ./HistoricoServico.bend as Historico
import ./Configuracao.bend as Configuracao

# Testemunhas de consultas, produzidas pelos construtores abaixo.
def ExisteQuadro(-qs: List<&2, Q.Quadro>, -q: Q.Quadro) -> Type:
  &t: Nat -> {Q.consultar(qs, t) == Some{q} : Maybe<&2, Q.Quadro>}

def Fim(-disposicao: X.Disposicao, -qs: List<&2, Q.Quadro>) -> Type:
  L.Ou<L.E<{disposicao == X.EncerrarSemResposta{} : X.Disposicao}, ExisteQuadro(qs, Q.Fechada{})>,
    &r: S.Resposta -> &s: D.Estado -> &fecha: Bool -> &bs: List<&2, U32> ->
      L.E<ExisteQuadro(qs, Q.Concluida{r, s, fecha}), ExisteQuadro(qs, Q.Entregue{bs})>>

def deslocar_existencia(+prefixo: List<&2, Q.Quadro>, +qs: List<&2, Q.Quadro>, +q: Q.Quadro,
  existe: ExisteQuadro(qs, q)) -> ExisteQuadro(Q.concatenar(prefixo, qs), q):
  match existe:
    case (+t, consulta):
      (Nat.add(Q.tamanho(prefixo), t), Equal.trans(Maybe<&2, Q.Quadro>,
        Q.consultar(Q.concatenar(prefixo, qs), Nat.add(Q.tamanho(prefixo), t)), Q.consultar(qs, t), Some{q},
        Q.consultar_apos_prefixo(prefixo, qs, t), consulta))

def deslocar_fim(+prefixo: List<&2, Q.Quadro>, +qs: List<&2, Q.Quadro>, -d: X.Disposicao,
  fim: Fim(d, qs)) -> Fim(d, Q.concatenar(prefixo, qs)):
  match fim:
    case L.Esquerda{L.Ambos{disposicao, fecha}}: L.Esquerda{L.Ambos{disposicao, deslocar_existencia(prefixo, qs, Q.Fechada{}, fecha)}}
    case L.Direita{(+r, +s, +fecha, +bs, L.Ambos{concluiu, entregou})}:
      L.Direita{(r, s, fecha, bs, L.Ambos{
        deslocar_existencia(prefixo, qs, Q.Concluida{r, s, fecha}, concluiu), deslocar_existencia(prefixo, qs, Q.Entregue{bs}, entregou)})}

def fim_da_conclusao(+s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecha: Bool, +proxima: Bool, -d: X.Disposicao) ->
  Fim(d, H.render_conclusao(N.Conclusao{s, r, bs}, fecha, H.Completa{proxima})):
  F.com_par(Fim(d, H.render_conclusao(N.Conclusao{s, r, bs}, fecha, H.Completa{proxima})),
    {Q.consultar(H.render_conclusao(N.Conclusao{s, r, bs}, fecha, H.Completa{proxima}), Conclusao.local_conclusao(s, r, bs)) == Some{Q.Concluida{r, s, fecha}} : Maybe<&2, Q.Quadro>},
    {Q.consultar(H.render_conclusao(N.Conclusao{s, r, bs}, fecha, H.Completa{proxima}), Succ{Conclusao.local_conclusao(s, r, bs)}) == Some{Q.Entregue{bs}} : Maybe<&2, Q.Quadro>},
    Q.dois_quadros_apos_prefixo(Con{Q.Preparada{r, bs}, H.render_publicacao(r, s)}, H.depois_entrega(fecha, s, proxima), Q.Concluida{r, s, fecha}, Q.Entregue{bs}),
    concluiu => entregou => L.Direita{(r, s, fecha, bs, L.Ambos{(Conclusao.local_conclusao(s, r, bs), concluiu), (Succ{Conclusao.local_conclusao(s, r, bs)}, entregou)})})

def fim_preparado(p: N.Preparada, +s: D.Estado, +proxima: Bool, -d: X.Disposicao) ->
  Fim(d, H.render_final(p, s, False{}, H.Completa{proxima})):
  match p:
    case N.Preparada{w, ts, +r, +bs}: fim_da_conclusao(S.publica(r, s, w), r, bs, False{}, proxima, d)

def fim_erro_enquadrado(+r: S.Resposta, +s: D.Estado, +fecha: Bool, +proxima: Bool, -d: X.Disposicao,
  +bs: List<&2, U32>, enquadrado: {P.enquadrar(S.resposta_valor(r)) == Some{bs} : Maybe<&2, List<&2, U32>>}) ->
  Fim(d, H.render_erro_enquadrado(P.enquadrar(S.resposta_valor(r)), r, s, fecha, H.Completa{proxima})):
  %Equal.sym(Maybe<&2, List<&2, U32>>, P.enquadrar(S.resposta_valor(r)), Some{bs}, enquadrado) :
    Fim(d, H.render_erro_enquadrado(_, r, s, fecha, H.Completa{proxima}))
  L.Direita{(r, s, fecha, bs, L.Ambos{(1n, {==}), (2n, {==})})}

def fim_erro_mensagem(~c: S.Configuracao, +status: S.Status, +s: D.Estado, +fecha: Bool, +proxima: Bool, -d: X.Disposicao,
  mensagem: &bs: List<&2, U32> -> P.Mensagem(S.resposta_valor(S.resposta_erro(status)), bs)) ->
  Fim(d, H.render_erro(status, s, fecha, H.Completa{proxima})):
  match mensagem:
    case (+bs, enquadrado): fim_erro_enquadrado(S.resposta_erro(status), s, fecha, proxima, d, bs, enquadrado)

def fim_erro(~c: S.Configuracao, +status: S.Status, +s: D.Estado, +fecha: Bool, +proxima: Bool, -d: X.Disposicao,
  +limites: {R.limites_validos(S.limites(c)) == True{} : Bool}, erro: Preparacao.Erro(status)) ->
  Fim(d, H.render_erro(status, s, fecha, H.Completa{proxima})):
  F.com_par(Fim(d, H.render_erro(status, s, fecha, H.Completa{proxima})),
    I.ErroFixo(S.resposta_erro(status)), {R.cabe(R.limite_resposta(S.limites(c)), S.resposta_valor(S.resposta_erro(status))) == True{} : Bool},
    Preparacao.erro_preparavel(status, S.limites(c), limites, erro),
    payload => cabe => fim_erro_mensagem(c, status, s, fecha, proxima, d,
      Chamada.resposta_preparavel_tem_enquadramento(S.resposta_valor(S.resposta_erro(status)), S.limites(c),
        limites, cabe)))

def fim_com_configuracao(+qs: List<&2, Q.Quadro>, -d: X.Disposicao, fim: Fim(d, qs)) -> Fim(d, Con{Q.Configurada{}, qs}):
  deslocar_fim([Q.Configurada{}], qs, d, fim)

def fim_render_executada(+m: H.Micro, +s: D.Estado, +r: P.Requisicao, +ctx: D.Contexto,
  +xs: List<&2, Q.QuadroExec>, +p: N.Preparada, +proxima: Bool, -d: X.Disposicao) ->
  Fim(d, H.render(m, s, H.Executada{r, ctx, xs, p, H.Completa{proxima}})):
  fim_com_configuracao(Q.concatenar(H.render_execucao(m, r, ctx, xs), Q.concatenar(H.micro_saida(m), H.render_final(p, s, False{}, H.Completa{proxima}))), d,
    deslocar_fim(H.render_execucao(m, r, ctx, xs), Q.concatenar(H.micro_saida(m), H.render_final(p, s, False{}, H.Completa{proxima})), d,
      deslocar_fim(H.micro_saida(m), H.render_final(p, s, False{}, H.Completa{proxima}), d, fim_preparado(p, s, proxima, d))))

def erro_de_entrada_e_fixo(erro: H.ErroEntrada) -> Preparacao.Erro(H.status_entrada(erro)):
  match erro:
    case H.Entrada{}: Unit{}
    case H.Limite{}: Unit{}

def fim_render_entrada(~c: S.Configuracao, +m: H.Micro, +s: D.Estado, +erro: H.ErroEntrada,
  +fecha: Bool, +proxima: Bool, -d: X.Disposicao, +limites: {R.limites_validos(S.limites(c)) == True{} : Bool}) ->
  Fim(d, H.render(m, s, H.EntradaRecusa{erro, fecha, H.Completa{proxima}})):
  fim_com_configuracao(Q.concatenar(H.micro_entrada(m), H.render_erro(H.status_entrada(erro), s, fecha, H.Completa{proxima})), d,
    deslocar_fim(H.micro_entrada(m), H.render_erro(H.status_entrada(erro), s, fecha, H.Completa{proxima}), d,
      fim_erro(c, H.status_entrada(erro), s, fecha, proxima, d, limites, erro_de_entrada_e_fixo(erro))))

def fim_render_aut(~c: S.Configuracao, +m: H.Micro, +s: D.Estado, +r: P.Requisicao,
  +proxima: Bool, -d: X.Disposicao, limites: {R.limites_validos(S.limites(c)) == True{} : Bool}) ->
  Fim(d, H.render(m, s, H.AutRecusa{r, H.Completa{proxima}})):
  fim_com_configuracao(Q.concatenar(H.render_recebida(m, r), Q.concatenar(H.micro_autenticacao(m), Con{Q.Autenticada{r, None{}}, H.render_erro(S.Autenticacao{}, s, False{}, H.Completa{proxima})})), d,
    deslocar_fim(H.render_recebida(m, r), Q.concatenar(H.micro_autenticacao(m), Con{Q.Autenticada{r, None{}}, H.render_erro(S.Autenticacao{}, s, False{}, H.Completa{proxima})}), d,
      deslocar_fim(H.micro_autenticacao(m), Con{Q.Autenticada{r, None{}}, H.render_erro(S.Autenticacao{}, s, False{}, H.Completa{proxima})}, d,
        deslocar_fim([Q.Autenticada{r, None{}}], H.render_erro(S.Autenticacao{}, s, False{}, H.Completa{proxima}), d,
          fim_erro(c, S.Autenticacao{}, s, False{}, proxima, d, limites, Unit{})))))

def fim_render_gate(~c: S.Configuracao, +m: H.Micro, +s: D.Estado, +r: P.Requisicao, +ctx: D.Contexto,
  +proxima: Bool, -d: X.Disposicao, limites: {R.limites_validos(S.limites(c)) == True{} : Bool}) ->
  Fim(d, H.render(m, s, H.GateRecusa{r, ctx, H.Completa{proxima}})):
  fim_com_configuracao(Q.concatenar(H.render_autenticada(m, r, ctx), Con{Q.Rejeitada{r, ctx}, H.render_erro(S.Certificado{}, s, False{}, H.Completa{proxima})}), d,
    deslocar_fim(H.render_autenticada(m, r, ctx), Con{Q.Rejeitada{r, ctx}, H.render_erro(S.Certificado{}, s, False{}, H.Completa{proxima})}, d,
      deslocar_fim([Q.Rejeitada{r, ctx}], H.render_erro(S.Certificado{}, s, False{}, H.Completa{proxima}), d,
        fim_erro(c, S.Certificado{}, s, False{}, proxima, d, limites, Unit{}))))

def fim_render_falha(~c: S.Configuracao, +m: H.Micro, +s: D.Estado, +proxima: Bool, -d: X.Disposicao,
  limites: {R.limites_validos(S.limites(c)) == True{} : Bool}) ->
  Fim(d, H.render(m, s, H.FalhaAntes{H.AntesEntrada{}, X.Enquadrar{}, "internal_transport", False{}, H.Completa{proxima}})):
  fim_com_configuracao(Q.concatenar(H.micro_entrada(m), H.render_falha(s, X.Enquadrar{}, "internal_transport", False{}, H.Completa{proxima})), d,
    deslocar_fim(H.micro_entrada(m), H.render_falha(s, X.Enquadrar{}, "internal_transport", False{}, H.Completa{proxima}), d,
      deslocar_fim([Q.Falhou{X.Enquadrar{}, "internal_transport", False{}}], H.render_erro(S.Falha{}, s, False{}, H.Completa{proxima}), d,
        fim_erro(c, S.Falha{}, s, False{}, proxima, d, limites, Unit{}))))

# Completude de chamadas de ferramenta/worker, nao eventos do protocolo.
def JuizoTerminou(j: H.Juizo) -> Type:
  match j:
    case H.Aceitou{}: Unit
    case H.Recusou{}: Unit
    case H.ErroJuizo{id, fatal}: Empty
    case H.PendenteJuizo{}: Empty

def EscreveuTudo(entrega: H.Entrega) -> Type:
  &proxima: Bool -> {entrega == H.Completa{proxima} : H.Entrega}

def RegressoNativo(-saida: H.SaidaExecucao, -limpeza: H.Limpeza) -> Type:
  &xs: List<&2, Q.QuadroExec> -> &p: N.Preparada ->
    L.E<{saida == H.Finalizou{xs, p} : H.SaidaExecucao}, {limpeza == H.Limpa{} : H.Limpeza}>

def RetornoNativo(~fonte: Fonte.Fonte, -c: S.Configuracao, +origem: Fonte.JuizoSintatico,
  -s: D.Estado, -r: P.Requisicao, -ctx: D.Contexto, -saida: H.SaidaExecucao, -limpeza: H.Limpeza) -> Type:
  I.Termina(Fonte.programa(fonte, origem), S.esquema(c), s, ctx, I.argumentos(r)) -> RegressoNativo(saida, limpeza)

def saida(dados: H.DadosFerramentas) -> H.SaidaExecucao:
  match dados:
    case H.DadosFerramentas{j, ex, li, en, pre}: ex

def limpeza(dados: H.DadosFerramentas) -> H.Limpeza:
  match dados:
    case H.DadosFerramentas{j, ex, li, en, pre}: li

def RetornosNoPre(~fonte: Fonte.Fonte, ~c: S.Configuracao, +origem: Fonte.JuizoSintatico,
  +dados: H.DadosFerramentas, pre: Entrada.PreAutenticacao) -> Type:
  match pre:
    case Entrada.Pronta{s, r}:
      @ctx: D.Contexto -> {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>} ->
        L.E<Fonte.JuizoClienteReal(fonte, c, r, ctx, origem, H.juizo_de(dados)),
          RetornoNativo(fonte, c, origem, s, r, ctx, saida(dados), limpeza(dados))>
    case _: Unit

def RetornosNoPacote(~fonte: Fonte.Fonte, ~c: S.Configuracao, +origem: Fonte.JuizoSintatico,
  +dados: H.DadosFerramentas, pacote: Maybe<&2, List<&2, U32>>) -> Type:
  match pacote:
    case None{}: Unit
    case Some{bs}: RetornosNoPre(fonte, c, origem, dados, Entrada.decodificar(bs, S.esquema(c), S.limites(c)))

def RetornosNaDisposicao(~fonte: Fonte.Fonte, ~c: S.Configuracao, +origem: Fonte.JuizoSintatico,
  +be: List<&2, U32>, +dados: H.DadosFerramentas, disposicao: X.Disposicao) -> Type:
  match disposicao:
    case X.ProcessarCorpo{br}: RetornosNoPacote(fonte, c, origem, dados, Transporte.juntar(be, br))
    case _: Unit

def fim_do_regresso(+m: H.Micro, +s: D.Estado, +r: P.Requisicao, +ctx: D.Contexto,
  +saida: H.SaidaExecucao, +limpeza: H.Limpeza, +proxima: Bool, -d: X.Disposicao, voltou: RegressoNativo(saida, limpeza)) ->
  Fim(d, H.render(m, s, H.decidir_execucao(r, ctx, saida, limpeza, H.Completa{proxima}))):
  match voltou:
    case (+xs, +p, L.Ambos{execucao, limpa}):
      %Equal.sym(H.SaidaExecucao, saida, H.Finalizou{xs, p}, execucao) :
        Fim(d, H.render(m, s, H.decidir_execucao(r, ctx, _, limpeza, H.Completa{proxima})))
      %Equal.sym(H.Limpeza, limpeza, H.Limpa{}, limpa) :
        Fim(d, H.render(m, s, H.decidir_execucao(r, ctx, H.Finalizou{xs, p}, _, H.Completa{proxima})))
      fim_render_executada(m, s, r, ctx, xs, p, proxima, d)

def fim_apos_juizo(~fonte: Fonte.Fonte, ~c: S.Configuracao, +origem: Fonte.JuizoSintatico,
  +m: H.Micro, +s: D.Estado, +decodificado: D.Estado, +r: P.Requisicao, +ctx: D.Contexto,
  j: H.Juizo, +saida: H.SaidaExecucao, +limpeza: H.Limpeza, +proxima: Bool, -d: X.Disposicao,
  limites: {R.limites_validos(S.limites(c)) == True{} : Bool}, terminou: JuizoTerminou(j),
  checado: Fonte.JuizoClienteReal(fonte, c, r, ctx, origem, j),
  runtime: RetornoNativo(fonte, c, origem, decodificado, r, ctx, saida, limpeza)) ->
  Fim(d, H.render(m, s, H.decidir_juizo(r, ctx, H.DadosFerramentas{j, saida, limpeza, H.Completa{proxima}, H.Normal{}}))):
  match j:
    case H.Aceitou{}:
      match checado:
        case L.Ambos{el, L.Ambos{de, L.Ambos{cert, L.Ambos{dt, termina}}}}:
          fim_do_regresso(m, s, r, ctx, saida, limpeza, proxima, d, runtime(termina(decodificado, ctx, I.argumentos(r))))
    case H.Recusou{}: fim_render_gate(c, m, s, r, ctx, proxima, d, limites)
    case H.ErroJuizo{id, fatal}: L.ex_falso(Fim(d, H.render(m, s, H.decidir_juizo(r, ctx, H.DadosFerramentas{H.ErroJuizo{id, fatal}, saida, limpeza, H.Completa{proxima}, H.Normal{}}))), terminou)
    case H.PendenteJuizo{}: L.ex_falso(Fim(d, H.render(m, s, H.decidir_juizo(r, ctx, H.DadosFerramentas{H.PendenteJuizo{}, saida, limpeza, H.Completa{proxima}, H.Normal{}}))), terminou)

def fim_da_identidade(~fonte: Fonte.Fonte, ~c: S.Configuracao, +origem: Fonte.JuizoSintatico,
  +m: H.Micro, +s: D.Estado, +decodificado: D.Estado, +r: P.Requisicao, identidade: Maybe<&2, D.Contexto>,
  +j: H.Juizo, +ex: H.SaidaExecucao, +li: H.Limpeza, +proxima: Bool, -d: X.Disposicao,
  limites: {R.limites_validos(S.limites(c)) == True{} : Bool}, terminou: JuizoTerminou(j),
  retornos: @ctx: D.Contexto -> {identidade == Some{ctx} : Maybe<&2, D.Contexto>} ->
    L.E<Fonte.JuizoClienteReal(fonte, c, r, ctx, origem, j), RetornoNativo(fonte, c, origem, decodificado, r, ctx, ex, li)>) ->
  Fim(d, H.render(m, s, H.decidir_identidade(identidade, r, H.DadosFerramentas{j, ex, li, H.Completa{proxima}, H.Normal{}}))):
  match identidade:
    case None{}: fim_render_aut(c, m, s, r, proxima, d, limites)
    case Some{+ctx}:
      F.com_par(Fim(d, H.render(m, s, H.decidir_identidade(Some{ctx}, r, H.DadosFerramentas{j, ex, li, H.Completa{proxima}, H.Normal{}}))),
        Fonte.JuizoClienteReal(fonte, c, r, ctx, origem, j), RetornoNativo(fonte, c, origem, decodificado, r, ctx, ex, li), retornos(ctx, {==}),
        checado => runtime => fim_apos_juizo(fonte, c, origem, m, s, decodificado, r, ctx, j, ex, li, proxima, d, limites, terminou, checado, runtime))

def fim_da_entrada(~fonte: Fonte.Fonte, ~c: S.Configuracao, +origem: Fonte.JuizoSintatico,
  +m: H.Micro, +s: D.Estado, pre: Entrada.PreAutenticacao,
  +j: H.Juizo, +ex: H.SaidaExecucao, +li: H.Limpeza, +proxima: Bool, -d: X.Disposicao,
  limites: {R.limites_validos(S.limites(c)) == True{} : Bool}, terminou: JuizoTerminou(j),
  retornos: RetornosNoPre(fonte, c, origem, H.DadosFerramentas{j, ex, li, H.Completa{proxima}, H.Normal{}}, pre)) ->
  Fim(d, H.render(m, s, H.decidir_pre(pre, H.DadosFerramentas{j, ex, li, H.Completa{proxima}, H.Normal{}}))):
  match pre:
    case Entrada.Pronta{+decodificado, +r}:
      fim_da_identidade(fonte, c, origem, m, s, decodificado, r, D.autenticar(decodificado, I.credencial(r)), j, ex, li, proxima, d, limites, terminou, retornos)
    case Entrada.ErroMensagem{+status}: fim_render_entrada(c, m, s, H.erro_de_mensagem(status), False{}, proxima, d, limites)
    case Entrada.ErroTransporte{}: fim_render_falha(c, m, s, proxima, d, limites)

def fim_do_pacote(~fonte: Fonte.Fonte, ~c: S.Configuracao, +origem: Fonte.JuizoSintatico,
  +m: H.Micro, +s: D.Estado, pacote: Maybe<&2, List<&2, U32>>,
  +j: H.Juizo, +ex: H.SaidaExecucao, +li: H.Limpeza, +proxima: Bool, -d: X.Disposicao,
  limites: {R.limites_validos(S.limites(c)) == True{} : Bool}, terminou: JuizoTerminou(j),
  retornos: RetornosNoPacote(fonte, c, origem, H.DadosFerramentas{j, ex, li, H.Completa{proxima}, H.Normal{}}, pacote)) ->
  Fim(d, H.render(m, s, H.decidir_pacote(pacote, S.esquema(c), S.limites(c), H.DadosFerramentas{j, ex, li, H.Completa{proxima}, H.Normal{}}))):
  match pacote:
    case None{}: fim_render_falha(c, m, s, proxima, d, limites)
    case Some{+bs}: fim_da_entrada(fonte, c, origem, m, s, Entrada.decodificar(bs, S.esquema(c), S.limites(c)), j, ex, li, proxima, d, limites, terminou, retornos)

def fim_da_disposicao(~fonte: Fonte.Fonte, ~c: S.Configuracao, +origem: Fonte.JuizoSintatico,
  +m: H.Micro, +s: D.Estado, +be: List<&2, U32>, +d: X.Disposicao,
  +j: H.Juizo, +ex: H.SaidaExecucao, +li: H.Limpeza, +proxima: Bool,
  limites: {R.limites_validos(S.limites(c)) == True{} : Bool}, terminou: JuizoTerminou(j),
  retornos: RetornosNaDisposicao(fonte, c, origem, be, H.DadosFerramentas{j, ex, li, H.Completa{proxima}, H.Normal{}}, d)) ->
  Fim(d, H.render(m, s, H.decidir_disposicao(d, be, S.esquema(c), S.limites(c), H.DadosFerramentas{j, ex, li, H.Completa{proxima}, H.Normal{}}))):
  match d:
    case X.EncerrarSemResposta{}: L.Esquerda{L.Ambos{{==}, (1n, {==})}}
    case X.RecusarEncerrar{+status}: fim_render_entrada(c, m, s, H.erro_de_mensagem(status), True{}, proxima, X.RecusarEncerrar{status}, limites)
    case X.RecusarContinuar{+status}: fim_render_entrada(c, m, s, H.erro_de_mensagem(status), False{}, proxima, X.RecusarContinuar{status}, limites)
    case X.ProcessarCorpo{+br}: fim_do_pacote(fonte, c, origem, m, s, Transporte.juntar(be, br), j, ex, li, proxima, X.ProcessarCorpo{br}, limites, terminou, retornos)

# Disponibilidade descreve retornos de read/checker/worker/cleanup/write.
# Nao redefine Processavel e nao fornece Concluiu, Aceita ou Comecada.
def FerramentasDisponiveis(~fonte: Fonte.Fonte, ~c: S.Configuracao, +origem: Fonte.JuizoSintatico,
  +be: List<&2, U32>, +entrada: X.Recepcao, dados: H.DadosFerramentas) -> Type:
  L.E<{H.preprocessamento(dados) == H.Normal{} : H.Preprocessamento},
    L.E<EscreveuTudo(H.entrega_de(dados)),
      L.E<JuizoTerminou(H.juizo_de(dados)), RetornosNaDisposicao(fonte, c, origem, be, dados, X.decidir_recepcao(c, entrada))>>>

def fim_das_ferramentas_normal(~fonte: Fonte.Fonte, ~c: S.Configuracao, +origem: Fonte.JuizoSintatico,
  +m: H.Micro, +s: D.Estado, +be: List<&2, U32>, +entrada: X.Recepcao,
  +j: H.Juizo, +ex: H.SaidaExecucao, +li: H.Limpeza, +en: H.Entrega, +pre: H.Preprocessamento, +proxima: Bool,
  limites: {R.limites_validos(S.limites(c)) == True{} : Bool},
  normal: {pre == H.Normal{} : H.Preprocessamento}, escrita: {en == H.Completa{proxima} : H.Entrega}, terminou: JuizoTerminou(j),
  retornos: RetornosNaDisposicao(fonte, c, origem, be, H.DadosFerramentas{j, ex, li, en, pre}, X.decidir_recepcao(c, entrada))) ->
  Fim(X.decidir_recepcao(c, entrada), H.render(m, s, H.decidir(c, entrada, be, H.DadosFerramentas{j, ex, li, en, pre}))):
  F.com_par(Fim(X.decidir_recepcao(c, entrada), H.render(m, s, H.decidir(c, entrada, be, H.DadosFerramentas{j, ex, li, en, pre}))),
    {pre == H.Normal{} : H.Preprocessamento}, {pre == H.Normal{} : H.Preprocessamento},
    Chamada.duplicar_igualdade(H.Preprocessamento, pre, H.Normal{}, normal), n1 => n2 =>
      F.com_par(Fim(X.decidir_recepcao(c, entrada), H.render(m, s, H.decidir(c, entrada, be, H.DadosFerramentas{j, ex, li, en, pre}))),
        {en == H.Completa{proxima} : H.Entrega}, {en == H.Completa{proxima} : H.Entrega},
        Chamada.duplicar_igualdade(H.Entrega, en, H.Completa{proxima}, escrita), e1 => e2 =>
          %Equal.sym(H.Preprocessamento, pre, H.Normal{}, n1) :
            Fim(X.decidir_recepcao(c, entrada), H.render(m, s, H.decidir(c, entrada, be, H.DadosFerramentas{j, ex, li, en, _})))
          %Equal.sym(H.Entrega, en, H.Completa{proxima}, e1) :
            Fim(X.decidir_recepcao(c, entrada), H.render(m, s, H.decidir(c, entrada, be, H.DadosFerramentas{j, ex, li, _, H.Normal{}})))
          %Equal.sym(H.Caso, H.decidir(c, entrada, be, H.DadosFerramentas{j, ex, li, H.Completa{proxima}, H.Normal{}}),
            H.decidir_enquadramento(H.Normal{}, X.decidir_recepcao(c, entrada), be, S.esquema(c), S.limites(c), H.DadosFerramentas{j, ex, li, H.Completa{proxima}, H.Normal{}}),
            Dois.decidir_por_recepcao(c, entrada, be, H.DadosFerramentas{j, ex, li, H.Completa{proxima}, H.Normal{}})) :
              Fim(X.decidir_recepcao(c, entrada), H.render(m, s, _))
          fim_da_disposicao(fonte, c, origem, m, s, be, X.decidir_recepcao(c, entrada), j, ex, li, proxima, limites, terminou,
            (%n2 : RetornosNaDisposicao(fonte, c, origem, be, H.DadosFerramentas{j, ex, li, H.Completa{proxima}, _}, X.decidir_recepcao(c, entrada))
              %e2 : RetornosNaDisposicao(fonte, c, origem, be, H.DadosFerramentas{j, ex, li, _, pre}, X.decidir_recepcao(c, entrada)) retornos))))

def fim_das_ferramentas(~fonte: Fonte.Fonte, ~c: S.Configuracao, +origem: Fonte.JuizoSintatico,
  +m: H.Micro, +s: D.Estado, +be: List<&2, U32>, +entrada: X.Recepcao, dados: H.DadosFerramentas,
  limites: {R.limites_validos(S.limites(c)) == True{} : Bool}, disponiveis: FerramentasDisponiveis(fonte, c, origem, be, entrada, dados)) ->
  Fim(X.decidir_recepcao(c, entrada), H.render(m, s, H.decidir(c, entrada, be, dados))):
  match dados disponiveis:
    case H.DadosFerramentas{+j, +ex, +li, +en, +pre} L.Ambos{normal, L.Ambos{(+proxima, escrita), L.Ambos{terminou, retornos}}}:
      fim_das_ferramentas_normal(fonte, c, origem, m, s, be, entrada, j, ex, li, en, pre, proxima, limites, normal, escrita, terminou, retornos)

# A consulta e convertida em fato somente pelo renderer e pela fonte fixos.
def EventoDeProgresso(f: I.Fato) -> Type:
  match f:
    case I.Concluiu{r, s, fecha}: Unit
    case I.EntregouTudo{bs}: Unit
    case I.EncerrouCanal{}: Unit
    case I.CertificadoAceito{r, ctx, p}: Unit
    case I.ProgramaComecou{r, ctx, p}: Unit
    case _: Empty

def consulta_observavel(-c: S.Configuracao, -raiz: S.Programa, +ini: Maybe<&2, D.Estado>, +qs: List<&2, Q.Quadro>,
  +t: Nat, +q: Q.Quadro, f: I.Fato, evento: EventoDeProgresso(f),
  relacao: Q.rel_fato(c, raiz, q, f), consulta: {Q.consultar(qs, t) == Some{q} : Maybe<&2, Q.Quadro>}) ->
  Q.observa_servico(c, raiz, ini, qs, t, f):
  match f:
    case I.ConfiguracaoEmUso{outra}: L.ex_falso(Q.observa_servico(c, raiz, ini, qs, t, I.ConfiguracaoEmUso{outra}), evento)
    case I.ProvaInicialAceita{}: L.ex_falso(Q.observa_servico(c, raiz, ini, qs, t, I.ProvaInicialAceita{}), evento)
    case I.InstanciaIniciou{s}: L.ex_falso(Q.observa_servico(c, raiz, ini, qs, t, I.InstanciaIniciou{s}), evento)
    case I.InicializacaoRecusada{s}: L.ex_falso(Q.observa_servico(c, raiz, ini, qs, t, I.InicializacaoRecusada{s}), evento)
    case I.Codificou{v, bs}: L.ex_falso(Q.observa_servico(c, raiz, ini, qs, t, I.Codificou{v, bs}), evento)
    case I.Decodificou{bs, v}: L.ex_falso(Q.observa_servico(c, raiz, ini, qs, t, I.Decodificou{bs, v}), evento)
    case I.Guardou{s, bs, abstr}: L.ex_falso(Q.observa_servico(c, raiz, ini, qs, t, I.Guardou{s, bs, abstr}), evento)
    case I.ConferiuComprimento{pos, n}: L.ex_falso(Q.observa_servico(c, raiz, ini, qs, t, I.ConferiuComprimento{pos, n}), evento)
    case I.AlocouCampo{pos, n}: L.ex_falso(Q.observa_servico(c, raiz, ini, qs, t, I.AlocouCampo{pos, n}), evento)
    case I.LeuCorpo{antes, n, declarado}: L.ex_falso(Q.observa_servico(c, raiz, ini, qs, t, I.LeuCorpo{antes, n, declarado}), evento)
    case I.RecebeuRequisicao{r}: L.ex_falso(Q.observa_servico(c, raiz, ini, qs, t, I.RecebeuRequisicao{r}), evento)
    case I.Autenticou{r, ctx}: L.ex_falso(Q.observa_servico(c, raiz, ini, qs, t, I.Autenticou{r, ctx}), evento)
    case I.CertificadoAceito{r, ctx, outro}: Q.consulta_estabelece_observacao(c, raiz, qs, t, q, I.CertificadoAceito{r, ctx, outro}, consulta, relacao)
    case I.CertificadoRejeitado{r, ctx}: L.ex_falso(Q.observa_servico(c, raiz, ini, qs, t, I.CertificadoRejeitado{r, ctx}), evento)
    case I.ProgramaComecou{r, ctx, outro}: Q.consulta_estabelece_observacao(c, raiz, qs, t, q, I.ProgramaComecou{r, ctx, outro}, consulta, relacao)
    case I.Avaliou{r, ctx, outro, percurso}: L.ex_falso(Q.observa_servico(c, raiz, ini, qs, t, I.Avaliou{r, ctx, outro, percurso}), evento)
    case I.Operou{e, s, o, r}: L.ex_falso(Q.observa_servico(c, raiz, ini, qs, t, I.Operou{e, s, o, r}), evento)
    case I.Preparou{r, bs}: L.ex_falso(Q.observa_servico(c, raiz, ini, qs, t, I.Preparou{r, bs}), evento)
    case I.Publicou{s}: L.ex_falso(Q.observa_servico(c, raiz, ini, qs, t, I.Publicou{s}), evento)
    case I.EstadoVisivel{s}: L.ex_falso(Q.observa_servico(c, raiz, ini, qs, t, I.EstadoVisivel{s}), evento)
    case I.FalhouAmbiente{etapa, id, fatal}: L.ex_falso(Q.observa_servico(c, raiz, ini, qs, t, I.FalhouAmbiente{etapa, id, fatal}), evento)
    case I.Concluiu{r, s, fecha}: Q.consulta_estabelece_observacao(c, raiz, qs, t, q, I.Concluiu{r, s, fecha}, consulta, relacao)
    case I.EntregouTudo{bs}: Q.consulta_estabelece_observacao(c, raiz, qs, t, q, I.EntregouTudo{bs}, consulta, relacao)
    case I.EntregaInterrompida{bs}: L.ex_falso(Q.observa_servico(c, raiz, ini, qs, t, I.EntregaInterrompida{bs}), evento)
    case I.EncerrouCanal{}: Q.consulta_estabelece_observacao(c, raiz, qs, t, q, I.EncerrouCanal{}, consulta, relacao)
    case I.ProximaChamada{antes, apos}: L.ex_falso(Q.observa_servico(c, raiz, ini, qs, t, I.ProximaChamada{antes, apos}), evento)
    case I.InspecaoNaoModelada{descricao}: L.ex_falso(Q.observa_servico(c, raiz, ini, qs, t, I.InspecaoNaoModelada{descricao}), evento)
    case I.EfeitoNaoModelado{descricao}: L.ex_falso(Q.observa_servico(c, raiz, ini, qs, t, I.EfeitoNaoModelado{descricao}), evento)

def RelacaoDaOrigem(~fonte: Fonte.Fonte, -c: S.Configuracao, origem: Maybe<&2, Fonte.JuizoSintatico>, +q: Q.Quadro, -f: I.Fato) -> Type:
  match origem:
    case None{}: Q.rel_fato(c, Fonte.sem_programa(), q, f)
    case Some{origem}: Q.rel_fato(c, Fonte.programa(fonte, origem), q, f)

def consulta_da_origem(~fonte: Fonte.Fonte, -c: S.Configuracao, +ini: Maybe<&2, D.Estado>, +qs: List<&2, Q.Quadro>,
  origem: Maybe<&2, Fonte.JuizoSintatico>, +t: Nat, +q: Q.Quadro, f: I.Fato, evento: EventoDeProgresso(f),
  relacao: RelacaoDaOrigem(fonte, c, origem, q, f), consulta: {Q.consultar(qs, t) == Some{q} : Maybe<&2, Q.Quadro>}) ->
  Fonte.de_origem(fonte, c, ini, qs, origem, t, f):
  match origem:
    case None{}: consulta_observavel(c, Fonte.sem_programa(), ini, qs, t, q, f, evento, relacao, consulta)
    case Some{origem}: consulta_observavel(c, Fonte.programa(fonte, origem), ini, qs, t, q, f, evento, relacao, consulta)

def quadros(dados: Fonte.ObservacaoData) -> List<&2, Q.Quadro>:
  match dados:
    case Fonte.ObservacaoData{ini, qs, origem}: qs

def origem_da_observacao(dados: Fonte.ObservacaoData) -> Maybe<&2, Fonte.JuizoSintatico>:
  match dados:
    case Fonte.ObservacaoData{ini, qs, origem}: origem

def consulta_da_observacao(~fonte: Fonte.Fonte, -c: S.Configuracao, +dados: Fonte.ObservacaoData,
  +t: Nat, +q: Q.Quadro, f: I.Fato, evento: EventoDeProgresso(f),
  relacao: RelacaoDaOrigem(fonte, c, origem_da_observacao(dados), q, f),
  consulta: {Q.consultar(quadros(dados), t) == Some{q} : Maybe<&2, Q.Quadro>}) -> Fonte.de_observacao(fonte, c, dados, t, f):
  match dados:
    case Fonte.ObservacaoData{ini, qs, origem}: consulta_da_origem(fonte, c, ini, qs, origem, t, q, f, evento, relacao, consulta)

def evento_da_rota(~fonte: Fonte.Fonte, ~c: S.Configuracao, +x: Fonte.Contexto, +t: Nat, +q: Q.Quadro, f: I.Fato,
  canonico: {Fonte.cenario_contexto(c, x) == Fonte.cenario(fonte, Fonte.mundo(Fonte.cenario_contexto(c, x))) : I.Cenario},
  evento: EventoDeProgresso(f), relacao: RelacaoDaOrigem(fonte, c, origem_da_observacao(Dois.dados_da_rota(fonte, c, x)), q, f),
  consulta: {Q.consultar(quadros(Dois.dados_da_rota(fonte, c, x)), t) == Some{q} : Maybe<&2, Q.Quadro>}) ->
  I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), Fonte.cenario_contexto(c, x), t, f):
  Fonte.introduzir_fato_literal(fonte, Fonte.artefato(fonte), Fonte.cenario_contexto(c, x), t, f,
    L.Ambos{{==}, L.Ambos{canonico, Dois.observacao_virou_rota(fonte, c, x, t, f,
      consulta_da_observacao(fonte, c, Dois.dados_da_rota(fonte, c, x), t, q, f, evento, relacao, consulta))}})

def relacao_uniforme(~fonte: Fonte.Fonte, -c: S.Configuracao, origem: Maybe<&2, Fonte.JuizoSintatico>, +q: Q.Quadro, -f: I.Fato,
  prova: @p: S.Programa -> Q.rel_fato(c, p, q, f)) -> RelacaoDaOrigem(fonte, c, origem, q, f):
  match origem:
    case None{}: prova(Fonte.sem_programa())
    case Some{origem}: prova(Fonte.programa(fonte, origem))

def DisponibilidadeDaChamada(~fonte: Fonte.Fonte, ~c: S.Configuracao, +entrada: X.Recepcao, dados: Fonte.ChamadaData) -> Type:
  match dados:
    case Fonte.ChamadaData{cf, origem, pf, tf, be, ferramentas, micro}: FerramentasDisponiveis(fonte, c, origem, be, entrada, ferramentas)

def fim_da_metadata(~fonte: Fonte.Fonte, ~c: S.Configuracao, +s: D.Estado, +entrada: X.Recepcao, dados: Fonte.ChamadaData,
  limites: {R.limites_validos(S.limites(c)) == True{} : Bool}, disponiveis: DisponibilidadeDaChamada(fonte, c, entrada, dados)) ->
  Fim(X.decidir_recepcao(c, entrada), quadros(Fonte.construir_chamada(c, s, entrada, dados))):
  match dados:
    case Fonte.ChamadaData{cf, +origem, pf, tf, +be, ferramentas, +micro}: fim_das_ferramentas(fonte, c, origem, micro, s, be, entrada, ferramentas, limites, disponiveis)

def fim_da_chamada(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +entrada: X.Recepcao,
  dados: Fonte.ChamadaData, mesma: {dados == Fonte.chamada(fonte, mundo) : Fonte.ChamadaData},
  limites: {R.limites_validos(S.limites(c)) == True{} : Bool},
  disponiveis: DisponibilidadeDaChamada(fonte, c, entrada, dados)) ->
  Fim(X.decidir_recepcao(c, entrada), quadros(Dois.dados_da_rota(fonte, c, Fonte.Atendimento{mundo, s, entrada}))):
  %mesma : Fim(X.decidir_recepcao(c, entrada), quadros(Fonte.construir_chamada(c, s, entrada, _)))
  fim_da_metadata(fonte, c, s, entrada, dados, limites, disponiveis)

def terminar_da_fonte(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +entrada: X.Recepcao,
  canonico: {I.Atender{mundo, c, s, entrada} == Fonte.cenario(fonte, mundo) : I.Cenario},
  fim: Fim(X.decidir_recepcao(c, entrada), quadros(Dois.dados_da_rota(fonte, c, Fonte.Atendimento{mundo, s, entrada})))) ->
  K.AtendimentoTermina(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, entrada}):
  match fim:
    case L.Esquerda{L.Ambos{sem_resposta, (+t, fechou)}}:
      L.Esquerda{L.Ambos{sem_resposta, (t, evento_da_rota(fonte, c, Fonte.Atendimento{mundo, s, entrada}, t, Q.Fechada{}, I.EncerrouCanal{},
        canonico, Unit{}, relacao_uniforme(fonte, c, origem_da_observacao(Dois.dados_da_rota(fonte, c, Fonte.Atendimento{mundo, s, entrada})), Q.Fechada{}, I.EncerrouCanal{}, p => {==}), fechou))}}
    case L.Direita{(+r, +w, +fecha, +bs, L.Ambos{(+tc, concluiu), (+te, entregou)})}:
      F.com_par(K.AtendimentoTermina(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, entrada}),
        {I.Atender{mundo, c, s, entrada} == Fonte.cenario(fonte, mundo) : I.Cenario},
        {I.Atender{mundo, c, s, entrada} == Fonte.cenario(fonte, mundo) : I.Cenario},
        Chamada.duplicar_igualdade(I.Cenario, I.Atender{mundo, c, s, entrada}, Fonte.cenario(fonte, mundo), canonico), c1 => c2 =>
          L.Direita{(r, w, fecha, L.Ambos{
            (tc, evento_da_rota(fonte, c, Fonte.Atendimento{mundo, s, entrada}, tc, Q.Concluida{r, w, fecha}, I.Concluiu{r, w, fecha}, c1, Unit{},
              relacao_uniforme(fonte, c, origem_da_observacao(Dois.dados_da_rota(fonte, c, Fonte.Atendimento{mundo, s, entrada})), Q.Concluida{r, w, fecha}, I.Concluiu{r, w, fecha}, p => {==}), concluiu)),
            (bs, te, evento_da_rota(fonte, c, Fonte.Atendimento{mundo, s, entrada}, te, Q.Entregue{bs}, I.EntregouTudo{bs}, c2, Unit{},
              relacao_uniforme(fonte, c, origem_da_observacao(Dois.dados_da_rota(fonte, c, Fonte.Atendimento{mundo, s, entrada})), Q.Entregue{bs}, I.EntregouTudo{bs}, p => {==}), entregou))})})

# Completude do parser deriva dos bytes canonicos e das medidas da copia real.
def pacote_pronto_oferece_pronta(~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +entrada: X.Recepcao,
  +be: List<&2, U32>, +br: List<&2, U32>, +r: P.Requisicao,
  disposicao: {X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{br} : X.Disposicao},
  pronto: EntradaCompleta.PacotePronto(S.esquema(c), s, r, S.limites(c), be, br)) ->
  &corpo: List<&2, U32> -> &bs: List<&2, U32> -> L.E<{X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{corpo} : X.Disposicao},
    L.E<{Transporte.juntar(be, corpo) == Some{bs} : Maybe<&2, List<&2, U32>>},
      {Entrada.decodificar(bs, S.esquema(c), S.limites(c)) == Entrada.Pronta{s, r} : Entrada.PreAutenticacao}>>:
  match pronto:
    case (bs, L.Ambos{montagem, L.Ambos{pronta, analise}}): (br, bs, L.Ambos{disposicao, L.Ambos{montagem, pronta}})

def pacote_de_requisicao_medida(~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +entrada: X.Recepcao,
  +be: List<&2, U32>, +r: P.Requisicao, +br: List<&2, U32>, +ce: B.Numero64, +te: B.Numero64,
  disposicao: {X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{br} : X.Disposicao},
  cod_e: P.Codificacao(D.estado_valor(s), be), cod_r: P.Codificacao(P.requisicao_valor(r), br),
  +medida_e: {B.nat64(B.comprimento(be)) == Some{ce} : Maybe<&2, B.Numero64>},
  teto_e: {B.nat64(R.limite_estado(S.limites(c))) == Some{te} : Maybe<&2, B.Numero64>},
  cabe_e: {Codec.menor_igual64(ce, te) == True{} : Bool}, estrutura: {D.estrutura(S.esquema(c), s) == True{} : Bool},
  medidas: &cr: B.Numero64 -> &tr: B.Numero64 -> L.E<{B.nat64(B.comprimento(br)) == Some{cr} : Maybe<&2, B.Numero64>},
    L.E<{B.nat64(R.limite_mensagem(S.limites(c))) == Some{tr} : Maybe<&2, B.Numero64>}, {Codec.menor_igual64(cr, tr) == True{} : Bool}>>) ->
  &corpo: List<&2, U32> -> &bs: List<&2, U32> -> L.E<{X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{corpo} : X.Disposicao},
    L.E<{Transporte.juntar(be, corpo) == Some{bs} : Maybe<&2, List<&2, U32>>},
      {Entrada.decodificar(bs, S.esquema(c), S.limites(c)) == Entrada.Pronta{s, r} : Entrada.PreAutenticacao}>>:
  match medidas:
    case (+cr, +tr, L.Ambos{medida_r, L.Ambos{teto_r, cabe_r}}):
      pacote_pronto_oferece_pronta(c, mundo, s, entrada, be, br, r, disposicao,
        EntradaCompleta.toda_entrada_canonica_admissivel_tem_pacote_pronto_e_analise_exata(S.esquema(c), s, r, S.limites(c), be, br, ce, cr, te, tr,
          cod_e, cod_r, medida_e, medida_r, teto_e, teto_r, cabe_e, cabe_r, estrutura))

def pacote_de_requisicao_recebida(~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +entrada: X.Recepcao,
  +be: List<&2, U32>, +r: P.Requisicao, estado: Copia.EstadoCopiado(c, s, be), corpo: Copia.CorpoCopiado(c, entrada),
  estrutura: {D.estrutura(S.esquema(c), s) == True{} : Bool}, recebido: I.RequisicaoRecebida(I.Atender{mundo, c, s, entrada}, r)) ->
  &br: List<&2, U32> -> &bs: List<&2, U32> ->
    L.E<{X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{br} : X.Disposicao},
      L.E<{Transporte.juntar(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>},
        {Entrada.decodificar(bs, S.esquema(c), S.limites(c)) == Entrada.Pronta{s, r} : Entrada.PreAutenticacao}>>:
  match estado:
    case (+ce, +te, L.Ambos{cod_e, L.Ambos{+medida_e, L.Ambos{teto_e, cabe_e}}}):
      match corpo:
        case L.Ambos{valida, medidas}:
          match recebido:
            case (+br, L.Ambos{+disposicao, cod_r}):
              pacote_de_requisicao_medida(c, mundo, s, entrada, be, r, br, ce, te, disposicao, cod_e, cod_r, medida_e, teto_e, cabe_e, estrutura, medidas(br, disposicao))

def ElaboracaoFuncional(~fonte: Fonte.Fonte, ~c: S.Configuracao) -> Type:
  @codigo: String -> @p: S.Programa -> @q: S.Programa ->
    L.E<Fonte.elaboracao(fonte, c, codigo, p), Fonte.elaboracao(fonte, c, codigo, q)> -> {p == q : S.Programa}

def gate_admite_certificado(~fonte: Fonte.Fonte, ~c: S.Configuracao, +origem: Fonte.JuizoSintatico,
  +s: D.Estado, +r: P.Requisicao, +ctx: D.Contexto, p: S.Programa,
  +j: H.Juizo, +ex: H.SaidaExecucao, +li: H.Limpeza,
  terminou: JuizoTerminou(j), semantica: Fonte.JuizoClienteReal(fonte, c, r, ctx, origem, j),
  runtime: RetornoNativo(fonte, c, origem, s, r, ctx, ex, li), funcional: ElaboracaoFuncional(fonte, c),
  certificado: L.E<I.Vinculado(Fonte.ambiente(fonte), c, I.codigo(r), p),
    I.Deriva(Fonte.ambiente(fonte), c, I.prova(r), R.Certifica(c, I.codigo(r), p, ctx, I.argumentos(r)))>) ->
  L.E<{j == H.Aceitou{} : H.Juizo}, L.E<{p == Fonte.programa(fonte, origem) : S.Programa}, RegressoNativo(ex, li)>>:
  match j:
    case H.Aceitou{}:
      match semantica certificado:
        case L.Ambos{elaborado, L.Ambos{de, L.Ambos{cert, L.Ambos{dt, termina}}}} L.Ambos{L.Ambos{elaborado_p, termina_p}, prova_p}:
          L.Ambos{{==}, L.Ambos{funcional(I.codigo(r), p, Fonte.programa(fonte, origem), L.Ambos{elaborado_p, elaborado}), runtime(termina(s, ctx, I.argumentos(r)))}}
    case H.Recusou{}:
      L.ex_falso(L.E<{H.Recusou{} == H.Aceitou{} : H.Juizo}, L.E<{p == Fonte.programa(fonte, origem) : S.Programa}, RegressoNativo(ex, li)>>, semantica(p, certificado))
    case H.ErroJuizo{id, fatal}:
      L.ex_falso(L.E<{H.ErroJuizo{id, fatal} == H.Aceitou{} : H.Juizo}, L.E<{p == Fonte.programa(fonte, origem) : S.Programa}, RegressoNativo(ex, li)>>, terminou)
    case H.PendenteJuizo{}:
      L.ex_falso(L.E<{H.PendenteJuizo{} == H.Aceitou{} : H.Juizo}, L.E<{p == Fonte.programa(fonte, origem) : S.Programa}, RegressoNativo(ex, li)>>, terminou)

def prolongar_existencia(+qs: List<&2, Q.Quadro>, +sufixo: List<&2, Q.Quadro>, +q: Q.Quadro,
  existe: ExisteQuadro(qs, q)) -> ExisteQuadro(Q.concatenar(qs, sufixo), q):
  match existe:
    case (+t, consulta):
      (t, Q.consulta_prefixo(qs, sufixo, t, q, consulta))

def marcos_da_execucao(+m: H.Micro, +s: D.Estado, +r: P.Requisicao, +ctx: D.Contexto,
  +xs: List<&2, Q.QuadroExec>, +p: N.Preparada, +proxima: Bool) ->
  L.E<ExisteQuadro(H.render(m, s, H.Executada{r, ctx, xs, p, H.Completa{proxima}}), Q.Aceita{r, ctx}),
    ExisteQuadro(H.render(m, s, H.Executada{r, ctx, xs, p, H.Completa{proxima}}), Q.Comecada{r, ctx})>:
  L.Ambos{
    deslocar_existencia([Q.Configurada{}], Q.concatenar(H.render_execucao(m, r, ctx, xs), Q.concatenar(H.micro_saida(m), H.render_final(p, s, False{}, H.Completa{proxima}))), Q.Aceita{r, ctx},
      prolongar_existencia(H.render_execucao(m, r, ctx, xs), Q.concatenar(H.micro_saida(m), H.render_final(p, s, False{}, H.Completa{proxima})), Q.Aceita{r, ctx},
        prolongar_existencia(H.render_comecada(m, r, ctx), Q.expandir_exec(r, ctx, xs), Q.Aceita{r, ctx},
          prolongar_existencia(H.render_verificada(m, r, ctx), Q.concatenar(H.micro_execucao(m), [Q.Comecada{r, ctx}]), Q.Aceita{r, ctx},
            deslocar_existencia(H.render_autenticada(m, r, ctx), [Q.Aceita{r, ctx}], Q.Aceita{r, ctx}, (0n, {==})))))),
    deslocar_existencia([Q.Configurada{}], Q.concatenar(H.render_execucao(m, r, ctx, xs), Q.concatenar(H.micro_saida(m), H.render_final(p, s, False{}, H.Completa{proxima}))), Q.Comecada{r, ctx},
      prolongar_existencia(H.render_execucao(m, r, ctx, xs), Q.concatenar(H.micro_saida(m), H.render_final(p, s, False{}, H.Completa{proxima})), Q.Comecada{r, ctx},
        prolongar_existencia(H.render_comecada(m, r, ctx), Q.expandir_exec(r, ctx, xs), Q.Comecada{r, ctx},
          deslocar_existencia(H.render_verificada(m, r, ctx), Q.concatenar(H.micro_execucao(m), [Q.Comecada{r, ctx}]), Q.Comecada{r, ctx},
            deslocar_existencia(H.micro_execucao(m), [Q.Comecada{r, ctx}], Q.Comecada{r, ctx}, (0n, {==}))))))}

def ferramentas_exatas(+j: H.Juizo, +ex: H.SaidaExecucao, +li: H.Limpeza, +en: H.Entrega, +pre: H.Preprocessamento,
  +xs: List<&2, Q.QuadroExec>, +p: N.Preparada, +proxima: Bool,
  aceitou: {j == H.Aceitou{} : H.Juizo}, executou: {ex == H.Finalizou{xs, p} : H.SaidaExecucao},
  limpou: {li == H.Limpa{} : H.Limpeza}, escreveu: {en == H.Completa{proxima} : H.Entrega}, normal: {pre == H.Normal{} : H.Preprocessamento}) ->
  {H.DadosFerramentas{j, ex, li, en, pre} == H.DadosFerramentas{H.Aceitou{}, H.Finalizou{xs, p}, H.Limpa{}, H.Completa{proxima}, H.Normal{}} : H.DadosFerramentas}:
  %Equal.sym(H.Juizo, j, H.Aceitou{}, aceitou) : {H.DadosFerramentas{_, ex, li, en, pre} == H.DadosFerramentas{H.Aceitou{}, H.Finalizou{xs, p}, H.Limpa{}, H.Completa{proxima}, H.Normal{}} : H.DadosFerramentas}
  %Equal.sym(H.SaidaExecucao, ex, H.Finalizou{xs, p}, executou) : {H.DadosFerramentas{H.Aceitou{}, _, li, en, pre} == H.DadosFerramentas{H.Aceitou{}, H.Finalizou{xs, p}, H.Limpa{}, H.Completa{proxima}, H.Normal{}} : H.DadosFerramentas}
  %Equal.sym(H.Limpeza, li, H.Limpa{}, limpou) : {H.DadosFerramentas{H.Aceitou{}, H.Finalizou{xs, p}, _, en, pre} == H.DadosFerramentas{H.Aceitou{}, H.Finalizou{xs, p}, H.Limpa{}, H.Completa{proxima}, H.Normal{}} : H.DadosFerramentas}
  %Equal.sym(H.Entrega, en, H.Completa{proxima}, escreveu) : {H.DadosFerramentas{H.Aceitou{}, H.Finalizou{xs, p}, H.Limpa{}, _, pre} == H.DadosFerramentas{H.Aceitou{}, H.Finalizou{xs, p}, H.Limpa{}, H.Completa{proxima}, H.Normal{}} : H.DadosFerramentas}
  %Equal.sym(H.Preprocessamento, pre, H.Normal{}, normal) : {H.DadosFerramentas{H.Aceitou{}, H.Finalizou{xs, p}, H.Limpa{}, H.Completa{proxima}, _} == H.DadosFerramentas{H.Aceitou{}, H.Finalizou{xs, p}, H.Limpa{}, H.Completa{proxima}, H.Normal{}} : H.DadosFerramentas}
  {==}

def caso_executado(~c: S.Configuracao, +entrada: X.Recepcao, +be: List<&2, U32>, +dados: H.DadosFerramentas,
  +s: D.Estado, +r: P.Requisicao, +ctx: D.Contexto, +br: List<&2, U32>, +bs: List<&2, U32>,
  +xs: List<&2, Q.QuadroExec>, +p: N.Preparada, +proxima: Bool,
  ferramentas: {dados == H.DadosFerramentas{H.Aceitou{}, H.Finalizou{xs, p}, H.Limpa{}, H.Completa{proxima}, H.Normal{}} : H.DadosFerramentas},
  recebeu: {X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{br} : X.Disposicao},
  montou: {Transporte.juntar(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>},
  decodificou: {Entrada.decodificar(bs, S.esquema(c), S.limites(c)) == Entrada.Pronta{s, r} : Entrada.PreAutenticacao},
  autenticou: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>}) ->
  {H.decidir(c, entrada, be, dados) == H.Executada{r, ctx, xs, p, H.Completa{proxima}} : H.Caso}:
  %Equal.sym(H.DadosFerramentas, dados, H.DadosFerramentas{H.Aceitou{}, H.Finalizou{xs, p}, H.Limpa{}, H.Completa{proxima}, H.Normal{}}, ferramentas) :
    {H.decidir(c, entrada, be, _) == H.Executada{r, ctx, xs, p, H.Completa{proxima}} : H.Caso}
  Equal.trans(H.Caso, H.decidir(c, entrada, be, H.DadosFerramentas{H.Aceitou{}, H.Finalizou{xs, p}, H.Limpa{}, H.Completa{proxima}, H.Normal{}}),
    H.decidir_enquadramento(H.Normal{}, X.decidir_recepcao(c, entrada), be, S.esquema(c), S.limites(c), H.DadosFerramentas{H.Aceitou{}, H.Finalizou{xs, p}, H.Limpa{}, H.Completa{proxima}, H.Normal{}}),
    H.Executada{r, ctx, xs, p, H.Completa{proxima}}, Dois.decidir_por_recepcao(c, entrada, be, H.DadosFerramentas{H.Aceitou{}, H.Finalizou{xs, p}, H.Limpa{}, H.Completa{proxima}, H.Normal{}}),
    (%Equal.sym(X.Disposicao, X.decidir_recepcao(c, entrada), X.ProcessarCorpo{br}, recebeu) :
      {H.decidir_disposicao(_, be, S.esquema(c), S.limites(c), H.DadosFerramentas{H.Aceitou{}, H.Finalizou{xs, p}, H.Limpa{}, H.Completa{proxima}, H.Normal{}}) == H.Executada{r, ctx, xs, p, H.Completa{proxima}} : H.Caso}
    %Equal.sym(Maybe<&2, List<&2, U32>>, Transporte.juntar(be, br), Some{bs}, montou) :
      {H.decidir_pacote(_, S.esquema(c), S.limites(c), H.DadosFerramentas{H.Aceitou{}, H.Finalizou{xs, p}, H.Limpa{}, H.Completa{proxima}, H.Normal{}}) == H.Executada{r, ctx, xs, p, H.Completa{proxima}} : H.Caso}
    %Equal.sym(Entrada.PreAutenticacao, Entrada.decodificar(bs, S.esquema(c), S.limites(c)), Entrada.Pronta{s, r}, decodificou) :
      {H.decidir_pre(_, H.DadosFerramentas{H.Aceitou{}, H.Finalizou{xs, p}, H.Limpa{}, H.Completa{proxima}, H.Normal{}}) == H.Executada{r, ctx, xs, p, H.Completa{proxima}} : H.Caso}
    %Equal.sym(Maybe<&2, D.Contexto>, D.autenticar(s, I.credencial(r)), Some{ctx}, autenticou) :
      {H.decidir_identidade(_, r, H.DadosFerramentas{H.Aceitou{}, H.Finalizou{xs, p}, H.Limpa{}, H.Completa{proxima}, H.Normal{}}) == H.Executada{r, ctx, xs, p, H.Completa{proxima}} : H.Caso}
    {==}))

def aplicar_retorno_da_pronta(~fonte: Fonte.Fonte, ~c: S.Configuracao, +origem: Fonte.JuizoSintatico,
  +s: D.Estado, +r: P.Requisicao, +ctx: D.Contexto, +dados: H.DadosFerramentas,
  retornos: RetornosNoPre(fonte, c, origem, dados, Entrada.Pronta{s, r}),
  autenticou: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>}) ->
  L.E<Fonte.JuizoClienteReal(fonte, c, r, ctx, origem, H.juizo_de(dados)), RetornoNativo(fonte, c, origem, s, r, ctx, saida(dados), limpeza(dados))>:
  retornos(ctx, autenticou)

def retornos_da_requisicao(~fonte: Fonte.Fonte, ~c: S.Configuracao, +origem: Fonte.JuizoSintatico,
  +s: D.Estado, +entrada: X.Recepcao, +be: List<&2, U32>, +br: List<&2, U32>, +bs: List<&2, U32>,
  +r: P.Requisicao, +ctx: D.Contexto, +dados: H.DadosFerramentas,
  recebeu: {X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{br} : X.Disposicao},
  montou: {Transporte.juntar(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>},
  decodificou: {Entrada.decodificar(bs, S.esquema(c), S.limites(c)) == Entrada.Pronta{s, r} : Entrada.PreAutenticacao},
  autenticou: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>},
  retornos: RetornosNaDisposicao(fonte, c, origem, be, dados, X.decidir_recepcao(c, entrada))) ->
  L.E<Fonte.JuizoClienteReal(fonte, c, r, ctx, origem, H.juizo_de(dados)), RetornoNativo(fonte, c, origem, s, r, ctx, saida(dados), limpeza(dados))>:
  aplicar_retorno_da_pronta(fonte, c, origem, s, r, ctx, dados,
    (%decodificou : RetornosNoPre(fonte, c, origem, dados, _)
      %montou : RetornosNoPacote(fonte, c, origem, dados, _)
      %recebeu : RetornosNaDisposicao(fonte, c, origem, be, dados, _) retornos), autenticou)

def AdmitidoNoTraco(~fonte: Fonte.Fonte, +origem: Fonte.JuizoSintatico, -p: S.Programa,
  -qs: List<&2, Q.Quadro>, +r: P.Requisicao, +ctx: D.Contexto) -> Type:
  L.E<{p == Fonte.programa(fonte, origem) : S.Programa}, L.E<ExisteQuadro(qs, Q.Aceita{r, ctx}), ExisteQuadro(qs, Q.Comecada{r, ctx})>>

def marcos_com_regresso(~fonte: Fonte.Fonte, ~c: S.Configuracao, +origem: Fonte.JuizoSintatico,
  +m: H.Micro, +mundo: Nat, +s: D.Estado, +entrada: X.Recepcao, +be: List<&2, U32>,
  +r: P.Requisicao, +ctx: D.Contexto, -p: S.Programa, +br: List<&2, U32>, +bs: List<&2, U32>,
  +j: H.Juizo, +ex: H.SaidaExecucao, +li: H.Limpeza, +en: H.Entrega, +pre: H.Preprocessamento, +proxima: Bool,
  recebeu: {X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{br} : X.Disposicao},
  montou: {Transporte.juntar(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>},
  decodificou: {Entrada.decodificar(bs, S.esquema(c), S.limites(c)) == Entrada.Pronta{s, r} : Entrada.PreAutenticacao},
  autenticou: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>},
  normal: {pre == H.Normal{} : H.Preprocessamento}, escrita: {en == H.Completa{proxima} : H.Entrega},
  gate: L.E<{j == H.Aceitou{} : H.Juizo}, L.E<{p == Fonte.programa(fonte, origem) : S.Programa}, RegressoNativo(ex, li)>>) ->
  AdmitidoNoTraco(fonte, origem, p, H.render(m, s, H.decidir(c, entrada, be, H.DadosFerramentas{j, ex, li, en, pre})), r, ctx):
  match gate:
    case L.Ambos{aceitou, L.Ambos{mesmo_programa, (+xs, +preparada, L.Ambos{executou, limpou})}}:
      %Equal.sym(H.Caso, H.decidir(c, entrada, be, H.DadosFerramentas{j, ex, li, en, pre}), H.Executada{r, ctx, xs, preparada, H.Completa{proxima}},
        caso_executado(c, entrada, be, H.DadosFerramentas{j, ex, li, en, pre}, s, r, ctx, br, bs, xs, preparada, proxima,
          ferramentas_exatas(j, ex, li, en, pre, xs, preparada, proxima, aceitou, executou, limpou, escrita, normal), recebeu, montou, decodificou, autenticou)) :
          AdmitidoNoTraco(fonte, origem, p, H.render(m, s, _), r, ctx)
      L.Ambos{mesmo_programa, marcos_da_execucao(m, s, r, ctx, xs, preparada, proxima)}

def admissao_da_montagem(~fonte: Fonte.Fonte, ~c: S.Configuracao, +origem: Fonte.JuizoSintatico,
  +m: H.Micro, +mundo: Nat, +s: D.Estado, +entrada: X.Recepcao, +be: List<&2, U32>,
  +r: P.Requisicao, +ctx: D.Contexto, p: S.Programa, +br: List<&2, U32>, +bs: List<&2, U32>,
  +j: H.Juizo, +ex: H.SaidaExecucao, +li: H.Limpeza, +en: H.Entrega, +pre: H.Preprocessamento, +proxima: Bool,
  +recebeu: {X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{br} : X.Disposicao},
  +montou: {Transporte.juntar(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>},
  +decodificou: {Entrada.decodificar(bs, S.esquema(c), S.limites(c)) == Entrada.Pronta{s, r} : Entrada.PreAutenticacao},
  +autenticou: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>},
  normal: {pre == H.Normal{} : H.Preprocessamento}, escrita: {en == H.Completa{proxima} : H.Entrega}, terminou: JuizoTerminou(j),
  retornos: RetornosNaDisposicao(fonte, c, origem, be, H.DadosFerramentas{j, ex, li, en, pre}, X.decidir_recepcao(c, entrada)),
  funcional: ElaboracaoFuncional(fonte, c), certificado: L.E<I.Vinculado(Fonte.ambiente(fonte), c, I.codigo(r), p),
    I.Deriva(Fonte.ambiente(fonte), c, I.prova(r), R.Certifica(c, I.codigo(r), p, ctx, I.argumentos(r)))>) ->
  AdmitidoNoTraco(fonte, origem, p, H.render(m, s, H.decidir(c, entrada, be, H.DadosFerramentas{j, ex, li, en, pre})), r, ctx):
  F.com_par(AdmitidoNoTraco(fonte, origem, p, H.render(m, s, H.decidir(c, entrada, be, H.DadosFerramentas{j, ex, li, en, pre})), r, ctx),
    Fonte.JuizoClienteReal(fonte, c, r, ctx, origem, j), RetornoNativo(fonte, c, origem, s, r, ctx, ex, li),
    retornos_da_requisicao(fonte, c, origem, s, entrada, be, br, bs, r, ctx, H.DadosFerramentas{j, ex, li, en, pre}, recebeu, montou, decodificou, autenticou, retornos),
    checado => runtime => marcos_com_regresso(fonte, c, origem, m, mundo, s, entrada, be, r, ctx, p, br, bs, j, ex, li, en, pre, proxima,
      recebeu, montou, decodificou, autenticou, normal, escrita, gate_admite_certificado(fonte, c, origem, s, r, ctx, p, j, ex, li, terminou, checado, runtime, funcional, certificado)))

def PacoteDaRequisicao(~c: S.Configuracao, +s: D.Estado, +entrada: X.Recepcao, +be: List<&2, U32>, +r: P.Requisicao) -> Type:
  &br: List<&2, U32> -> &bs: List<&2, U32> -> L.E<{X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{br} : X.Disposicao},
    L.E<{Transporte.juntar(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>},
      {Entrada.decodificar(bs, S.esquema(c), S.limites(c)) == Entrada.Pronta{s, r} : Entrada.PreAutenticacao}>>

def admissao_com_pacote(~fonte: Fonte.Fonte, ~c: S.Configuracao, +origem: Fonte.JuizoSintatico,
  +m: H.Micro, +mundo: Nat, +s: D.Estado, +entrada: X.Recepcao, +be: List<&2, U32>, +dados: H.DadosFerramentas,
  +r: P.Requisicao, +ctx: D.Contexto, p: S.Programa, pacote: PacoteDaRequisicao(c, s, entrada, be, r),
  disponiveis: FerramentasDisponiveis(fonte, c, origem, be, entrada, dados), funcional: ElaboracaoFuncional(fonte, c),
  autenticou: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>},
  certificado: L.E<I.Vinculado(Fonte.ambiente(fonte), c, I.codigo(r), p),
    I.Deriva(Fonte.ambiente(fonte), c, I.prova(r), R.Certifica(c, I.codigo(r), p, ctx, I.argumentos(r)))>) ->
  AdmitidoNoTraco(fonte, origem, p, H.render(m, s, H.decidir(c, entrada, be, dados)), r, ctx):
  match dados:
    case H.DadosFerramentas{+j, +ex, +li, +en, +pre}:
      match pacote:
        case (+br, +bs, L.Ambos{recebeu, L.Ambos{montou, decodificou}}):
          match disponiveis:
            case L.Ambos{normal, L.Ambos{(+proxima, escrita), L.Ambos{terminou, retornos}}}:
              admissao_da_montagem(fonte, c, origem, m, mundo, s, entrada, be, r, ctx, p, br, bs, j, ex, li, en, pre, proxima,
                recebeu, montou, decodificou, autenticou, normal, escrita, terminou, retornos, funcional, certificado)

def AdmissaoDaChamada(~fonte: Fonte.Fonte, ~c: S.Configuracao, +s: D.Estado, +entrada: X.Recepcao,
  dados: Fonte.ChamadaData, -p: S.Programa, +r: P.Requisicao, +ctx: D.Contexto) -> Type:
  match dados:
    case Fonte.ChamadaData{cf, origem, pf, tf, be, ferramentas, micro}:
      AdmitidoNoTraco(fonte, origem, p, H.render(micro, s, H.decidir(c, entrada, be, ferramentas)), r, ctx)

def CopiaDoEstado(~c: S.Configuracao, +s: D.Estado, dados: Fonte.ChamadaData) -> Type:
  match dados:
    case Fonte.ChamadaData{cf, origem, pf, tf, be, ferramentas, micro}: Copia.EstadoCopiado(c, s, be)

def admissao_da_metadata(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +entrada: X.Recepcao,
  dados: Fonte.ChamadaData, +r: P.Requisicao, +ctx: D.Contexto, p: S.Programa,
  copiado: CopiaDoEstado(c, s, dados), corpo: Copia.CorpoCopiado(c, entrada), estrutura: {D.estrutura(S.esquema(c), s) == True{} : Bool},
  disponiveis: DisponibilidadeDaChamada(fonte, c, entrada, dados), funcional: ElaboracaoFuncional(fonte, c),
  recebeu: I.RequisicaoRecebida(I.Atender{mundo, c, s, entrada}, r),
  autenticou: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>},
  certificado: L.E<I.Vinculado(Fonte.ambiente(fonte), c, I.codigo(r), p),
    I.Deriva(Fonte.ambiente(fonte), c, I.prova(r), R.Certifica(c, I.codigo(r), p, ctx, I.argumentos(r)))>) ->
  AdmissaoDaChamada(fonte, c, s, entrada, dados, p, r, ctx):
  match dados:
    case Fonte.ChamadaData{cf, +origem, pf, tf, +be, +ferramentas, +micro}:
      admissao_com_pacote(fonte, c, origem, micro, mundo, s, entrada, be, ferramentas, r, ctx, p,
        pacote_de_requisicao_recebida(c, mundo, s, entrada, be, r, copiado, corpo, estrutura, recebeu), disponiveis, funcional, autenticou, certificado)

def admissao_na_fonte(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +entrada: X.Recepcao,
  +dados: Fonte.ChamadaData, +mesma: {dados == Fonte.chamada(fonte, mundo) : Fonte.ChamadaData},
  +r: P.Requisicao, +ctx: D.Contexto, -p: S.Programa,
  canonico: {I.Atender{mundo, c, s, entrada} == Fonte.cenario(fonte, mundo) : I.Cenario},
  admitido: AdmissaoDaChamada(fonte, c, s, entrada, dados, p, r, ctx)) ->
  L.E<I.EmAlgumMomento(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, entrada}, I.CertificadoAceito{r, ctx, p}),
    I.EmAlgumMomento(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, entrada}, I.ProgramaComecou{r, ctx, p})>:
  match dados:
    case Fonte.ChamadaData{+cf, +origem, +pf, +tf, +be, +ferramentas, +micro}:
      match admitido:
        case L.Ambos{mesmo_programa, L.Ambos{(+ta, aceitou), (+tc, comecou)}}:
          %Equal.sym(S.Programa, p, Fonte.programa(fonte, origem), mesmo_programa) :
            L.E<I.EmAlgumMomento(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, entrada}, I.CertificadoAceito{r, ctx, _}),
              I.EmAlgumMomento(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, entrada}, I.ProgramaComecou{r, ctx, _})>
          F.com_par(
            L.E<I.EmAlgumMomento(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, entrada}, I.CertificadoAceito{r, ctx, Fonte.programa(fonte, origem)}),
              I.EmAlgumMomento(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, entrada}, I.ProgramaComecou{r, ctx, Fonte.programa(fonte, origem)})>,
            {I.Atender{mundo, c, s, entrada} == Fonte.cenario(fonte, mundo) : I.Cenario},
            {I.Atender{mundo, c, s, entrada} == Fonte.cenario(fonte, mundo) : I.Cenario},
            Chamada.duplicar_igualdade(I.Cenario, I.Atender{mundo, c, s, entrada}, Fonte.cenario(fonte, mundo), canonico), c1 => c2 => L.Ambos{
              (ta, evento_da_rota(fonte, c, Fonte.Atendimento{mundo, s, entrada}, ta, Q.Aceita{r, ctx}, I.CertificadoAceito{r, ctx, Fonte.programa(fonte, origem)}, c1, Unit{},
                (%mesma : RelacaoDaOrigem(fonte, c, origem_da_observacao(Fonte.construir_chamada(c, s, entrada, _)), Q.Aceita{r, ctx}, I.CertificadoAceito{r, ctx, Fonte.programa(fonte, origem)}) {==}),
                (%mesma : {Q.consultar(quadros(Fonte.construir_chamada(c, s, entrada, _)), ta) == Some{Q.Aceita{r, ctx}} : Maybe<&2, Q.Quadro>} aceitou))),
              (tc, evento_da_rota(fonte, c, Fonte.Atendimento{mundo, s, entrada}, tc, Q.Comecada{r, ctx}, I.ProgramaComecou{r, ctx, Fonte.programa(fonte, origem)}, c2, Unit{},
                (%mesma : RelacaoDaOrigem(fonte, c, origem_da_observacao(Fonte.construir_chamada(c, s, entrada, _)), Q.Comecada{r, ctx}, I.ProgramaComecou{r, ctx, Fonte.programa(fonte, origem)}) {==}),
                (%mesma : {Q.consultar(quadros(Fonte.construir_chamada(c, s, entrada, _)), tc) == Some{Q.Comecada{r, ctx}} : Maybe<&2, Q.Quadro>} comecou)))})

# As duas instancias sao evidencias logicas dos mesmos resultados fixos.
# Nao executam novamente checker/worker nem duplicam o programa linear.
def PrimitivasAtendimento(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +entrada: X.Recepcao) -> Type:
  L.E<DisponibilidadeDaChamada(fonte, c, entrada, Fonte.chamada(fonte, mundo)),
    L.E<DisponibilidadeDaChamada(fonte, c, entrada, Fonte.chamada(fonte, mundo)),
      L.E<CopiaDoEstado(c, s, Fonte.chamada(fonte, mundo)),
        L.E<Copia.CorpoCopiado(c, entrada), ElaboracaoFuncional(fonte, c)>>>>

def ResultadoAtendimento(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +entrada: X.Recepcao) -> Type:
  L.E<K.AtendimentoTermina(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, entrada}),
    @r: P.Requisicao -> @ctx: D.Contexto -> @p: S.Programa ->
      I.RequisicaoRecebida(I.Atender{mundo, c, s, entrada}, r) ->
      {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>} ->
      L.E<I.Vinculado(Fonte.ambiente(fonte), c, I.codigo(r), p),
        I.Deriva(Fonte.ambiente(fonte), c, I.prova(r), R.Certifica(c, I.codigo(r), p, ctx, I.argumentos(r)))> ->
        L.E<I.EmAlgumMomento(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, entrada}, I.CertificadoAceito{r, ctx, p}),
          I.EmAlgumMomento(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, entrada}, I.ProgramaComecou{r, ctx, p})>>

def estrutura_do_estado(c: S.Configuracao, +s: D.Estado, estrutura: {R.estrutura(c, s) == True{} : Bool}) ->
  {D.estrutura(S.esquema(c), s) == True{} : Bool}:
  match c:
    case S.Configuracao{+e, ls, +lim, amb}:
      F.e_booleano_esquerda(D.estrutura(e, s), R.cabe(R.limite_estado(lim), D.estado_valor(s)), estrutura)

def atendimento_primitivo(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +entrada: X.Recepcao,
  canonico: {I.Atender{mundo, c, s, entrada} == Fonte.cenario(fonte, mundo) : I.Cenario},
  configuracao: I.ConfiguracaoValida(Fonte.ambiente(fonte), c), valido: R.Valido(c, s), primitivas: PrimitivasAtendimento(fonte, c, mundo, s, entrada)) ->
  ResultadoAtendimento(fonte, c, mundo, s, entrada):
  match configuracao valido primitivas:
    case L.Ambos{cfg, id} L.Ambos{estrutura, leis} L.Ambos{fim, L.Ambos{admissao, L.Ambos{copiado, L.Ambos{corpo, funcional}}}}:
      F.com_par(ResultadoAtendimento(fonte, c, mundo, s, entrada),
        {I.Atender{mundo, c, s, entrada} == Fonte.cenario(fonte, mundo) : I.Cenario},
        {I.Atender{mundo, c, s, entrada} == Fonte.cenario(fonte, mundo) : I.Cenario},
        Chamada.duplicar_igualdade(I.Cenario, I.Atender{mundo, c, s, entrada}, Fonte.cenario(fonte, mundo), canonico), c1 => c2 => L.Ambos{
          terminar_da_fonte(fonte, c, mundo, s, entrada, c1,
            fim_da_chamada(fonte, c, mundo, s, entrada, Fonte.chamada(fonte, mundo), {==}, Preparacao.limites_da_configuracao(c, cfg), fim)),
          +r => +ctx => p => recebeu => autenticou => certificado =>
            admissao_na_fonte(fonte, c, mundo, s, entrada, Fonte.chamada(fonte, mundo), {==}, r, ctx, p, c2,
              admissao_da_metadata(fonte, c, mundo, s, entrada, Fonte.chamada(fonte, mundo), r, ctx, p,
                copiado, corpo, estrutura_do_estado(c, s, estrutura), admissao, funcional, recebeu, autenticou, certificado))})

# Inicializacao usa somente aprovacao/retorno reais do checker e worker.
def PrimitivasInicial(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +pi: String) -> Type:
  I.Deriva(Fonte.ambiente(fonte), c, pi, R.Valido(c, s)) ->
    &cf: Fonte.JuizoSintatico -> &sf: Fonte.JuizoSintatico -> &pf: Fonte.JuizoSintatico -> &micro: H.Micro ->
      {Fonte.inicial(fonte, mundo) == Fonte.InicialData{cf, sf, pf, H.Aceitou{}, H.Finalizada{}, micro} : Fonte.InicialData}

def inicio_primitivo_resultado(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +pi: String,
  canonico: {I.Inicializar{mundo, c, s, pi} == Fonte.cenario(fonte, mundo) : I.Cenario},
  configurada: {Config.valida(c, Fonte.identidade(fonte)) == True{} : Bool}, valido: R.Valido(c, s),
  resultado: &cf: Fonte.JuizoSintatico -> &sf: Fonte.JuizoSintatico -> &pf: Fonte.JuizoSintatico -> &micro: H.Micro ->
    {Fonte.inicial(fonte, mundo) == Fonte.InicialData{cf, sf, pf, H.Aceitou{}, H.Finalizada{}, micro} : Fonte.InicialData}) ->
  I.EmAlgumMomento(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, I.InstanciaIniciou{s}):
  match resultado:
    case (+cf, +sf, +pf, +micro, origem):
      Fonte.inicializacao_aprovada_atinge_inicio(fonte, c, mundo, s, pi, cf, sf, pf, micro, canonico, origem, configurada, valido)

def inicial_primitivo(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +pi: String,
  canonico: {I.Inicializar{mundo, c, s, pi} == Fonte.cenario(fonte, mundo) : I.Cenario},
  condicoes: K.InicializacaoPossivel(Fonte.ambiente(fonte), c, s, pi), primitivas: PrimitivasInicial(fonte, c, mundo, s, pi)) ->
  I.EmAlgumMomento(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, I.InstanciaIniciou{s}):
  match condicoes:
    case L.Ambos{configuracao, L.Ambos{derivada, valido}}:
      inicio_primitivo_resultado(fonte, c, mundo, s, pi, canonico,
        Configuracao.configuracao_original_valida_e_aceita(Fonte.ambiente(fonte), c, configuracao), valido, primitivas(derivada))

# Separacao das condicoes e da consequencia da Lei8, preservando seu texto.
def Condicoes(~fonte: Fonte.Fonte, x: I.Cenario) -> Type:
  match x:
    case I.Inicializar{m, c, s, pi}: K.InicializacaoPossivel(Fonte.ambiente(fonte), c, s, pi)
    case I.Atender{m, c, s, entrada}: L.E<I.ConfiguracaoValida(Fonte.ambiente(fonte), c), L.E<R.Valido(c, s), X.RecepcaoValida(entrada)>>

def Resultado(~fonte: Fonte.Fonte, x: I.Cenario) -> Type:
  match x:
    case I.Inicializar{m, c, +s, pi}: I.EmAlgumMomento(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{m, c, s, pi}, I.InstanciaIniciou{s})
    case I.Atender{+m, c, +s, +entrada}:
      L.E<K.AtendimentoTermina(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{m, c, s, entrada}),
        @r: P.Requisicao -> @ctx: D.Contexto -> @p: S.Programa ->
          I.RequisicaoRecebida(I.Atender{m, c, s, entrada}, r) ->
          {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>} ->
          L.E<I.Vinculado(Fonte.ambiente(fonte), c, I.codigo(r), p),
            I.Deriva(Fonte.ambiente(fonte), c, I.prova(r), R.Certifica(c, I.codigo(r), p, ctx, I.argumentos(r)))> ->
              L.E<I.EmAlgumMomento(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{m, c, s, entrada}, I.CertificadoAceito{r, ctx, p}),
                I.EmAlgumMomento(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{m, c, s, entrada}, I.ProgramaComecou{r, ctx, p})>>

def PrimitivasDoContexto(~fonte: Fonte.Fonte, ~c: S.Configuracao, x: Fonte.Contexto) -> Type:
  match x:
    case Fonte.Inicial{+m, +s, +pi}: PrimitivasInicial(fonte, c, m, s, pi)
    case Fonte.Atendimento{+m, +s, +entrada}: PrimitivasAtendimento(fonte, c, m, s, entrada)

def progresso_no_contexto(~fonte: Fonte.Fonte, ~c: S.Configuracao, +x: Fonte.Contexto,
  canonico: {Fonte.cenario_contexto(c, x) == Fonte.cenario(fonte, Fonte.mundo(Fonte.cenario_contexto(c, x))) : I.Cenario},
  condicoes: Condicoes(fonte, Fonte.cenario_contexto(c, x)), primitivas: PrimitivasDoContexto(fonte, c, x)) ->
  Resultado(fonte, Fonte.cenario_contexto(c, x)):
  match x:
    case Fonte.Inicial{+m, +s, +pi}: inicial_primitivo(fonte, c, m, s, pi, canonico, condicoes, primitivas)
    case Fonte.Atendimento{+m, +s, +entrada}:
      match condicoes:
        case L.Ambos{configuracao, L.Ambos{valido, recepcao}}: atendimento_primitivo(fonte, c, m, s, entrada, canonico, configuracao, valido, primitivas)

def PrimitivasDoModelo(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String, +mundo: Nat) -> Type:
  PrimitivasDoContexto(Modelo.fonte(base, c, seed, historico, momento, pi), c,
    Dois.contexto_do_momento(seed, historico, pi, mundo, momento(mundo)))

# Contrato externo de disponibilidade: coerencia do cenario e retornos de
# primitivas. Processavel continua sendo exatamente o predicado da base.
def DisponibilidadeDoModelo(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String) -> Type:
  @x: I.Cenario -> I.Processavel(Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momento, pi)), x) ->
    L.E<{x == Fonte.cenario(Modelo.fonte(base, c, seed, historico, momento, pi), Fonte.mundo(x)) : I.Cenario},
      PrimitivasDoModelo(base, c, seed, historico, momento, pi, Fonte.mundo(x))>

def progresso_por_igualdade_do_contexto(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +x: Fonte.Contexto,
  mundo_igual: {Fonte.mundo(Fonte.cenario_contexto(c, x)) == mundo : Nat},
  igual: {Fonte.cenario_contexto(c, x) == Fonte.cenario(fonte, mundo) : I.Cenario},
  condicoes: Condicoes(fonte, Fonte.cenario(fonte, mundo)), primitivas: PrimitivasDoContexto(fonte, c, x)) ->
  Resultado(fonte, Fonte.cenario(fonte, mundo)):
  F.com_par(Resultado(fonte, Fonte.cenario(fonte, mundo)),
    {Fonte.cenario_contexto(c, x) == Fonte.cenario(fonte, mundo) : I.Cenario},
    {Fonte.cenario_contexto(c, x) == Fonte.cenario(fonte, mundo) : I.Cenario},
    Chamada.duplicar_igualdade(I.Cenario, Fonte.cenario_contexto(c, x), Fonte.cenario(fonte, mundo), igual), i1 => i2 =>
      Cinco.aplicar(Condicoes(fonte, Fonte.cenario(fonte, mundo)), Resultado(fonte, Fonte.cenario(fonte, mundo)),
        (%i1 : Condicoes(fonte, _) -> Resultado(fonte, _)
          cs => progresso_no_contexto(fonte, c, x, Dois.mesmo_mundo_do_contexto(fonte, c, mundo, x, mundo_igual, i2), cs, primitivas)), condicoes))

def progresso_no_canonico(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String, +mundo: Nat,
  condicoes: Condicoes(Modelo.fonte(base, c, seed, historico, momento, pi), Fonte.cenario(Modelo.fonte(base, c, seed, historico, momento, pi), mundo)),
  primitivas: PrimitivasDoModelo(base, c, seed, historico, momento, pi, mundo)) ->
  Resultado(Modelo.fonte(base, c, seed, historico, momento, pi), Fonte.cenario(Modelo.fonte(base, c, seed, historico, momento, pi), mundo)):
  progresso_por_igualdade_do_contexto(Modelo.fonte(base, c, seed, historico, momento, pi), c, mundo,
    Dois.contexto_do_momento(seed, historico, pi, mundo, momento(mundo)),
    Dois.contexto_conserva_mundo(c, seed, historico, pi, mundo, momento(mundo)),
    Equal.trans(I.Cenario,
      Fonte.cenario_contexto(c, Dois.contexto_do_momento(seed, historico, pi, mundo, momento(mundo))),
      Cenarios.canonico(c, seed, historico, momento, pi, mundo), Fonte.cenario(Modelo.fonte(base, c, seed, historico, momento, pi), mundo),
      Dois.contexto_representa_cenario(c, seed, historico, pi, mundo, momento(mundo)),
      Equal.sym(I.Cenario, Fonte.cenario(Modelo.fonte(base, c, seed, historico, momento, pi), mundo), Cenarios.canonico(c, seed, historico, momento, pi, mundo),
        Modelo.cenario_do_modelo(base, c, seed, historico, momento, pi, mundo))), condicoes, primitivas)

def resultado_apos_coerencia(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String,
  -x: I.Cenario, +mundo: Nat,
  condicoes: Condicoes(Modelo.fonte(base, c, seed, historico, momento, pi), x),
  origem: L.E<{x == Fonte.cenario(Modelo.fonte(base, c, seed, historico, momento, pi), mundo) : I.Cenario},
    PrimitivasDoModelo(base, c, seed, historico, momento, pi, mundo)>) ->
  Resultado(Modelo.fonte(base, c, seed, historico, momento, pi), x):
  match origem:
    case L.Ambos{igual, primitivas}:
      Cinco.aplicar(Condicoes(Modelo.fonte(base, c, seed, historico, momento, pi), x),
        Resultado(Modelo.fonte(base, c, seed, historico, momento, pi), x),
        (%Equal.sym(I.Cenario, x, Fonte.cenario(Modelo.fonte(base, c, seed, historico, momento, pi), mundo), igual) :
          Condicoes(Modelo.fonte(base, c, seed, historico, momento, pi), _) -> Resultado(Modelo.fonte(base, c, seed, historico, momento, pi), _)
          cs => progresso_no_canonico(base, c, seed, historico, momento, pi, mundo, cs, primitivas)), condicoes)

def progresso_do_cenario(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String,
  disponibilidade: DisponibilidadeDoModelo(base, c, seed, historico, momento, pi), x: I.Cenario) ->
  K.Progresso(x, Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momento, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi))):
  match x:
    case I.Inicializar{+m, original, +s, +prova}:
      possivel => processavel => resultado_apos_coerencia(base, c, seed, historico, momento, pi, I.Inicializar{m, original, s, prova}, m,
        possivel, disponibilidade(I.Inicializar{m, original, s, prova}, processavel))
    case I.Atender{+m, original, +s, +entrada}:
      configuracao => valido => recepcao => processavel =>
        resultado_apos_coerencia(base, c, seed, historico, momento, pi, I.Atender{m, original, s, entrada}, m,
          L.Ambos{configuracao, L.Ambos{valido, recepcao}}, disponibilidade(I.Atender{m, original, s, entrada}, processavel))

# Lei8 EXATA: nao recebe Progresso, Concluiu ou Started como premissa.
def lei8_do_modelo(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String,
  disponibilidade: DisponibilidadeDoModelo(base, c, seed, historico, momento, pi)) ->
  K.Lei8(Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momento, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi))):
  x => progresso_do_cenario(base, c, seed, historico, momento, pi, disponibilidade, x)
