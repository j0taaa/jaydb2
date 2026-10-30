# Ligacoes de campos observados; a conferencia vem do gerador real do Codec.
import Base
import ./FonteServico.bend as Fonte
import ./RotasServico.bend as Rota
import ../contrato/Recursos.bend as X
import ../contrato/Bytes.bend as B
import ../contrato/Protocolo.bend as P
import ../src/Codec.bend as Codec
import ./PrimitivasServico.bend as M
import ./CodecLei2.bend as CodecLei2
import ./CodecRecusas.bend as Recusas
import ./Representacao.bend as Representacao
import ./Fundamentos.bend as Fundamentos
import ../src/Estado.bend as Estado
import ../contrato/Dados.bend as D
import ../contrato/Interface.bend as I
import ../contrato/LAWS.bend as K
import ../contrato/Logica.bend as L
import ../contrato/Semantica.bend as S
import ../contrato/Requisitos.bend as Requisitos
import ./CamposServico.bend as C
import ./ProtocoloServico.bend as Q
import ./ExecucaoServico.bend as E
import ./Lei5Servico.bend as Cinco
import ./RecepcaoLimites.bend as Leitura
import ./ModeloServico.bend as Modelo
import ./CenariosServico.bend as Cenarios
import ./HistoricoServico.bend as Historico
import ./Chamada.bend as Chamada
import ../src/Nucleo.bend as N
import ../src/Entrada.bend as Entrada
import ../src/Transporte.bend as Transporte
import ../src/Configuracao.bend as Configuracao

# Testemunhas locais de ordem, depois levantadas ao ambiente da fonte.
def Antes(-ob: Nat -> I.Fato -> Type, -t: Nat, -f: I.Fato) -> Type:
  &b: Nat -> L.E<{Nat.is_lt(b, t) == True{} : Bool}, ob(b, f)>

# Conteudo dos fatos puros. Leituras e ordem sao tratadas separadamente.
def Conteudo(~c: S.Configuracao, +x: Fonte.Contexto, q: Q.Quadro) -> Type:
  match q:
    case Q.Codificada{v, bs}: {bs == P.codificar(v) : Maybe<&2, List<&2, U32>>}
    case Q.Decodificada{bs, v}: I.DecodificacaoCorreta(bs, v)
    case Q.Guardada{s, bs, abstr}: {abstr == s : D.Estado}
    case Q.Operada{e, s, o, r}: {r == D.operar(e, s, o) : D.ResultadoOp}
    case Q.Recebida{r}: I.RequisicaoRecebida(Fonte.cenario_contexto(c, x), r)
    case Q.Lida{antes, n, declarado}: K.LeituraLimitada(Fonte.cenario_contexto(c, x), antes, n, declarado)
    case _: Unit

def Conteudos(~c: S.Configuracao, +x: Fonte.Contexto, qs: List<&2, Q.Quadro>) -> Type:
  match qs:
    case Nil{}: Unit
    case Con{h, t}: L.E<Conteudo(c, x, h), Conteudos(c, x, t)>

def concatenar_conteudos(~c: S.Configuracao, +x: Fonte.Contexto, xs: List<&2, Q.Quadro>, -ys: List<&2, Q.Quadro>, a: Conteudos(c, x, xs), b: Conteudos(c, x, ys)) ->
  Conteudos(c, x, Q.concatenar(xs, ys)):
  match xs a:
    case Nil{} _: b
    case Con{h, t} L.Ambos{cabeca, cauda}: L.Ambos{cabeca, concatenar_conteudos(c, x, t, ys, cauda, b)}

def construir_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, conferencia: Codec.Conferencia, -pos: Nat, -n: Nat) -> Conteudos(c, x, M.construir(conferencia, pos, n)):
  match conferencia:
    case Codec.Cabe{}: L.Ambos{Unit{}, L.Ambos{Unit{}, Unit{}}}
    case Codec.Curto{}: Unit{}
    case Codec.Grande{}: Unit{}

def abertura_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, conferencia: Codec.Conferencia, pronto: Bool, -pos: Nat, -n: Nat) ->
  Conteudos(c, x, M.abrir_campo(conferencia, pronto, pos, n)):
  match conferencia pronto:
    case Codec.Cabe{} True{}: construir_conteudo(c, x, Codec.Cabe{}, pos, n)
    case Codec.Cabe{} False{}: L.Ambos{Unit{}, Unit{}}
    case Codec.Curto{} _: Unit{}
    case Codec.Grande{} _: Unit{}

def campo_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, +pos: Nat, +f: Codec.Finalidade, +alto: U32, +baixo: U32,
  +pilha: Codec.Pilha, +corpo: B.Numero64, +teto: B.Numero64) ->
  Conteudos(c, x, M.quadro_campo(pos, f, alto, baixo, pilha, corpo, teto)):
  abertura_conteudo(c, x, M.conferencia(f, alto, baixo, pilha, corpo, teto), M.abrir_nome_valido(f, alto, baixo), pos, M.quantidade(alto, baixo))

def tag_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, tag: Nat, -pos: Nat) -> Conteudos(c, x, M.quadro_tag(tag, pos)):
  match tag:
    case 0n: construir_conteudo(c, x, Codec.Cabe{}, pos, 1n)
    case 1n: construir_conteudo(c, x, Codec.Cabe{}, pos, 1n)
    case 2n: construir_conteudo(c, x, Codec.Cabe{}, pos, 1n)
    case 3n+k: Unit{}

def palavra_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, f: Codec.Finalidade, +alto: U32, +baixo: U32, +pilha: Codec.Pilha,
  +corpo: B.Numero64, +teto: B.Numero64, +pos: Nat) -> Conteudos(c, x, M.quadro_palavra(f, alto, baixo, pilha, corpo, teto, pos)):
  match f:
    case Codec.Inteiro{}: construir_conteudo(c, x, Codec.Cabe{}, pos, 8n)
    case Codec.Texto{}: campo_conteudo(c, x, pos, Codec.Texto{}, alto, baixo, pilha, corpo, teto)
    case Codec.NomeTexto{}: campo_conteudo(c, x, pos, Codec.NomeTexto{}, alto, baixo, pilha, corpo, teto)
    case Codec.ContaLista{}: campo_conteudo(c, x, pos, Codec.ContaLista{}, alto, baixo, pilha, corpo, teto)
    case Codec.ContaRegistro{}: campo_conteudo(c, x, pos, Codec.ContaRegistro{}, alto, baixo, pilha, corpo, teto)

def passo_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, m: Codec.Maquina, +b: U32, +corpo: B.Numero64, +teto: B.Numero64, +pos: Nat) ->
  Conteudos(c, x, M.quadro_passo(m, b, corpo, teto, pos)):
  match m:
    case Codec.Tag{pilha}: tag_conteudo(c, x, U32.to_nat(b), pos)
    case Codec.Palavra{f, 0n, alto, +baixo, pilha}:
      palavra_conteudo(c, x, f, (alto * 256 + U32.shrn(baixo, 24n) : U32), (baixo * 256 + b : U32), pilha, corpo, teto, pos)
    case Codec.Palavra{f, 1n+k, alto, baixo, pilha}: Unit{}
    case Codec.TagNome{pilha}: Unit{}
    case Codec.Conteudo{nome, ultimo, q, u, texto, pilha}: Unit{}
    case Codec.Pronto{v}: Unit{}
    case Codec.Invalido{}: Unit{}
    case Codec.Acima{}: Unit{}

law conteudo_do_parser_vem_das_funcoes_reais:
  for ~c: S.Configuracao
  for +x: Fonte.Contexto
  for bs: List<&2, U32>
  for +m: Codec.Maquina
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +pos: Nat
  Conteudos(c, x, M.quadros_codec(bs, m, corpo, teto, pos))
def conteudo_do_parser_vem_das_funcoes_reais(c, x, bs, m, corpo, teto, pos):
  match bs:
    case Nil{}: Unit{}
    case Con{+b, +t}:
      concatenar_conteudos(c, x, M.quadro_passo(m, b, Codec.diminuir64(corpo), Codec.diminuir64(teto), pos),
        M.quadros_codec(t, Codec.passo(m, b, Codec.diminuir64(corpo), Codec.diminuir64(teto)), Codec.diminuir64(corpo), Codec.diminuir64(teto), Succ{pos}),
        passo_conteudo(c, x, m, b, Codec.diminuir64(corpo), Codec.diminuir64(teto), pos),
        conteudo_do_parser_vem_das_funcoes_reais(c, x, t, Codec.passo(m, b, Codec.diminuir64(corpo), Codec.diminuir64(teto)), Codec.diminuir64(corpo), Codec.diminuir64(teto), Succ{pos}))

def decodificacao_admitida_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, ok: Bool, +bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64,
  medido: {B.nat64(B.comprimento(bs)) == Some{corpo} : Maybe<&2, B.Numero64>},
  decisao: {Codec.menor_igual64(corpo, teto) && B.octetos_validos(bs) == ok : Bool}) ->
  Conteudos(c, x, M.decodificacao_admitida(ok, bs, corpo, teto)):
  match ok:
    case False{}: Unit{}
    case True{}:
      concatenar_conteudos(c, x, M.quadros_codec(bs, Codec.Tag{Codec.Raiz{}}, corpo, teto, 0n),
        [Q.Decodificada{bs, Recusas.opcional(Codec.decodificar(bs, teto))}],
        conteudo_do_parser_vem_das_funcoes_reais(c, x, bs, Codec.Tag{Codec.Raiz{}}, corpo, teto, 0n),
        L.Ambos{CodecLei2.decodificar_satisfaz_relacao_original(bs, corpo, teto, medido,
          Fundamentos.e_booleano_esquerda(Codec.menor_igual64(corpo, teto), B.octetos_validos(bs), decisao)), Unit{}})

def decodificacao_medida_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, q: Maybe<&2, B.Numero64>, +bs: List<&2, U32>, +teto: B.Numero64,
  medida: {B.nat64(B.comprimento(bs)) == q : Maybe<&2, B.Numero64>}) -> Conteudos(c, x, M.decodificacao_medida(q, bs, teto)):
  match q:
    case None{}: Unit{}
    case Some{+corpo}:
      decodificacao_admitida_conteudo(c, x, Codec.menor_igual64(corpo, teto) && B.octetos_validos(bs), bs, corpo, teto, medida, {==})

def armazenamento_abstrato_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, q: Maybe<&2, D.Estado>, +s: D.Estado, -bs: List<&2, U32>,
  exato: {q == Some{s} : Maybe<&2, D.Estado>}) -> Conteudos(c, x, M.guardar_abstracao(q, s, bs)):
  match q:
    case None{}: Unit{}
    case Some{a}:
      L.Ambos{Fundamentos.algum_injetivo(D.Estado, a, s, exato), Unit{}}

def armazenamento_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, q: Maybe<&2, List<&2, U32>>, +e: D.Esquema, +s: D.Estado,
  estrutura: {D.estrutura(e, s) == True{} : Bool}) -> Conteudos(c, x, M.guardar_bytes(q, e, s)):
  match q:
    case None{}: Unit{}
    case Some{bs}: armazenamento_abstrato_conteudo(c, x, Estado.decodificar(D.estado_valor(s), e), s, bs,
      Representacao.transporte_privado_preserva_estado(e, s, estrutura))

def primeiros_conteudos(~c: S.Configuracao, +x: Fonte.Contexto, n: Nat, qs: List<&2, Q.Quadro>, conteudos: Conteudos(c, x, qs)) -> Conteudos(c, x, Q.primeiros(n, qs)):
  match n qs:
    case 0n _: Unit{}
    case 1n+k Nil{}: Unit{}
    case 1n+k Con{h, t}:
      match conteudos:
        case L.Ambos{cabeca, cauda}: L.Ambos{cabeca, primeiros_conteudos(c, x, k, t, cauda)}

def CabecalhoMedido(entrada: X.Recepcao, -declarado: Nat) -> Type:
  match entrada:
    case X.BodyTruncado{alto, baixo, corpo}: {B.nat64(declarado) == Some{B.Numero64{alto, baixo}} : Maybe<&2, B.Numero64>}
    case X.CorpoRecebido{alto, baixo, corpo}: {B.nat64(declarado) == Some{B.Numero64{alto, baixo}} : Maybe<&2, B.Numero64>}
    case _: Empty

def LeituraReal(~c: S.Configuracao, +x: Fonte.Contexto, -antes: Nat, -cap: Nat, -recebido: Nat, -declarado: Nat) -> Type:
  match x:
    case Fonte.Inicial{mundo, s, pi}: Empty
    case Fonte.Atendimento{mundo, s, entrada}:
      L.E<CabecalhoMedido(entrada, declarado),
        L.E<{Nat.is_le(antes, declarado) == True{} : Bool},
          L.E<{Nat.is_le(recebido, Nat.min(cap, Nat.sub(declarado, antes))) == True{} : Bool},
            {Nat.is_le(declarado, Requisitos.limite_mensagem(S.limites(c))) == True{} : Bool}>>>

def declaracao_medida(~c: S.Configuracao, entrada: X.Recepcao, +declarado: Nat, medida: CabecalhoMedido(entrada, declarado)) ->
  K.ComprimentoDeclarado(entrada, declarado):
  match entrada:
    case X.BodyTruncado{+alto, +baixo, corpo}: Leitura.cabecalho_medido_estabelece_declaracao_original(alto, baixo, declarado, medida)
    case X.CorpoRecebido{+alto, +baixo, corpo}: Leitura.cabecalho_medido_estabelece_declaracao_original(alto, baixo, declarado, medida)
    case X.EOFEntreMensagens{}: medida
    case X.ParadaOperador{}: medida
    case X.HeaderTruncado{bs}: medida

def leitura_tem_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, +antes: Nat, +cap: Nat, +recebido: Nat, +declarado: Nat,
  real: LeituraReal(c, x, antes, cap, recebido, declarado)) -> K.LeituraLimitada(Fonte.cenario_contexto(c, x), antes, recebido, declarado):
  match x:
    case Fonte.Inicial{mundo, s, pi}: L.ex_falso(K.LeituraLimitada(I.Inicializar{mundo, c, s, pi}, antes, recebido, declarado), real)
    case Fonte.Atendimento{mundo, s, +entrada}:
      match real:
        case L.Ambos{medida, L.Ambos{existente, L.Ambos{real, admitido}}}:
          L.Ambos{declaracao_medida(c, entrada, declarado, medida),
            Leitura.consumo_confirmado_respeita_declarado_e_limite(declarado, antes, cap, recebido,
              Requisitos.limite_mensagem(S.limites(c)), existente, real, admitido)}

# Apenas o pre-requisito concreto do decoder de armazenamento e solicitado.
# A validade publicada e derivada do historico e do certificado, nao deste tipo.
# Guardar nao e um teste em cada mutacao privada; estados de trabalho com
# credenciais vazias/duplicadas nao passam por este decoder de snapshot.
def OrigemPrimitiva(~c: S.Configuracao, +x: Fonte.Contexto, q: M.Primitiva) -> Type:
  match q:
    case M.Prefixo{n, p}: OrigemPrimitiva(c, x, p)
    case M.Guardar{e, s}: {D.estrutura(e, s) == True{} : Bool}
    case M.Ler{antes, cap, recebido, declarado}: LeituraReal(c, x, antes, cap, recebido, declarado)
    case _: Unit

law primitivas_produzem_conteudo_exato:
  for ~c: S.Configuracao
  for +x: Fonte.Contexto
  for q: M.Primitiva
  for origem: OrigemPrimitiva(c, x, q)
  Conteudos(c, x, M.expandir(q))
def primitivas_produzem_conteudo_exato(c, x, q, origem):
  match q:
    case M.Prefixo{n, +p}: primeiros_conteudos(c, x, n, M.expandir(p), primitivas_produzem_conteudo_exato(c, x, p, origem))
    case M.Codificar{v}: L.Ambos{{==}, Unit{}}
    case M.Decodificar{+bs, +teto}: decodificacao_medida_conteudo(c, x, B.nat64(B.comprimento(bs)), bs, teto, {==})
    case M.Guardar{e, +s}: armazenamento_conteudo(c, x, P.codificar(D.estado_valor(s)), e, s, origem)
    case M.Ler{+antes, +cap, +recebido, +declarado}:
      L.Ambos{leitura_tem_conteudo(c, x, antes, cap, recebido, declarado, origem), Unit{}}

def OrigensPrimitivas(~c: S.Configuracao, +x: Fonte.Contexto, ps: List<&2, M.Primitiva>) -> Type:
  match ps:
    case Nil{}: Unit
    case Con{h, t}: L.E<OrigemPrimitiva(c, x, h), OrigensPrimitivas(c, x, t)>

law conteudo_de_todas_primitivas_e_exato:
  for ~c: S.Configuracao
  for +x: Fonte.Contexto
  for ps: List<&2, M.Primitiva>
  for origem: OrigensPrimitivas(c, x, ps)
  Conteudos(c, x, M.expandir_primitivas(ps))
def conteudo_de_todas_primitivas_e_exato(c, x, ps, origem):
  match ps origem:
    case Nil{} _: Unit{}
    case Con{+h, +t} L.Ambos{cabeca, cauda}:
      concatenar_conteudos(c, x, M.expandir(h), M.expandir_primitivas(t),
        primitivas_produzem_conteudo_exato(c, x, h, cabeca), conteudo_de_todas_primitivas_e_exato(c, x, t, cauda))

law conteudo_da_consulta:
  for ~c: S.Configuracao
  for +x: Fonte.Contexto
  for qs: List<&2, Q.Quadro>
  for t: Nat
  for -q: Q.Quadro
  for conteudos: Conteudos(c, x, qs)
  for consulta: {Q.consultar(qs, t) == Some{q} : Maybe<&2, Q.Quadro>}
  Conteudo(c, x, q)
def conteudo_da_consulta(c, x, qs, t, q, conteudos, consulta):
  match qs t:
    case Nil{} _: L.ex_falso(Conteudo(c, x, q), Fundamentos.nenhum_nao_algum(Q.Quadro, q, consulta))
    case Con{+h, resto} 0n:
      match conteudos:
        case L.Ambos{cabeca, cauda}:
          %Fundamentos.algum_injetivo(Q.Quadro, h, q, consulta) : Conteudo(c, x, _)
          cabeca
    case Con{h, resto} 1n+n:
      match conteudos:
        case L.Ambos{cabeca, cauda}: conteudo_da_consulta(c, x, resto, n, q, cauda, consulta)

# Conferencia observada na mesma rota; nao e uma hipotese de Regra2.
def registrar_puro(-c: S.Configuracao, -p: S.Programa, +ini: Maybe<&2, D.Estado>,
  +qs: List<&2, Q.Quadro>, -t: Nat, +pos: Nat, +n: Nat, antes: C.AntesDoCampo(qs, t, pos, n)) ->
  Antes(E.observacao_modelo(c, p, ini, qs), t, I.ConferiuComprimento{pos, n}):
  match antes:
    case (+b, L.Ambos{ordem, consulta}):
      (b, L.Ambos{ordem, Q.consulta_estabelece_observacao(c, p, qs, b, Q.Conferida{pos, n}, I.ConferiuComprimento{pos, n}, consulta, {==})})

def campo_puro(-c: S.Configuracao, -p: S.Programa, +ini: Maybe<&2, D.Estado>,
  +qs: List<&2, Q.Quadro>, +t: Nat, +pos: Nat, +n: Nat, seguros: C.CamposSeguros(qs),
  fato: Q.observa_servico(c, p, ini, qs, t, I.AlocouCampo{pos, n})) ->
  Antes(E.observacao_modelo(c, p, ini, qs), t, I.ConferiuComprimento{pos, n}):
  registrar_puro(c, p, ini, qs, t, pos, n, seguros(t, pos, n,
    Q.observacao_quadro(c, p, qs, t, I.AlocouCampo{pos, n}, fato)))

def AntesOrigem(~fonte: Fonte.Fonte, -c: S.Configuracao, -ini: Maybe<&2, D.Estado>,
  -qs: List<&2, Q.Quadro>, -origem: Maybe<&2, Fonte.JuizoSintatico>, -t: Nat, -pos: Nat, -n: Nat) -> Type:
  &b: Nat -> L.E<{Nat.is_lt(b, t) == True{} : Bool}, Fonte.de_origem(fonte, c, ini, qs, origem, b, I.ConferiuComprimento{pos, n})>

def campo_da_origem(~fonte: Fonte.Fonte, -c: S.Configuracao, +ini: Maybe<&2, D.Estado>,
  +qs: List<&2, Q.Quadro>, origem: Maybe<&2, Fonte.JuizoSintatico>, +t: Nat, +pos: Nat, +n: Nat,
  seguros: C.CamposSeguros(qs), fato: Fonte.de_origem(fonte, c, ini, qs, origem, t, I.AlocouCampo{pos, n})) ->
  AntesOrigem(fonte, c, ini, qs, origem, t, pos, n):
  match origem:
    case None{}: campo_puro(c, Fonte.sem_programa(), ini, qs, t, pos, n, seguros, fato)
    case Some{origem}: campo_puro(c, Fonte.programa(fonte, origem), ini, qs, t, pos, n, seguros, fato)

def AntesObservacao(~fonte: Fonte.Fonte, -c: S.Configuracao, -d: Fonte.ObservacaoData, -t: Nat, -pos: Nat, -n: Nat) -> Type:
  &b: Nat -> L.E<{Nat.is_lt(b, t) == True{} : Bool}, Fonte.de_observacao(fonte, c, d, b, I.ConferiuComprimento{pos, n})>

def CamposDaObservacao(d: Fonte.ObservacaoData) -> Type:
  match d:
    case Fonte.ObservacaoData{ini, qs, origem}: C.CamposSeguros(qs)

def campo_da_observacao(~fonte: Fonte.Fonte, -c: S.Configuracao, d: Fonte.ObservacaoData,
  +t: Nat, +pos: Nat, +n: Nat, seguros: CamposDaObservacao(d),
  fato: Fonte.de_observacao(fonte, c, d, t, I.AlocouCampo{pos, n})) -> AntesObservacao(fonte, c, d, t, pos, n):
  match d:
    case Fonte.ObservacaoData{ini, qs, origem}: campo_da_origem(fonte, c, ini, qs, origem, t, pos, n, seguros, fato)

def campos_da_chamada(~c: S.Configuracao, +s: D.Estado, +recepcao: X.Recepcao, dados: Fonte.ChamadaData) ->
  CamposDaObservacao(Fonte.construir_chamada(c, s, recepcao, dados)):
  match dados:
    case Fonte.ChamadaData{cf, pf, cert, termina, estado, ferramentas, +micro}:
      C.protocolo_confere_campos_antes_de_construir(micro, s, Rota.decidir(c, recepcao, estado, ferramentas))

def campos_do_inicio(~fonte: Fonte.Fonte, ~c: S.Configuracao, +s: D.Estado, dados: Fonte.InicialData) ->
  CamposDaObservacao(Fonte.construir_inicial(Fonte.identidade(fonte), c, s, dados)):
  match dados:
    case Fonte.InicialData{cf, sf, pf, juizo, resultado, +micro}:
      C.protocolo_confere_campos_antes_de_construir(micro, s, Rota.decidir_resultado_inicial(c, Fonte.identidade(fonte), juizo, resultado))

# Uma unica prova de conteudo para o renderer: Codec, reads, pedidos e operacoes.
def OrigensMicro(~c: S.Configuracao, +x: Fonte.Contexto, m: Rota.Micro) -> Type:
  match m:
    case Rota.Micro{a, b, d, e}:
      L.E<OrigensPrimitivas(c, x, a), L.E<OrigensPrimitivas(c, x, b),
        L.E<OrigensPrimitivas(c, x, d), OrigensPrimitivas(c, x, e)>>>

def execucao_gerada_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, +r: P.Requisicao, +ctx: D.Contexto,
  n: Nat, m: N.Maquina, +e: D.Esquema) -> Conteudos(c, x, Q.expandir_exec(r, ctx, E.gerar(n, m, e))):
  match n m:
    case _ N.Parada{w, ts, resposta}: L.Ambos{Unit{}, Unit{}}
    case 0n N.EmCurso{w, a, ts}: L.Ambos{Unit{}, Unit{}}
    case 1n+j N.EmCurso{+w, a, +ts}:
      match a:
        case S.Terminar{v}: L.Ambos{Unit{}, L.Ambos{Unit{}, Unit{}}}
        case S.Recusar{v}: L.Ambos{Unit{}, L.Ambos{Unit{}, Unit{}}}
        case S.Acessar{+o, k}:
          L.Ambos{Unit{}, L.Ambos{{==}, execucao_gerada_conteudo(c, x, r, ctx, j,
            N.passo_maquina(S.aplicar(D.operar(e, w, o), w, o, k), ts), e)}}

def execucao_real_conteudo(~fonte: Fonte.Fonte, ~c: S.Configuracao, +x: Fonte.Contexto,
  +s: D.Estado, +origem: Fonte.JuizoSintatico, +r: P.Requisicao, +ctx: D.Contexto,
  +xs: List<&2, Q.QuadroExec>, real: Fonte.PrefixoReal(fonte, c, s, r, ctx, origem, xs)) ->
  Conteudos(c, x, Q.expandir_exec(r, ctx, xs)):
  match real:
    case (+n, igual):
      %Equal.sym(List<&2, Q.QuadroExec>, xs, E.gerar(n, N.iniciar(Fonte.programa(fonte, origem), ctx, I.argumentos(r), s), S.esquema(c)), igual) :
        Conteudos(c, x, Q.expandir_exec(r, ctx, _))
      execucao_gerada_conteudo(c, x, r, ctx, n, N.iniciar(Fonte.programa(fonte, origem), ctx, I.argumentos(r), s), S.esquema(c))

def recebida_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, +m: Rota.Micro, +r: P.Requisicao,
  a: Conteudos(c, x, Rota.micro_entrada(m)), pedido: I.RequisicaoRecebida(Fonte.cenario_contexto(c, x), r)) ->
  Conteudos(c, x, Rota.render_recebida(m, r)):
  concatenar_conteudos(c, x, Rota.micro_entrada(m), [Q.Recebida{r}], a, L.Ambos{pedido, Unit{}})

def autenticada_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, +m: Rota.Micro, +r: P.Requisicao, +ctx: D.Contexto,
  a: Conteudos(c, x, Rota.micro_entrada(m)), b: Conteudos(c, x, Rota.micro_autenticacao(m)),
  pedido: I.RequisicaoRecebida(Fonte.cenario_contexto(c, x), r)) -> Conteudos(c, x, Rota.render_autenticada(m, r, ctx)):
  concatenar_conteudos(c, x, Rota.render_recebida(m, r), Q.concatenar(Rota.micro_autenticacao(m), [Q.Autenticada{r, Some{ctx}}]),
    recebida_conteudo(c, x, m, r, a, pedido), concatenar_conteudos(c, x, Rota.micro_autenticacao(m), [Q.Autenticada{r, Some{ctx}}], b, L.Ambos{Unit{}, Unit{}}))

def verificada_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, +m: Rota.Micro, +r: P.Requisicao, +ctx: D.Contexto,
  a: Conteudos(c, x, Rota.micro_entrada(m)), b: Conteudos(c, x, Rota.micro_autenticacao(m)),
  pedido: I.RequisicaoRecebida(Fonte.cenario_contexto(c, x), r)) -> Conteudos(c, x, Rota.render_verificada(m, r, ctx)):
  concatenar_conteudos(c, x, Rota.render_autenticada(m, r, ctx), [Q.Aceita{r, ctx}],
    autenticada_conteudo(c, x, m, r, ctx, a, b, pedido), L.Ambos{Unit{}, Unit{}})

def comecada_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, +m: Rota.Micro, +r: P.Requisicao, +ctx: D.Contexto,
  a: Conteudos(c, x, Rota.micro_entrada(m)), b: Conteudos(c, x, Rota.micro_autenticacao(m)),
  d: Conteudos(c, x, Rota.micro_execucao(m)), pedido: I.RequisicaoRecebida(Fonte.cenario_contexto(c, x), r)) ->
  Conteudos(c, x, Rota.render_comecada(m, r, ctx)):
  concatenar_conteudos(c, x, Rota.render_verificada(m, r, ctx), Q.concatenar(Rota.micro_execucao(m), [Q.Comecada{r, ctx}]),
    verificada_conteudo(c, x, m, r, ctx, a, b, pedido), concatenar_conteudos(c, x, Rota.micro_execucao(m), [Q.Comecada{r, ctx}], d, L.Ambos{Unit{}, Unit{}}))

def executada_conteudo(~fonte: Fonte.Fonte, ~c: S.Configuracao, +x: Fonte.Contexto, +m: Rota.Micro,
  +s: D.Estado, +origem: Fonte.JuizoSintatico, +r: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>,
  real: Fonte.PrefixoReal(fonte, c, s, r, ctx, origem, xs), pedido: I.RequisicaoRecebida(Fonte.cenario_contexto(c, x), r),
  a: Conteudos(c, x, Rota.micro_entrada(m)), b: Conteudos(c, x, Rota.micro_autenticacao(m)), d: Conteudos(c, x, Rota.micro_execucao(m))) ->
  Conteudos(c, x, Rota.render_execucao(m, r, ctx, xs)):
  concatenar_conteudos(c, x, Rota.render_comecada(m, r, ctx), Q.expandir_exec(r, ctx, xs),
    comecada_conteudo(c, x, m, r, ctx, a, b, d, pedido), execucao_real_conteudo(fonte, c, x, s, origem, r, ctx, xs, real))

def depois_entrega_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, fecha: Bool, -s: D.Estado, proxima: Bool) ->
  Conteudos(c, x, Rota.depois_entrega(fecha, s, proxima)):
  match fecha proxima:
    case True{} _: L.Ambos{Unit{}, Unit{}}
    case False{} True{}: L.Ambos{Unit{}, Unit{}}
    case False{} False{}: Unit{}

def entrega_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, +s: D.Estado, +bs: List<&2, U32>, +fecha: Bool, entrega: Rota.Entrega) ->
  Conteudos(c, x, Rota.render_entrega(s, bs, fecha, entrega)):
  match entrega:
    case Rota.Completa{proxima}: L.Ambos{Unit{}, depois_entrega_conteudo(c, x, fecha, s, proxima)}
    case Rota.Quebrada{prefixo}: L.Ambos{Unit{}, L.Ambos{Unit{}, Unit{}}}
    case Rota.PendenteEntrega{}: Unit{}

def publicacao_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, r: S.Resposta, -s: D.Estado) ->
  Conteudos(c, x, Rota.render_publicacao(r, s)):
  match r:
    case S.Resposta{S.Sucesso{}, v}: L.Ambos{Unit{}, Unit{}}
    case S.Resposta{S.Recusa{}, v}: Unit{}
    case S.Resposta{S.Entrada{}, v}: Unit{}
    case S.Resposta{S.Autenticacao{}, v}: Unit{}
    case S.Resposta{S.Certificado{}, v}: Unit{}
    case S.Resposta{S.Dados{}, v}: Unit{}
    case S.Resposta{S.Limite{}, v}: Unit{}
    case S.Resposta{S.Falha{}, v}: Unit{}

def conclusao_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, conclusao: N.Conclusao, +fecha: Bool, entrega: Rota.Entrega) ->
  Conteudos(c, x, Rota.render_conclusao(conclusao, fecha, entrega)):
  match conclusao:
    case N.Conclusao{+s, +r, +bs}:
      L.Ambos{Unit{}, concatenar_conteudos(c, x, Rota.render_publicacao(r, s), Con{Q.Concluida{r, s, fecha}, Rota.render_entrega(s, bs, fecha, entrega)},
        publicacao_conteudo(c, x, r, s), L.Ambos{Unit{}, entrega_conteudo(c, x, s, bs, fecha, entrega)})}

def erro_enquadrado_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, q: Maybe<&2, List<&2, U32>>, +r: S.Resposta,
  +s: D.Estado, +fecha: Bool, entrega: Rota.Entrega) -> Conteudos(c, x, Rota.render_erro_enquadrado(q, r, s, fecha, entrega)):
  match q:
    case None{}: Unit{}
    case Some{+bs}: L.Ambos{Unit{}, L.Ambos{Unit{}, entrega_conteudo(c, x, s, bs, fecha, entrega)}}

def erro_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, +status: S.Status, +s: D.Estado, +fecha: Bool, entrega: Rota.Entrega) ->
  Conteudos(c, x, Rota.render_erro(status, s, fecha, entrega)):
  erro_enquadrado_conteudo(c, x, P.enquadrar(S.resposta_valor(S.resposta_erro(status))), S.resposta_erro(status), s, fecha, entrega)

def falha_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, +s: D.Estado, +etapa: X.Etapa, +id: String, fatal: Bool, +entrega: Rota.Entrega) ->
  Conteudos(c, x, Rota.render_falha(s, etapa, id, fatal, entrega)):
  match fatal:
    case True{}: L.Ambos{Unit{}, L.Ambos{Unit{}, Unit{}}}
    case False{}: L.Ambos{Unit{}, erro_conteudo(c, x, S.Falha{}, s, False{}, entrega)}

def fatal_publicada_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, conclusao: N.Conclusao, +etapa: X.Etapa, +id: String) ->
  Conteudos(c, x, Rota.render_fatal_publicada(conclusao, etapa, id)):
  match conclusao:
    case N.Conclusao{+s, +r, bs}:
      L.Ambos{Unit{}, concatenar_conteudos(c, x, Rota.render_publicacao(r, s), [Q.Falhou{etapa, id, True{}}, Q.Fechada{}],
        publicacao_conteudo(c, x, r, s), L.Ambos{Unit{}, L.Ambos{Unit{}, Unit{}}})}

def inicial_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, q: Maybe<&2, List<&2, U32>>, +s: D.Estado,
  exato: {q == P.codificar(D.estado_valor(s)) : Maybe<&2, List<&2, U32>>}) -> Conteudos(c, x, Rota.render_inicial(q, s)):
  match q:
    case None{}: L.Ambos{exato, Unit{}}
    case Some{bs}: L.Ambos{exato, L.Ambos{{==}, L.Ambos{Unit{}, Unit{}}}}

def preparada_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, p: N.Preparada) -> Conteudos(c, x, [Rota.quadro_preparada(p)]):
  match p:
    case N.Preparada{w, ts, r, bs}: L.Ambos{Unit{}, Unit{}}

def fase_conteudo(~fonte: Fonte.Fonte, ~c: S.Configuracao, +x: Fonte.Contexto, +m: Rota.Micro,
  +s: D.Estado, +origem: Fonte.JuizoSintatico, fase: Rota.FaseAntes,
  real: Cinco.FaseReal(fonte, c, s, origem, fase), pedido: Fonte.PedidoDaFase(c, x, fase),
  a: Conteudos(c, x, Rota.micro_entrada(m)), b: Conteudos(c, x, Rota.micro_autenticacao(m)),
  d: Conteudos(c, x, Rota.micro_execucao(m)), e: Conteudos(c, x, Rota.micro_saida(m))) -> Conteudos(c, x, Rota.render_fase(m, fase)):
  match fase:
    case Rota.AntesEntrada{}: a
    case Rota.AposReceber{r}: recebida_conteudo(c, x, m, r, a, pedido)
    case Rota.AposAutenticar{r, ctx}: autenticada_conteudo(c, x, m, r, ctx, a, b, pedido)
    case Rota.AposVerificar{r, ctx}: verificada_conteudo(c, x, m, r, ctx, a, b, pedido)
    case Rota.Executando{r, ctx, xs}: executada_conteudo(fonte, c, x, m, s, origem, r, ctx, xs, real, pedido, a, b, d)
    case Rota.AposPreparar{+r, +ctx, +xs, +p}:
      concatenar_conteudos(c, x, Rota.render_execucao(m, r, ctx, xs), Q.concatenar(Rota.micro_saida(m), [Rota.quadro_preparada(p)]),
        executada_conteudo(fonte, c, x, m, s, origem, r, ctx, xs, Cinco.prefixo_do_final(fonte, c, s, r, ctx, origem, xs, p, real), pedido, a, b, d),
        concatenar_conteudos(c, x, Rota.micro_saida(m), [Rota.quadro_preparada(p)], e, preparada_conteudo(c, x, p)))

def prefixo_inicial_conteudo(~c: S.Configuracao, +x: Fonte.Contexto, +m: Rota.Micro, aceita: Bool,
  e: Conteudos(c, x, Rota.micro_saida(m))) -> Conteudos(c, x, Rota.prefixo_inicial(m, aceita)):
  match aceita:
    case True{}: L.Ambos{Unit{}, e}
    case False{}: Unit{}

def caso_conteudo(~fonte: Fonte.Fonte, ~c: S.Configuracao, +x: Fonte.Contexto, +m: Rota.Micro,
  +s: D.Estado, +origem: Fonte.JuizoSintatico, caso: Rota.Caso,
  real: Cinco.CasoReal(fonte, c, s, origem, caso), pedido: Fonte.PedidoDoCaso(c, x, caso),
  a: Conteudos(c, x, Rota.micro_entrada(m)), b: Conteudos(c, x, Rota.micro_autenticacao(m)),
  d: Conteudos(c, x, Rota.micro_execucao(m)), e: Conteudos(c, x, Rota.micro_saida(m))) -> Conteudos(c, x, Rota.render_caso(m, s, caso)):
  match caso:
    case Rota.InicialOk{}:
      L.Ambos{Unit{}, concatenar_conteudos(c, x, Rota.micro_saida(m), Rota.render_inicial(P.codificar(D.estado_valor(s)), s), e,
        inicial_conteudo(c, x, P.codificar(D.estado_valor(s)), s, {==}))}
    case Rota.InicialRecusa{status}: L.Ambos{Unit{}, Unit{}}
    case Rota.InicialFalha{+aceita, +etapa, +id, +fatal}:
      concatenar_conteudos(c, x, Rota.prefixo_inicial(m, aceita), [Q.Falhou{etapa, id, fatal}, Q.InicialRecusada{S.Falha{}}],
        prefixo_inicial_conteudo(c, x, m, aceita, e), L.Ambos{Unit{}, L.Ambos{Unit{}, Unit{}}})
    case Rota.SemResposta{}: L.Ambos{Unit{}, Unit{}}
    case Rota.EntradaRecusa{+erro, +fecha, +entrega}:
      concatenar_conteudos(c, x, Rota.micro_entrada(m), Rota.render_erro(Rota.status_entrada(erro), s, fecha, entrega), a,
        erro_conteudo(c, x, Rota.status_entrada(erro), s, fecha, entrega))
    case Rota.AutRecusa{+r, +entrega}:
      concatenar_conteudos(c, x, Rota.render_recebida(m, r), Q.concatenar(Rota.micro_autenticacao(m), Con{Q.Autenticada{r, None{}}, Rota.render_erro(S.Autenticacao{}, s, False{}, entrega)}),
        recebida_conteudo(c, x, m, r, a, pedido), concatenar_conteudos(c, x, Rota.micro_autenticacao(m), Con{Q.Autenticada{r, None{}}, Rota.render_erro(S.Autenticacao{}, s, False{}, entrega)},
          b, L.Ambos{Unit{}, erro_conteudo(c, x, S.Autenticacao{}, s, False{}, entrega)}))
    case Rota.GateRecusa{+r, +ctx, +entrega}:
      concatenar_conteudos(c, x, Rota.render_autenticada(m, r, ctx), Con{Q.Rejeitada{r, ctx}, Rota.render_erro(S.Certificado{}, s, False{}, entrega)},
        autenticada_conteudo(c, x, m, r, ctx, a, b, pedido), L.Ambos{Unit{}, erro_conteudo(c, x, S.Certificado{}, s, False{}, entrega)})
    case Rota.Executada{+r, +ctx, +xs, +p, +entrega}:
      concatenar_conteudos(c, x, Rota.render_execucao(m, r, ctx, xs), Q.concatenar(Rota.micro_saida(m), Rota.render_final(p, s, False{}, entrega)),
        executada_conteudo(fonte, c, x, m, s, origem, r, ctx, xs, Cinco.prefixo_do_final(fonte, c, s, r, ctx, origem, xs, p, real), pedido, a, b, d),
        concatenar_conteudos(c, x, Rota.micro_saida(m), Rota.render_final(p, s, False{}, entrega), e, conclusao_conteudo(c, x, N.concluir(p, s), False{}, entrega)))
    case Rota.FalhaAntes{+fase, +etapa, +id, +fatal, +entrega}:
      concatenar_conteudos(c, x, Rota.render_fase(m, fase), Rota.render_falha(s, etapa, id, fatal, entrega),
        fase_conteudo(fonte, c, x, m, s, origem, fase, real, pedido, a, b, d, e), falha_conteudo(c, x, s, etapa, id, fatal, entrega))
    case Rota.FatalAposPublicacao{+r, +ctx, +xs, +p, +etapa, +id}:
      concatenar_conteudos(c, x, Rota.render_execucao(m, r, ctx, xs), Q.concatenar(Rota.micro_saida(m), Rota.render_fatal_publicada(N.concluir(p, s), etapa, id)),
        executada_conteudo(fonte, c, x, m, s, origem, r, ctx, xs, Cinco.prefixo_do_final(fonte, c, s, r, ctx, origem, xs, p, real), pedido, a, b, d),
        concatenar_conteudos(c, x, Rota.micro_saida(m), Rota.render_fatal_publicada(N.concluir(p, s), etapa, id), e, fatal_publicada_conteudo(c, x, N.concluir(p, s), etapa, id)))
    case Rota.Pendente{fase}: fase_conteudo(fonte, c, x, m, s, origem, fase, real, pedido, a, b, d, e)
    case Rota.InicialPendente{aceita}: prefixo_inicial_conteudo(c, x, m, aceita, e)

# Todas as premissas locais sao resultados de primitivas concretas, nao Regra2.
def protocolo_conteudo(~fonte: Fonte.Fonte, ~c: S.Configuracao, +x: Fonte.Contexto, +m: Rota.Micro,
  +s: D.Estado, +origem: Fonte.JuizoSintatico, +caso: Rota.Caso,
  real: Cinco.CasoReal(fonte, c, s, origem, caso), pedido: Fonte.PedidoDoCaso(c, x, caso), origens: OrigensMicro(c, x, m)) ->
  Conteudos(c, x, Rota.render(m, s, caso)):
  match m origens:
    case Rota.Micro{+a, +b, +d, +e} L.Ambos{oa, L.Ambos{ob, L.Ambos{od, oe}}}:
      L.Ambos{Unit{}, caso_conteudo(fonte, c, x, Rota.Micro{a, b, d, e}, s, origem, caso, real, pedido,
        conteudo_de_todas_primitivas_e_exato(c, x, a, oa), conteudo_de_todas_primitivas_e_exato(c, x, b, ob),
        conteudo_de_todas_primitivas_e_exato(c, x, d, od), conteudo_de_todas_primitivas_e_exato(c, x, e, oe))}

def dados_da_rota(~fonte: Fonte.Fonte, ~c: S.Configuracao, x: Fonte.Contexto) -> Fonte.ObservacaoData:
  match x:
    case Fonte.Inicial{+m, +s, pi}: Fonte.construir_inicial(Fonte.identidade(fonte), c, s, Fonte.inicial(fonte, m))
    case Fonte.Atendimento{+m, +s, +r}: Fonte.construir_chamada(c, s, r, Fonte.chamada(fonte, m))

def origem_observada(~fonte: Fonte.Fonte, ~c: S.Configuracao, +x: Fonte.Contexto, -t: Nat, -f: I.Fato,
  observado: Fonte.da_rota(fonte, Fonte.cenario_contexto(c, x), t, f)) -> Fonte.de_observacao(fonte, c, dados_da_rota(fonte, c, x), t, f):
  match x:
    case Fonte.Inicial{m, s, pi}: observado
    case Fonte.Atendimento{m, s, r}: observado

def campos_da_rota(~fonte: Fonte.Fonte, ~c: S.Configuracao, +x: Fonte.Contexto) -> CamposDaObservacao(dados_da_rota(fonte, c, x)):
  match x:
    case Fonte.Inicial{+m, +s, pi}: campos_do_inicio(fonte, c, s, Fonte.inicial(fonte, m))
    case Fonte.Atendimento{+m, +s, +r}: campos_da_chamada(c, s, r, Fonte.chamada(fonte, m))

def ConteudoDaObservacao(~c: S.Configuracao, +x: Fonte.Contexto, d: Fonte.ObservacaoData) -> Type:
  match d:
    case Fonte.ObservacaoData{ini, qs, origem}: Conteudos(c, x, qs)

def conteudo_do_fato(~c: S.Configuracao, +x: Fonte.Contexto, -p: S.Programa,
  +ini: Maybe<&2, D.Estado>, +qs: List<&2, Q.Quadro>, +t: Nat, f: I.Fato,
  conteudos: Conteudos(c, x, qs), observado: Q.observa_servico(c, p, ini, qs, t, f)) -> Conteudo(c, x, Q.quadro_do_fato(f)):
  match f:
    case I.ConfiguracaoEmUso{c}: Unit{}
    case I.ProvaInicialAceita{}: Unit{}
    case I.InstanciaIniciou{s}: Unit{}
    case I.InicializacaoRecusada{s}: Unit{}
    case I.Codificou{+v, +bs}: conteudo_da_consulta(c, x, qs, t, Q.Codificada{v, bs}, conteudos, Q.observacao_quadro(c, p, qs, t, I.Codificou{v, bs}, observado))
    case I.Decodificou{+bs, +v}: conteudo_da_consulta(c, x, qs, t, Q.Decodificada{bs, v}, conteudos, Q.observacao_quadro(c, p, qs, t, I.Decodificou{bs, v}, observado))
    case I.Guardou{+s, +bs, +abstr}: conteudo_da_consulta(c, x, qs, t, Q.Guardada{s, bs, abstr}, conteudos, Q.observacao_quadro(c, p, qs, t, I.Guardou{s, bs, abstr}, observado))
    case I.ConferiuComprimento{pos, n}: Unit{}
    case I.AlocouCampo{pos, n}: Unit{}
    case I.LeuCorpo{+antes, +n, +declarado}: conteudo_da_consulta(c, x, qs, t, Q.Lida{antes, n, declarado}, conteudos, Q.observacao_quadro(c, p, qs, t, I.LeuCorpo{antes, n, declarado}, observado))
    case I.RecebeuRequisicao{+r}: conteudo_da_consulta(c, x, qs, t, Q.Recebida{r}, conteudos, Q.observacao_quadro(c, p, qs, t, I.RecebeuRequisicao{r}, observado))
    case I.Autenticou{r, ctx}: Unit{}
    case I.CertificadoAceito{r, ctx, p}: Unit{}
    case I.CertificadoRejeitado{r, ctx}: Unit{}
    case I.ProgramaComecou{r, ctx, p}: Unit{}
    case I.Avaliou{r, ctx, p, percurso}: Unit{}
    case I.Operou{+e, +s, +o, +r}: conteudo_da_consulta(c, x, qs, t, Q.Operada{e, s, o, r}, conteudos, Q.observacao_quadro(c, p, qs, t, I.Operou{e, s, o, r}, observado))
    case I.Preparou{r, bs}: Unit{}
    case I.Publicou{s}: Unit{}
    case I.EstadoVisivel{s}: Unit{}
    case I.FalhouAmbiente{etapa, id, fatal}: Unit{}
    case I.Concluiu{r, s, fecha}: Unit{}
    case I.EntregouTudo{bs}: Unit{}
    case I.EntregaInterrompida{bs}: Unit{}
    case I.EncerrouCanal{}: Unit{}
    case I.ProximaChamada{antes, apos}: Unit{}
    case I.InspecaoNaoModelada{descricao}: Unit{}
    case I.EfeitoNaoModelado{descricao}: Unit{}

def conteudo_na_origem(~fonte: Fonte.Fonte, ~c: S.Configuracao, +x: Fonte.Contexto,
  +ini: Maybe<&2, D.Estado>, +qs: List<&2, Q.Quadro>, origem: Maybe<&2, Fonte.JuizoSintatico>, +t: Nat, f: I.Fato,
  conteudos: Conteudos(c, x, qs), observado: Fonte.de_origem(fonte, c, ini, qs, origem, t, f)) ->
  Conteudo(c, x, Q.quadro_do_fato(f)):
  match origem:
    case None{}:
      conteudo_do_fato(c, x, Fonte.sem_programa(), ini, qs, t, f, conteudos, observado)
    case Some{origem}:
      conteudo_do_fato(c, x, Fonte.programa(fonte, origem), ini, qs, t, f, conteudos, observado)

def conteudo_na_observacao(~fonte: Fonte.Fonte, ~c: S.Configuracao, +x: Fonte.Contexto, dados: Fonte.ObservacaoData,
  +t: Nat, f: I.Fato, conteudos: ConteudoDaObservacao(c, x, dados),
  observado: Fonte.de_observacao(fonte, c, dados, t, f)) -> Conteudo(c, x, Q.quadro_do_fato(f)):
  match dados:
    case Fonte.ObservacaoData{ini, qs, origem}: conteudo_na_origem(fonte, c, x, ini, qs, origem, t, f, conteudos, observado)

def observacao_virou_rota(~fonte: Fonte.Fonte, ~c: S.Configuracao, +x: Fonte.Contexto, -t: Nat, -f: I.Fato,
  observado: Fonte.de_observacao(fonte, c, dados_da_rota(fonte, c, x), t, f)) -> Fonte.da_rota(fonte, Fonte.cenario_contexto(c, x), t, f):
  match x:
    case Fonte.Inicial{m, s, pi}: observado
    case Fonte.Atendimento{m, s, r}: observado

def introduzir_conferencia(~fonte: Fonte.Fonte, ~c: S.Configuracao, +x: Fonte.Contexto, -t: Nat, -pos: Nat, -n: Nat,
  nome: {Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
  canonico: {Fonte.cenario_contexto(c, x) == Fonte.cenario(fonte, Fonte.mundo(Fonte.cenario_contexto(c, x))) : I.Cenario},
  antes: AntesObservacao(fonte, c, dados_da_rota(fonte, c, x), t, pos, n)) ->
  I.Antes(Fonte.ambiente(fonte), Fonte.artefato(fonte), Fonte.cenario_contexto(c, x), t, I.ConferiuComprimento{pos, n}):
  match antes:
    case (+b, L.Ambos{ordem, observado}):
      (b, L.Ambos{ordem, Fonte.introduzir_fato_literal(fonte, Fonte.artefato(fonte), Fonte.cenario_contexto(c, x), b, I.ConferiuComprimento{pos, n},
        L.Ambos{nome, L.Ambos{canonico, observacao_virou_rota(fonte, c, x, b, I.ConferiuComprimento{pos, n}, observado)}})})

# Composicao exata: o unico fato com obrigacao de ordem usa CamposServico.
def regra2_componentes(~fonte: Fonte.Fonte, ~c: S.Configuracao, +x: Fonte.Contexto, +t: Nat, f: I.Fato,
  conteudos: ConteudoDaObservacao(c, x, dados_da_rota(fonte, c, x)),
  nome: {Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
  canonico: {Fonte.cenario_contexto(c, x) == Fonte.cenario(fonte, Fonte.mundo(Fonte.cenario_contexto(c, x))) : I.Cenario},
  observado: Fonte.da_rota(fonte, Fonte.cenario_contexto(c, x), t, f)) ->
  K.Regra2(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), Fonte.cenario_contexto(c, x), t):
  match f:
    case I.ConfiguracaoEmUso{c}: Unit{}
    case I.ProvaInicialAceita{}: Unit{}
    case I.InstanciaIniciou{s}: Unit{}
    case I.InicializacaoRecusada{s}: Unit{}
    case I.Codificou{+v, +bs}: conteudo_na_observacao(fonte, c, x, dados_da_rota(fonte, c, x), t, I.Codificou{v, bs}, conteudos, origem_observada(fonte, c, x, t, I.Codificou{v, bs}, observado))
    case I.Decodificou{+bs, +v}: conteudo_na_observacao(fonte, c, x, dados_da_rota(fonte, c, x), t, I.Decodificou{bs, v}, conteudos, origem_observada(fonte, c, x, t, I.Decodificou{bs, v}, observado))
    case I.Guardou{+s, +bs, +abstr}: conteudo_na_observacao(fonte, c, x, dados_da_rota(fonte, c, x), t, I.Guardou{s, bs, abstr}, conteudos, origem_observada(fonte, c, x, t, I.Guardou{s, bs, abstr}, observado))
    case I.ConferiuComprimento{pos, n}: Unit{}
    case I.AlocouCampo{+pos, +n}: introduzir_conferencia(fonte, c, x, t, pos, n, nome, canonico, campo_da_observacao(fonte, c, dados_da_rota(fonte, c, x), t, pos, n, campos_da_rota(fonte, c, x), origem_observada(fonte, c, x, t, I.AlocouCampo{pos, n}, observado)))
    case I.LeuCorpo{+antes, +n, +declarado}: conteudo_na_observacao(fonte, c, x, dados_da_rota(fonte, c, x), t, I.LeuCorpo{antes, n, declarado}, conteudos, origem_observada(fonte, c, x, t, I.LeuCorpo{antes, n, declarado}, observado))
    case I.RecebeuRequisicao{+r}: conteudo_na_observacao(fonte, c, x, dados_da_rota(fonte, c, x), t, I.RecebeuRequisicao{r}, conteudos, origem_observada(fonte, c, x, t, I.RecebeuRequisicao{r}, observado))
    case I.Autenticou{r, ctx}: Unit{}
    case I.CertificadoAceito{r, ctx, p}: Unit{}
    case I.CertificadoRejeitado{r, ctx}: Unit{}
    case I.ProgramaComecou{r, ctx, p}: Unit{}
    case I.Avaliou{r, ctx, p, percurso}: Unit{}
    case I.Operou{+e, +s, +o, +r}: conteudo_na_observacao(fonte, c, x, dados_da_rota(fonte, c, x), t, I.Operou{e, s, o, r}, conteudos, origem_observada(fonte, c, x, t, I.Operou{e, s, o, r}, observado))
    case I.Preparou{r, bs}: Unit{}
    case I.Publicou{s}: Unit{}
    case I.EstadoVisivel{s}: Unit{}
    case I.FalhouAmbiente{etapa, id, fatal}: Unit{}
    case I.Concluiu{r, s, fecha}: Unit{}
    case I.EntregouTudo{bs}: Unit{}
    case I.EntregaInterrompida{bs}: Unit{}
    case I.EncerrouCanal{}: Unit{}
    case I.ProximaChamada{antes, apos}: Unit{}
    case I.InspecaoNaoModelada{descricao}: Unit{}
    case I.EfeitoNaoModelado{descricao}: Unit{}

# Proveniencia de pedidos pela mesma decisao, sem outro parser nem renderer.
def pedidos_no_ponto(~c: S.Configuracao, +x: Fonte.Contexto, +r: P.Requisicao, +ctx: D.Contexto,
  ponto: Rota.PontoExec, pedido: I.RequisicaoRecebida(Fonte.cenario_contexto(c, x), r)) ->
  Fonte.PedidoDaFase(c, x, Rota.fase_do_erro(ponto, r, ctx)):
  match ponto:
    case Rota.AntesDeComecar{}: pedido
    case Rota.Durante{xs}: pedido
    case Rota.Preparou{xs, p}: pedido

def pedidos_na_limpeza(~c: S.Configuracao, +x: Fonte.Contexto, +r: P.Requisicao, +ctx: D.Contexto,
  +xs: List<&2, Q.QuadroExec>, +p: N.Preparada, limpeza: Rota.Limpeza, +entrega: Rota.Entrega,
  pedido: I.RequisicaoRecebida(Fonte.cenario_contexto(c, x), r)) ->
  Fonte.PedidoDoCaso(c, x, Rota.decidir_limpeza(r, ctx, xs, p, limpeza, entrega)):
  match limpeza:
    case Rota.Limpa{}: pedido
    case Rota.ErroLimpeza{id, fatal}: pedido
    case Rota.FatalAposStore{etapa, id}: pedido
    case Rota.PendenteLimpeza{}: pedido

def pedidos_na_execucao(~c: S.Configuracao, +x: Fonte.Contexto, +r: P.Requisicao, +ctx: D.Contexto,
  saida: Rota.SaidaExecucao, +limpeza: Rota.Limpeza, +entrega: Rota.Entrega,
  pedido: I.RequisicaoRecebida(Fonte.cenario_contexto(c, x), r)) ->
  Fonte.PedidoDoCaso(c, x, Rota.decidir_execucao(r, ctx, saida, limpeza, entrega)):
  match saida:
    case Rota.Finalizou{xs, p}: pedidos_na_limpeza(c, x, r, ctx, xs, p, limpeza, entrega, pedido)
    case Rota.ErroExecucao{ponto, etapa, id, fatal}: pedidos_no_ponto(c, x, r, ctx, ponto, pedido)
    case Rota.PendenteExecucao{ponto}: pedidos_no_ponto(c, x, r, ctx, ponto, pedido)

def pedidos_no_juizo(~c: S.Configuracao, +x: Fonte.Contexto, +r: P.Requisicao, +ctx: D.Contexto,
  dados: Rota.DadosFerramentas, pedido: I.RequisicaoRecebida(Fonte.cenario_contexto(c, x), r)) ->
  Fonte.PedidoDoCaso(c, x, Rota.decidir_juizo(r, ctx, dados)):
  match dados:
    case Rota.DadosFerramentas{j, +saida, +limpeza, +entrega, pre}:
      match j:
        case Rota.Aceitou{}: pedidos_na_execucao(c, x, r, ctx, saida, limpeza, entrega, pedido)
        case Rota.Recusou{}: pedido
        case Rota.ErroJuizo{id, fatal}: pedido
        case Rota.PendenteJuizo{}: pedido

def pedidos_na_identidade(~c: S.Configuracao, +x: Fonte.Contexto, identidade: Maybe<&2, D.Contexto>, +r: P.Requisicao,
  +dados: Rota.DadosFerramentas, pedido: I.RequisicaoRecebida(Fonte.cenario_contexto(c, x), r)) ->
  Fonte.PedidoDoCaso(c, x, Rota.decidir_identidade(identidade, r, dados)):
  match identidade:
    case None{}:
      match dados:
        case Rota.DadosFerramentas{j, saida, limpeza, entrega, pre}: pedido
    case Some{ctx}: pedidos_no_juizo(c, x, r, ctx, dados, pedido)

def pedidos_na_autenticacao(~c: S.Configuracao, +x: Fonte.Contexto, +s: D.Estado, +r: P.Requisicao,
  pre: Rota.Preprocessamento, +dados: Rota.DadosFerramentas, pedido: I.RequisicaoRecebida(Fonte.cenario_contexto(c, x), r)) ->
  Fonte.PedidoDoCaso(c, x, Rota.decidir_autenticacao(pre, s, r, dados)):
  match pre:
    case Rota.FalhaAuth{id, fatal}: pedido
    case Rota.PendenteAuth{}: pedido
    case Rota.Normal{}: pedidos_na_identidade(c, x, D.autenticar(s, I.credencial(r)), r, dados, pedido)
    case Rota.FalhaEnquadramento{id, fatal}: pedidos_na_identidade(c, x, D.autenticar(s, I.credencial(r)), r, dados, pedido)
    case Rota.FalhaDecode{id, fatal}: pedidos_na_identidade(c, x, D.autenticar(s, I.credencial(r)), r, dados, pedido)
    case Rota.PendenteEnquadramento{}: pedidos_na_identidade(c, x, D.autenticar(s, I.credencial(r)), r, dados, pedido)
    case Rota.PendenteDecode{}: pedidos_na_identidade(c, x, D.autenticar(s, I.credencial(r)), r, dados, pedido)

def pedidos_na_entrada(~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +entrada: X.Recepcao,
  +be: List<&2, U32>, +br: List<&2, U32>, +bs: List<&2, U32>, pre: Entrada.PreAutenticacao, +dados: Rota.DadosFerramentas,
  montagem: {Transporte.juntar(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>},
  octetos_e: {B.octetos_validos(be) == True{} : Bool}, octetos_r: {B.octetos_validos(br) == True{} : Bool},
  recebido: {X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{br} : X.Disposicao},
  pronta: {Entrada.decodificar(bs, S.esquema(c), S.limites(c)) == pre : Entrada.PreAutenticacao}) ->
  Fonte.PedidoDoCaso(c, Fonte.Atendimento{mundo, s, entrada}, Rota.decidir_pre(pre, dados)):
  match pre:
    case Entrada.Pronta{+decodificado, +r}:
      pedidos_na_autenticacao(c, Fonte.Atendimento{mundo, s, entrada}, decodificado, r, Rota.preprocessamento(dados), dados,
        Fonte.requisicao_pronta_veio_do_corpo(be, br, bs, S.esquema(c), S.limites(c), decodificado, r, mundo, c, entrada,
          montagem, octetos_e, octetos_r, recebido, pronta))
    case Entrada.ErroMensagem{status}:
      match dados:
        case Rota.DadosFerramentas{j, saida, limpeza, entrega, pre}: Unit{}
    case Entrada.ErroTransporte{}:
      match dados:
        case Rota.DadosFerramentas{j, saida, limpeza, entrega, pre}: Unit{}

def pedidos_no_decode(~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +entrada: X.Recepcao,
  +be: List<&2, U32>, +br: List<&2, U32>, +bs: List<&2, U32>, pre: Rota.Preprocessamento, +dados: Rota.DadosFerramentas,
  montagem: {Transporte.juntar(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>},
  octetos_e: {B.octetos_validos(be) == True{} : Bool}, octetos_r: {B.octetos_validos(br) == True{} : Bool},
  recebido: {X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{br} : X.Disposicao}) ->
  Fonte.PedidoDoCaso(c, Fonte.Atendimento{mundo, s, entrada}, Rota.decidir_decode(pre, bs, S.esquema(c), S.limites(c), dados)):
  match pre:
    case Rota.FalhaDecode{id, fatal}: Unit{}
    case Rota.PendenteDecode{}: Unit{}
    case Rota.Normal{}: pedidos_na_entrada(c, mundo, s, entrada, be, br, bs, Entrada.decodificar(bs, S.esquema(c), S.limites(c)), dados, montagem, octetos_e, octetos_r, recebido, {==})
    case Rota.FalhaEnquadramento{id, fatal}: pedidos_na_entrada(c, mundo, s, entrada, be, br, bs, Entrada.decodificar(bs, S.esquema(c), S.limites(c)), dados, montagem, octetos_e, octetos_r, recebido, {==})
    case Rota.FalhaAuth{id, fatal}: pedidos_na_entrada(c, mundo, s, entrada, be, br, bs, Entrada.decodificar(bs, S.esquema(c), S.limites(c)), dados, montagem, octetos_e, octetos_r, recebido, {==})
    case Rota.PendenteEnquadramento{}: pedidos_na_entrada(c, mundo, s, entrada, be, br, bs, Entrada.decodificar(bs, S.esquema(c), S.limites(c)), dados, montagem, octetos_e, octetos_r, recebido, {==})
    case Rota.PendenteAuth{}: pedidos_na_entrada(c, mundo, s, entrada, be, br, bs, Entrada.decodificar(bs, S.esquema(c), S.limites(c)), dados, montagem, octetos_e, octetos_r, recebido, {==})

def pedidos_no_pacote(~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +entrada: X.Recepcao,
  +be: List<&2, U32>, +br: List<&2, U32>, pacote: Maybe<&2, List<&2, U32>>, +dados: Rota.DadosFerramentas,
  montagem: {Transporte.juntar(be, br) == pacote : Maybe<&2, List<&2, U32>>},
  octetos_e: {B.octetos_validos(be) == True{} : Bool}, octetos_r: {B.octetos_validos(br) == True{} : Bool},
  recebido: {X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{br} : X.Disposicao}) ->
  Fonte.PedidoDoCaso(c, Fonte.Atendimento{mundo, s, entrada}, Rota.decidir_pacote(pacote, S.esquema(c), S.limites(c), dados)):
  match pacote:
    case None{}:
      match dados:
        case Rota.DadosFerramentas{j, saida, limpeza, entrega, pre}: Unit{}
    case Some{+bs}: pedidos_no_decode(c, mundo, s, entrada, be, br, bs, Rota.preprocessamento(dados), dados, montagem, octetos_e, octetos_r, recebido)

def OctetosRecebidos(d: X.Disposicao) -> Type:
  match d:
    case X.ProcessarCorpo{br}: {B.octetos_validos(br) == True{} : Bool}
    case _: Unit

def pedidos_na_disposicao(~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +entrada: X.Recepcao,
  +be: List<&2, U32>, disposicao: X.Disposicao, +dados: Rota.DadosFerramentas,
  octetos_e: {B.octetos_validos(be) == True{} : Bool}, octetos_r: OctetosRecebidos(disposicao),
  recebido: {X.decidir_recepcao(c, entrada) == disposicao : X.Disposicao}) ->
  Fonte.PedidoDoCaso(c, Fonte.Atendimento{mundo, s, entrada}, Rota.decidir_disposicao(disposicao, be, S.esquema(c), S.limites(c), dados)):
  match disposicao:
    case X.EncerrarSemResposta{}: Unit{}
    case X.RecusarEncerrar{status}:
      match dados:
        case Rota.DadosFerramentas{j, saida, limpeza, entrega, pre}: Unit{}
    case X.RecusarContinuar{status}:
      match dados:
        case Rota.DadosFerramentas{j, saida, limpeza, entrega, pre}: Unit{}
    case X.ProcessarCorpo{+br}: pedidos_no_pacote(c, mundo, s, entrada, be, br, Transporte.juntar(be, br), dados, {==}, octetos_e, octetos_r, recebido)

def pedidos_no_enquadramento(~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +entrada: X.Recepcao,
  +be: List<&2, U32>, pre: Rota.Preprocessamento, +disposicao: X.Disposicao, +dados: Rota.DadosFerramentas,
  octetos_e: {B.octetos_validos(be) == True{} : Bool}, octetos_r: OctetosRecebidos(disposicao),
  recebido: {X.decidir_recepcao(c, entrada) == disposicao : X.Disposicao}) ->
  Fonte.PedidoDoCaso(c, Fonte.Atendimento{mundo, s, entrada}, Rota.decidir_enquadramento(pre, disposicao, be, S.esquema(c), S.limites(c), dados)):
  match pre:
    case Rota.FalhaEnquadramento{id, fatal}: Unit{}
    case Rota.PendenteEnquadramento{}: Unit{}
    case Rota.Normal{}: pedidos_na_disposicao(c, mundo, s, entrada, be, disposicao, dados, octetos_e, octetos_r, recebido)
    case Rota.FalhaDecode{id, fatal}: pedidos_na_disposicao(c, mundo, s, entrada, be, disposicao, dados, octetos_e, octetos_r, recebido)
    case Rota.FalhaAuth{id, fatal}: pedidos_na_disposicao(c, mundo, s, entrada, be, disposicao, dados, octetos_e, octetos_r, recebido)
    case Rota.PendenteDecode{}: pedidos_na_disposicao(c, mundo, s, entrada, be, disposicao, dados, octetos_e, octetos_r, recebido)
    case Rota.PendenteAuth{}: pedidos_na_disposicao(c, mundo, s, entrada, be, disposicao, dados, octetos_e, octetos_r, recebido)

law decidir_por_recepcao:
  for c: S.Configuracao
  for -r: X.Recepcao
  for -be: List<&2, U32>
  for -dados: Rota.DadosFerramentas
  {Rota.decidir(c, r, be, dados) ==
    Rota.decidir_enquadramento(Rota.preprocessamento(dados), X.decidir_recepcao(c, r), be, S.esquema(c), S.limites(c), dados) : Rota.Caso}
def decidir_por_recepcao(c, r, be, dados):
  match c:
    case S.Configuracao{e, leis, lim, ambiente}: {==}

def pedidos_da_decisao(~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +entrada: X.Recepcao,
  +be: List<&2, U32>, +dados: Rota.DadosFerramentas,
  octetos_e: {B.octetos_validos(be) == True{} : Bool}, octetos_r: OctetosRecebidos(X.decidir_recepcao(c, entrada))) ->
  Fonte.PedidoDoCaso(c, Fonte.Atendimento{mundo, s, entrada}, Rota.decidir(c, entrada, be, dados)):
  %Equal.sym(Rota.Caso, Rota.decidir(c, entrada, be, dados),
    Rota.decidir_enquadramento(Rota.preprocessamento(dados), X.decidir_recepcao(c, entrada), be, S.esquema(c), S.limites(c), dados),
    decidir_por_recepcao(c, entrada, be, dados)) : Fonte.PedidoDoCaso(c, Fonte.Atendimento{mundo, s, entrada}, _)
  pedidos_no_enquadramento(c, mundo, s, entrada, be, Rota.preprocessamento(dados), X.decidir_recepcao(c, entrada), dados, octetos_e, octetos_r, {==})

# Contratos baixos das primitivas efetivamente registradas para esta chamada.
def OrigemDaChamada(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado,
  +entrada: X.Recepcao, dados: Fonte.ChamadaData) -> Type:
  match dados:
    case Fonte.ChamadaData{cf, origem, pf, tf, be, ferramentas, micro}:
      L.E<Cinco.ChamadaReal(fonte, c, s, entrada, Fonte.ChamadaData{cf, origem, pf, tf, be, ferramentas, micro}),
        L.E<OrigensMicro(c, Fonte.Atendimento{mundo, s, entrada}, micro),
          L.E<{B.octetos_validos(be) == True{} : Bool}, OctetosRecebidos(X.decidir_recepcao(c, entrada))>>>

def conteudos_da_chamada(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado,
  +entrada: X.Recepcao, dados: Fonte.ChamadaData, origem_real: OrigemDaChamada(fonte, c, mundo, s, entrada, dados)) ->
  ConteudoDaObservacao(c, Fonte.Atendimento{mundo, s, entrada}, Fonte.construir_chamada(c, s, entrada, dados)):
  match dados origem_real:
    case Fonte.ChamadaData{cf, +origem, pf, tf, +be, +ferramentas, +micro} L.Ambos{real, L.Ambos{origens, L.Ambos{octetos_e, octetos_r}}}:
      protocolo_conteudo(fonte, c, Fonte.Atendimento{mundo, s, entrada}, micro, s, origem, Rota.decidir(c, entrada, be, ferramentas),
        Cinco.execucao_da_decisao(fonte, c, s, origem, be, ferramentas, entrada, real),
        pedidos_da_decisao(c, mundo, s, entrada, be, ferramentas, octetos_e, octetos_r), origens)

def inicial_aceito_sem_programa(~fonte: Fonte.Fonte, ~c: S.Configuracao, +x: Fonte.Contexto,
  -s: D.Estado, -origem: Fonte.JuizoSintatico, resultado: Rota.ResultadoInicial, valida: Bool) ->
  L.E<Cinco.CasoReal(fonte, c, s, origem, Rota.decidir_aceitou_inicial(resultado, valida)),
    Fonte.PedidoDoCaso(c, x, Rota.decidir_aceitou_inicial(resultado, valida))>:
  match resultado:
    case Rota.Finalizada{}:
      match valida:
        case False{}: L.Ambos{Unit{}, Unit{}}
        case True{}: L.Ambos{Unit{}, Unit{}}
    case Rota.FalhouInicial{aceita, etapa, id, fatal}: L.Ambos{Unit{}, Unit{}}
    case Rota.PendenteInicial{aceita}: L.Ambos{Unit{}, Unit{}}

def inicial_sem_programa(~fonte: Fonte.Fonte, ~c: S.Configuracao, +x: Fonte.Contexto,
  -s: D.Estado, -origem: Fonte.JuizoSintatico, juizo: Rota.Juizo, +resultado: Rota.ResultadoInicial, +valida: Bool) ->
  L.E<Cinco.CasoReal(fonte, c, s, origem, Rota.decidir_juizo_inicial(juizo, resultado, valida)),
    Fonte.PedidoDoCaso(c, x, Rota.decidir_juizo_inicial(juizo, resultado, valida))>:
  match juizo:
    case Rota.Aceitou{}: inicial_aceito_sem_programa(fonte, c, x, s, origem, resultado, valida)
    case Rota.Recusou{}: L.Ambos{Unit{}, Unit{}}
    case Rota.ErroJuizo{id, fatal}: L.Ambos{Unit{}, Unit{}}
    case Rota.PendenteJuizo{}: L.Ambos{Unit{}, Unit{}}

def OrigemDaInicial(~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +pi: String, dados: Fonte.InicialData) -> Type:
  match dados:
    case Fonte.InicialData{cf, sf, pf, j, resultado, micro}: OrigensMicro(c, Fonte.Inicial{mundo, s, pi}, micro)

def conteudos_da_inicial(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +pi: String,
  dados: Fonte.InicialData, origens: OrigemDaInicial(c, mundo, s, pi, dados)) ->
  ConteudoDaObservacao(c, Fonte.Inicial{mundo, s, pi}, Fonte.construir_inicial(Fonte.identidade(fonte), c, s, dados)):
  match dados:
    case Fonte.InicialData{cf, sf, +pf, +j, +resultado, +micro}:
      Fundamentos.com_par(Conteudos(c, Fonte.Inicial{mundo, s, pi}, Rota.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, j, resultado, micro)),
        Cinco.CasoReal(fonte, c, s, pf, Rota.decidir_resultado_inicial(c, Fonte.identidade(fonte), j, resultado)),
        Fonte.PedidoDoCaso(c, Fonte.Inicial{mundo, s, pi}, Rota.decidir_resultado_inicial(c, Fonte.identidade(fonte), j, resultado)),
        inicial_sem_programa(fonte, c, Fonte.Inicial{mundo, s, pi}, s, pf, j, resultado, Configuracao.valida(c, Fonte.identidade(fonte))),
        real => pedido => protocolo_conteudo(fonte, c, Fonte.Inicial{mundo, s, pi}, micro, s, pf,
          Rota.decidir_resultado_inicial(c, Fonte.identidade(fonte), j, resultado), real, pedido, origens))

def OrigemDaRota(~fonte: Fonte.Fonte, ~c: S.Configuracao, x: Fonte.Contexto) -> Type:
  match x:
    case Fonte.Inicial{+m, +s, +pi}: OrigemDaInicial(c, m, s, pi, Fonte.inicial(fonte, m))
    case Fonte.Atendimento{+m, +s, +r}: OrigemDaChamada(fonte, c, m, s, r, Fonte.chamada(fonte, m))

def conteudos_da_rota(~fonte: Fonte.Fonte, ~c: S.Configuracao, +x: Fonte.Contexto,
  origens: OrigemDaRota(fonte, c, x)) -> ConteudoDaObservacao(c, x, dados_da_rota(fonte, c, x)):
  match x:
    case Fonte.Inicial{+m, +s, +pi}: conteudos_da_inicial(fonte, c, m, s, pi, Fonte.inicial(fonte, m), origens)
    case Fonte.Atendimento{+m, +s, +r}: conteudos_da_chamada(fonte, c, m, s, r, Fonte.chamada(fonte, m), origens)

def regra2_literal(~fonte: Fonte.Fonte, ~c: S.Configuracao, +x: Fonte.Contexto, +t: Nat, f: I.Fato,
  origens: OrigemDaRota(fonte, c, x),
  entrada: L.E<{Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
    L.E<{Fonte.cenario_contexto(c, x) == Fonte.cenario(fonte, Fonte.mundo(Fonte.cenario_contexto(c, x))) : I.Cenario},
      Fonte.da_rota(fonte, Fonte.cenario_contexto(c, x), t, f)>>) ->
  K.Regra2(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), Fonte.cenario_contexto(c, x), t):
  match entrada:
    case L.Ambos{nome, L.Ambos{canonico, observado}}:
      regra2_componentes(fonte, c, x, t, f, conteudos_da_rota(fonte, c, x, origens), nome, canonico, observado)

# O mundo usa a mesma configuracao e o mesmo snapshot calculado do historico.
def contexto_do_momento(~seed: Unit -> D.Estado, ~historico: Nat -> List<&2, Historico.Registro>, ~pi: String,
  +mundo: Nat, momento: Cenarios.Momento) -> Fonte.Contexto:
  match momento:
    case Cenarios.Inicializacao{}: Fonte.Inicial{mundo, seed(Unit{}), pi}
    case Cenarios.Atendimento{r}: Fonte.Atendimento{mundo, Historico.estado(historico(mundo), seed(Unit{})), r}

def contexto_representa_cenario(~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~pi: String, +mundo: Nat, +momento: Cenarios.Momento) ->
  {Fonte.cenario_contexto(c, contexto_do_momento(seed, historico, pi, mundo, momento)) ==
    Cenarios.de_momento(c, seed, historico, pi, momento, mundo) : I.Cenario}:
  match momento:
    case Cenarios.Inicializacao{}: {==}
    case Cenarios.Atendimento{r}: {==}

def mesmo_mundo_do_contexto(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +x: Fonte.Contexto,
  mundo_igual: {Fonte.mundo(Fonte.cenario_contexto(c, x)) == mundo : Nat},
  igual: {Fonte.cenario_contexto(c, x) == Fonte.cenario(fonte, mundo) : I.Cenario}) ->
  {Fonte.cenario_contexto(c, x) == Fonte.cenario(fonte, Fonte.mundo(Fonte.cenario_contexto(c, x))) : I.Cenario}:
  %Equal.sym(Nat, Fonte.mundo(Fonte.cenario_contexto(c, x)), mundo, mundo_igual) :
    {Fonte.cenario_contexto(c, x) == Fonte.cenario(fonte, _) : I.Cenario}
  igual

def regra2_no_canonico(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +x: Fonte.Contexto,
  mundo_igual: {Fonte.mundo(Fonte.cenario_contexto(c, x)) == mundo : Nat},
  igual: {Fonte.cenario_contexto(c, x) == Fonte.cenario(fonte, mundo) : I.Cenario}, origens: OrigemDaRota(fonte, c, x),
  +t: Nat, f: I.Fato, nome: {Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
  observado: Fonte.da_rota(fonte, Fonte.cenario(fonte, mundo), t, f)) ->
  K.Regra2(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), Fonte.cenario(fonte, mundo), t):
  Cinco.com_quatro({Fonte.cenario_contexto(c, x) == Fonte.cenario(fonte, mundo) : I.Cenario},
    K.Regra2(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), Fonte.cenario(fonte, mundo), t),
    Cinco.quatro_igualdades(I.Cenario, Fonte.cenario_contexto(c, x), Fonte.cenario(fonte, mundo), igual),
    i1 => i2 => i3 => i4 =>
      %i1 : K.Regra2(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), _, t)
      regra2_literal(fonte, c, x, t, f, origens, L.Ambos{nome, L.Ambos{
        mesmo_mundo_do_contexto(fonte, c, mundo, x, mundo_igual, i2),
        (%Equal.sym(I.Cenario, Fonte.cenario_contexto(c, x), Fonte.cenario(fonte, mundo), i3) :
          Fonte.da_rota(fonte, _, t, f) observado)}}))

def contexto_conserva_mundo(~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~pi: String, +mundo: Nat, momento: Cenarios.Momento) ->
  {Fonte.mundo(Fonte.cenario_contexto(c, contexto_do_momento(seed, historico, pi, mundo, momento))) == mundo : Nat}:
  match momento:
    case Cenarios.Inicializacao{}: {==}
    case Cenarios.Atendimento{r}: {==}

def OrigemDoModelo(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String, +mundo: Nat) -> Type:
  OrigemDaRota(Modelo.fonte(base, c, seed, historico, momento, pi), c,
    contexto_do_momento(seed, historico, pi, mundo, momento(mundo)))

def regra2_da_origem(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String,
  -x: I.Cenario, +mundo: Nat, origens: OrigemDoModelo(base, c, seed, historico, momento, pi, mundo),
  +t: Nat, f: I.Fato,
  entrada: L.E<{Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)) ==
      Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)) : String},
    L.E<{x == Fonte.cenario(Modelo.fonte(base, c, seed, historico, momento, pi), mundo) : I.Cenario},
      Fonte.da_rota(Modelo.fonte(base, c, seed, historico, momento, pi),
        Fonte.cenario(Modelo.fonte(base, c, seed, historico, momento, pi), mundo), t, f)>>) ->
  K.Regra2(f, Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momento, pi)),
    Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)), x, t):
  match entrada:
    case L.Ambos{nome, L.Ambos{igual, observado}}:
      %Equal.sym(I.Cenario, x, Fonte.cenario(Modelo.fonte(base, c, seed, historico, momento, pi), mundo), igual) :
        K.Regra2(f, Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momento, pi)),
          Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)), _, t)
      regra2_no_canonico(Modelo.fonte(base, c, seed, historico, momento, pi), c, mundo,
        contexto_do_momento(seed, historico, pi, mundo, momento(mundo)),
        contexto_conserva_mundo(c, seed, historico, pi, mundo, momento(mundo)),
        Equal.trans(I.Cenario,
          Fonte.cenario_contexto(c, contexto_do_momento(seed, historico, pi, mundo, momento(mundo))),
          Cenarios.canonico(c, seed, historico, momento, pi, mundo),
          Fonte.cenario(Modelo.fonte(base, c, seed, historico, momento, pi), mundo),
          contexto_representa_cenario(c, seed, historico, pi, mundo, momento(mundo)),
          Equal.sym(I.Cenario, Fonte.cenario(Modelo.fonte(base, c, seed, historico, momento, pi), mundo),
            Cenarios.canonico(c, seed, historico, momento, pi, mundo), Modelo.cenario_do_modelo(base, c, seed, historico, momento, pi, mundo))),
        origens, t, f, nome, observado)

def lei2_do_cenario(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String,
  origens: @mundo: Nat -> OrigemDoModelo(base, c, seed, historico, momento, pi, mundo),
  x: I.Cenario, +t: Nat, f: I.Fato,
  observado: I.Acontece(Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momento, pi)),
    Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)), x, t, f)) ->
  K.Regra2(f, Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momento, pi)),
    Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)), x, t):
  match x:
    case I.Inicializar{+m, original, +s, +prova}:
      regra2_da_origem(base, c, seed, historico, momento, pi, I.Inicializar{m, original, s, prova}, m, origens(m), t, f,
        Fonte.eliminar_fato(Modelo.fonte(base, c, seed, historico, momento, pi),
          Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)), I.Inicializar{m, original, s, prova}, t, f, observado))
    case I.Atender{+m, original, +s, +entrada}:
      regra2_da_origem(base, c, seed, historico, momento, pi, I.Atender{m, original, s, entrada}, m, origens(m), t, f,
        Fonte.eliminar_fato(Modelo.fonte(base, c, seed, historico, momento, pi),
          Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)), I.Atender{m, original, s, entrada}, t, f, observado))

def lei2_do_modelo(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String,
  origens: @mundo: Nat -> OrigemDoModelo(base, c, seed, historico, momento, pi, mundo)) ->
  K.Lei2(Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momento, pi)),
    Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi))):
  x => +t => f => observado => lei2_do_cenario(base, c, seed, historico, momento, pi, origens, x, t, f, observado)
