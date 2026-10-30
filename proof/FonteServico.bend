# Origem e ambiente do protocolo. JuizoSintatico e sintaxe, nao um checker bool.
# As familias elabora/deriva sao as relacoes do sistema oficial; soundness e
# refinamento sao contratos separados. Este modulo nao concede Lei1..Lei8.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Interface.bend as I
import ../contrato/Logica.bend as L
import ../contrato/Recursos.bend as X
import ../contrato/Semantica.bend as S
import ./ProtocoloServico.bend as Q
import ./RotasServico.bend as R
import ../contrato/Protocolo.bend as P
import ../contrato/Requisitos.bend as Req
import ../src/Nucleo.bend as N
import ./ExecucaoServico.bend as Exec
import ../contrato/Bytes.bend as B
import ../src/Entrada.bend as E
import ./EntradaRelacoes.bend as Mensagens
import ./FasesServico.bend as Fases
import ../src/Configuracao.bend as Config
import ./Configuracao.bend as Configuracao
import ../contrato/LAWS.bend as K
import ../src/Transporte.bend as T
import ./Transporte.bend as Transporte
import ./Fundamentos.bend as F

type ArquivoFonte is Data:
  ArquivoFonte{caminho: String, conteudo: String}

# Denota o termo declarado nesses modulos fechados. Ser dado nao e prova de
# derivabilidade: essa pertence a relacao logica oficial, nunca ao bit Aceitou.
type JuizoSintatico is Data:
  JuizoSintatico{modulos: List<&2, ArquivoFonte>, entrada: String, declaracao: String}

# O seed so participa da inicializacao/metateoria, nao do Book do cliente.
type InicialData is Data:
  InicialData{configuracao_fonte: JuizoSintatico, estado_fonte: JuizoSintatico,
    prova_fonte: JuizoSintatico, juizo: R.Juizo, resultado: R.ResultadoInicial, micro: R.Micro}

type ChamadaData is Data:
  ChamadaData{configuracao_fonte: JuizoSintatico, programa_fonte: JuizoSintatico,
    certificado_fonte: JuizoSintatico, termina_fonte: JuizoSintatico,
    estado: List<&2, U32>, ferramentas: R.DadosFerramentas, micro: R.Micro}

# O contexto de consulta e dado; a configuracao fechada nao e copiada.
type Contexto is Data:
  Inicial{mundo: Nat, estado: D.Estado, prova: String}
  Atendimento{mundo: Nat, estado: D.Estado, entrada: X.Recepcao}

def cenario_contexto(~c: S.Configuracao, x: Contexto) -> I.Cenario:
  match x:
    case Inicial{m, s, pi}: I.Inicializar{m, c, s, pi}
    case Atendimento{m, s, r}: I.Atender{m, c, s, r}

def PedidoDaFase(~c: S.Configuracao, +x: Contexto, fase: R.FaseAntes) -> Type:
  match fase:
    case R.AntesEntrada{}: Unit
    case R.AposReceber{r}: I.RequisicaoRecebida(cenario_contexto(c, x), r)
    case R.AposAutenticar{r, ctx}: I.RequisicaoRecebida(cenario_contexto(c, x), r)
    case R.AposVerificar{r, ctx}: I.RequisicaoRecebida(cenario_contexto(c, x), r)
    case R.Executando{r, ctx, qs}: I.RequisicaoRecebida(cenario_contexto(c, x), r)
    case R.AposPreparar{r, ctx, qs, p}: I.RequisicaoRecebida(cenario_contexto(c, x), r)

def PedidoDoCaso(~c: S.Configuracao, +x: Contexto, caso: R.Caso) -> Type:
  match caso:
    case R.AutRecusa{r, entrega}: I.RequisicaoRecebida(cenario_contexto(c, x), r)
    case R.GateRecusa{r, ctx, entrega}: I.RequisicaoRecebida(cenario_contexto(c, x), r)
    case R.Executada{r, ctx, qs, p, entrega}: I.RequisicaoRecebida(cenario_contexto(c, x), r)
    case R.FatalAposPublicacao{r, ctx, qs, p, etapa, id}: I.RequisicaoRecebida(cenario_contexto(c, x), r)
    case R.FalhaAntes{fase, etapa, id, fatal, entrega}: PedidoDaFase(c, x, fase)
    case R.Pendente{fase}: PedidoDaFase(c, x, fase)
    case _: Unit

type ObservacaoData is Data:
  ObservacaoData{inicial: Maybe<&2, D.Estado>, quadros: List<&2, Q.Quadro>,
    programa_fonte: Maybe<&2, JuizoSintatico>}

def construir_inicial(~identidade: String, c: S.Configuracao, +s: D.Estado, dados: InicialData) -> ObservacaoData:
  match dados:
    case InicialData{cf, sf, pf, juizo, resultado, micro}:
      ObservacaoData{None{}, R.gerar_resultado_inicial(c, identidade, s, juizo, resultado, micro), None{}}

def construir_chamada(c: S.Configuracao, +s: D.Estado, recepcao: X.Recepcao,
  dados: ChamadaData) -> ObservacaoData:
  match dados:
    case ChamadaData{cf, programa, certificado, termina, estado, ferramentas, micro}:
      ObservacaoData{Some{s}, R.gerar(c, recepcao, estado, s, ferramentas, micro), Some{programa}}

# Indice inerte: o ramo Inicializar nao possui programa de cliente.
# Nao e uma transacao oferecida nem um fallback de admissao.
def sem_programa() -> S.Programa:
  S.Programa{ctx => args => S.Recusar{D.VAusente{}}}

# Uma fonte fechada reprodutivel. Os contratos logicos nao sao booleans do
# checker. Nenhum campo concede uma lei do banco ou validade pos-publicacao.
type Fonte is Type:
  Fonte{identidade: String, artefato: String, cenarios: Nat -> I.Cenario,
    iniciais: Nat -> InicialData, chamadas: Nat -> ChamadaData,
    programa: JuizoSintatico -> S.Programa,
    elabora: S.Configuracao -> String -> S.Programa -> Type,
    deriva: S.Configuracao -> String -> Type -> Type,
    processavel: I.Cenario -> Type,
    falha: String -> I.Cenario -> Nat -> X.Etapa -> String -> Bool -> Type,
    entrega_falhou: String -> I.Cenario -> Nat -> Type}

def identidade(f: Fonte) -> String:
  Fonte{id, k, cs, ins, hs, ps, el, de, pr, fr, ef} = f
  id

def artefato(f: Fonte) -> String:
  Fonte{id, k, cs, ins, hs, ps, el, de, pr, fr, ef} = f
  k

def cenario(f: Fonte, mundo: Nat) -> I.Cenario:
  Fonte{id, k, cs, ins, hs, ps, el, de, pr, fr, ef} = f
  cs(mundo)

def inicial(f: Fonte, mundo: Nat) -> InicialData:
  Fonte{id, k, cs, ins, hs, ps, el, de, pr, fr, ef} = f
  ins(mundo)

def chamada(f: Fonte, mundo: Nat) -> ChamadaData:
  Fonte{id, k, cs, ins, hs, ps, el, de, pr, fr, ef} = f
  hs(mundo)

def programa(f: Fonte, fonte: JuizoSintatico) -> S.Programa:
  Fonte{id, k, cs, ins, hs, ps, el, de, pr, fr, ef} = f
  ps(fonte)

def de_origem(~fonte: Fonte, -c: S.Configuracao,
  inicial: Maybe<&2, D.Estado>, quadros: List<&2, Q.Quadro>,
  origem: Maybe<&2, JuizoSintatico>, t: Nat, f: I.Fato) -> Type:
  match origem:
    case None{}: Q.observa_servico(c, sem_programa(), inicial, quadros, t, f)
    case Some{origem}: Q.observa_servico(c, programa(fonte, origem), inicial, quadros, t, f)

def de_observacao(~fonte: Fonte, -c: S.Configuracao,
  dados: ObservacaoData, t: Nat, f: I.Fato) -> Type:
  match dados:
    case ObservacaoData{inicial, quadros, origem}: de_origem(fonte, c, inicial, quadros, origem, t, f)

# Uma unica rota por mundo: o parametro x apenas prova que descreve aquele
# cenario real. A geracao consulta sempre o cenario canonico, nao x de novo.
def da_rota(~fonte: Fonte, x: I.Cenario, t: Nat, f: I.Fato) -> Type:
  match x:
    case I.Inicializar{+mundo, c, +s, pi}:
      de_observacao(fonte, c, construir_inicial(identidade(fonte), c, s, inicial(fonte, mundo)), t, f)
    case I.Atender{+mundo, c, +s, recepcao}:
      de_observacao(fonte, c, construir_chamada(c, s, recepcao, chamada(fonte, mundo)), t, f)

def mundo(x: I.Cenario) -> Nat:
  match x:
    case I.Inicializar{m, c, s, pi}: m
    case I.Atender{m, c, s, r}: m

def observar_fonte(~fonte: Fonte, x: I.Cenario, t: Nat, f: I.Fato) -> Type:
  match x:
    case I.Inicializar{+mundo, c, +s, pi}:
      L.E<{I.Inicializar{mundo, c, s, pi} == cenario(fonte, mundo) : I.Cenario},
        da_rota(fonte, cenario(fonte, mundo), t, f)>
    case I.Atender{+mundo, c, +s, recepcao}:
      L.E<{I.Atender{mundo, c, s, recepcao} == cenario(fonte, mundo) : I.Cenario},
        da_rota(fonte, cenario(fonte, mundo), t, f)>

# Estas sao apenas duas direcoes do mesmo J, nao dois observadores.
def origem_literal_dividida(~fonte: Fonte, -x: I.Cenario, -y: I.Cenario, -t: Nat, -f: I.Fato,
  iguais: L.E<{x == y : I.Cenario}, {x == y : I.Cenario}>, obs: da_rota(fonte, y, t, f)) ->
  L.E<{x == y : I.Cenario}, da_rota(fonte, x, t, f)>:
  match iguais:
    case L.Ambos{guarda, substituicao}:
      L.Ambos{guarda, (%Equal.sym(I.Cenario, x, y, substituicao) : da_rota(fonte, _, t, f) obs)}

def origem_literal(~fonte: Fonte, -x: I.Cenario, -y: I.Cenario, -t: Nat, -f: I.Fato,
  igual: {x == y : I.Cenario}, obs: da_rota(fonte, y, t, f)) ->
  L.E<{x == y : I.Cenario}, da_rota(fonte, x, t, f)>:
  origem_literal_dividida(fonte, x, y, t, f, Q.igualdade_reabrivel(I.Cenario, x, y, igual), obs)

def origem_canonica(~fonte: Fonte, -x: I.Cenario, -y: I.Cenario, -t: Nat, -f: I.Fato,
  igual: {x == y : I.Cenario}, obs: da_rota(fonte, x, t, f)) ->
  L.E<{x == y : I.Cenario}, da_rota(fonte, y, t, f)>:
  %igual : L.E<{x == _ : I.Cenario}, da_rota(fonte, _, t, f)>
  L.Ambos{{==}, obs}

def elaboracao(f: Fonte, c: S.Configuracao, codigo: String, p: S.Programa) -> Type:
  Fonte{id, k, cs, ins, hs, ps, el, de, pr, fr, ef} = f
  el(c, codigo, p)

def derivacao(f: Fonte, c: S.Configuracao, texto: String, alvo: Type) -> Type:
  Fonte{id, k, cs, ins, hs, ps, el, de, pr, fr, ef} = f
  de(c, texto, alvo)

def processavel(f: Fonte, x: I.Cenario) -> Type:
  Fonte{id, k, cs, ins, hs, ps, el, de, pr, fr, ef} = f
  pr(x)

def falha(f: Fonte, codigo: String, x: I.Cenario, t: Nat,
  etapa: X.Etapa, nome: String, fatal: Bool) -> Type:
  Fonte{id, k, cs, ins, hs, ps, el, de, pr, fr, ef} = f
  fr(codigo, x, t, etapa, nome, fatal)

def falha_entrega(f: Fonte, codigo: String, x: I.Cenario, t: Nat) -> Type:
  Fonte{id, k, cs, ins, hs, ps, el, de, pr, fr, ef} = f
  ef(codigo, x, t)

def ambiente(~fonte: Fonte) -> I.Ambiente:
  I.Ambiente{identidade(fonte),
    c => codigo => p => elaboracao(fonte, c, codigo, p),
    c => texto => alvo => derivacao(fonte, c, texto, alvo),
    codigo => x => t => f => L.E<{codigo == artefato(fonte) : String},
      observar_fonte(fonte, x, t, f)>, x => processavel(fonte, x),
    codigo => x => t => etapa => nome => fatal => falha(fonte, codigo, x, t, etapa, nome, fatal),
    codigo => x => t => falha_entrega(fonte, codigo, x, t)}

# Intro/eliminacao da guarda do artefato. O conteudo restante conserva a
# igualdade ao cenario canonico e a consulta da rota realmente gerada.
def eliminar_fato(~fonte: Fonte, -k: String, -x: I.Cenario, -t: Nat, -f: I.Fato,
  fato: I.Acontece(ambiente(fonte), k, x, t, f)) ->
  L.E<{k == artefato(fonte) : String}, observar_fonte(fonte, x, t, f)>:
  fato

def introduzir_fato(~fonte: Fonte, -k: String, -x: I.Cenario, -t: Nat, -f: I.Fato,
  nome: {k == artefato(fonte) : String}, obs: observar_fonte(fonte, x, t, f)) ->
  I.Acontece(ambiente(fonte), k, x, t, f):
  L.Ambos{nome, obs}

def fato_literal_do_mundo(~fonte: Fonte, -k: String, -x: I.Cenario, -m: Nat,
  -t: Nat, -f: I.Fato, entrada: L.E<{k == artefato(fonte) : String},
    L.E<{x == cenario(fonte, m) : I.Cenario}, da_rota(fonte, cenario(fonte, m), t, f)>>) ->
  L.E<{k == artefato(fonte) : String}, L.E<{x == cenario(fonte, m) : I.Cenario}, da_rota(fonte, x, t, f)>>:
  match entrada:
    case L.Ambos{nome, L.Ambos{igual, obs}}:
      L.Ambos{nome, origem_literal(fonte, x, cenario(fonte, m), t, f, igual, obs)}

def eliminar_fato_literal(~fonte: Fonte, -k: String, x: I.Cenario, -t: Nat, -f: I.Fato,
  fato: I.Acontece(ambiente(fonte), k, x, t, f)) ->
  L.E<{k == artefato(fonte) : String},
    L.E<{x == cenario(fonte, mundo(x)) : I.Cenario}, da_rota(fonte, x, t, f)>>:
  match x:
    case I.Inicializar{+m, c, +s, +pi}: fato_literal_do_mundo(fonte, k, I.Inicializar{m, c, s, pi}, m, t, f, fato)
    case I.Atender{+m, c, +s, +r}: fato_literal_do_mundo(fonte, k, I.Atender{m, c, s, r}, m, t, f, fato)

def fato_canonico_do_mundo(~fonte: Fonte, -k: String, -x: I.Cenario, -m: Nat,
  -t: Nat, -f: I.Fato, entrada: L.E<{k == artefato(fonte) : String},
    L.E<{x == cenario(fonte, m) : I.Cenario}, da_rota(fonte, x, t, f)>>) ->
  L.E<{k == artefato(fonte) : String},
    L.E<{x == cenario(fonte, m) : I.Cenario}, da_rota(fonte, cenario(fonte, m), t, f)>>:
  match entrada:
    case L.Ambos{nome, L.Ambos{igual, obs}}:
      L.Ambos{nome, origem_canonica(fonte, x, cenario(fonte, m), t, f, igual, obs)}

def introduzir_fato_literal(~fonte: Fonte, -k: String, x: I.Cenario, -t: Nat, -f: I.Fato,
  entrada: L.E<{k == artefato(fonte) : String},
    L.E<{x == cenario(fonte, mundo(x)) : I.Cenario}, da_rota(fonte, x, t, f)>>) ->
  I.Acontece(ambiente(fonte), k, x, t, f):
  match x:
    case I.Inicializar{+m, c, +s, +pi}: fato_canonico_do_mundo(fonte, k, I.Inicializar{m, c, s, pi}, m, t, f, entrada)
    case I.Atender{+m, c, +s, +r}: fato_canonico_do_mundo(fonte, k, I.Atender{m, c, s, r}, m, t, f, entrada)

# Resultado do executor: equacoes das funcoes reais e da sequencia gerada.
# Nenhuma preservacao de leis/estado e recebida aqui como premissa.
def PrefixoReal(~fonte: Fonte,
  -c: S.Configuracao, -s: D.Estado, -r: P.Requisicao, -ctx: D.Contexto,
  +origem: JuizoSintatico, -quadros: List<&2, Q.QuadroExec>) -> Type:
  &n: Nat -> {quadros == Exec.gerar(n,
    N.iniciar(programa(fonte, origem), ctx, I.argumentos(r), s), S.esquema(c)) : List<&2, Q.QuadroExec>}

def FinalReal(~fonte: Fonte,
  -c: S.Configuracao, -s: D.Estado, -r: P.Requisicao, -ctx: D.Contexto,
  +origem: JuizoSintatico, -quadros: List<&2, Q.QuadroExec>, -preparada: N.Preparada) -> Type:
  &n: Nat -> &w: D.Estado -> &ts: List<&2, S.Evento> -> &proposta: S.Resposta ->
    L.E<{quadros == Exec.gerar(n, N.iniciar(programa(fonte, origem), ctx, I.argumentos(r), s),
      S.esquema(c)) : List<&2, Q.QuadroExec>},
      L.E<{N.percorrer(n, N.iniciar(programa(fonte, origem), ctx, I.argumentos(r), s), S.esquema(c)) ==
        S.Final{w, ts, proposta} : S.Percurso},
        {N.preparar(N.Parada{w, ts, proposta}, c) == Some{preparada} : Maybe<&2, N.Preparada>}>>

def PontoReal(~fonte: Fonte, -c: S.Configuracao,
  -s: D.Estado, -r: P.Requisicao, -ctx: D.Contexto, +origem: JuizoSintatico,
  ponto: R.PontoExec) -> Type:
  match ponto:
    case R.AntesDeComecar{}: Unit
    case R.Durante{quadros}: PrefixoReal(fonte, c, s, r, ctx, origem, quadros)
    case R.Preparou{quadros, preparada}: FinalReal(fonte, c, s, r, ctx, origem, quadros, preparada)

def SaidaReal(~fonte: Fonte, -c: S.Configuracao,
  -s: D.Estado, -r: P.Requisicao, -ctx: D.Contexto, +origem: JuizoSintatico,
  saida: R.SaidaExecucao) -> Type:
  match saida:
    case R.Finalizou{quadros, preparada}: FinalReal(fonte, c, s, r, ctx, origem, quadros, preparada)
    case R.ErroExecucao{ponto, etapa, id, fatal}: PontoReal(fonte, c, s, r, ctx, origem, ponto)
    case R.PendenteExecucao{ponto}: PontoReal(fonte, c, s, r, ctx, origem, ponto)

# A aprovacao da ferramenta fornece os juizos de elaboracao/derivacao exatos,
# e as denotacoes das duas declaracoes fechadas efetivamente checadas.
# Nao concede lei do banco nem validade de estado pos-publicacao.
def JuizoAceito(~fonte: Fonte, -c: S.Configuracao, -r: P.Requisicao,
  -ctx: D.Contexto, +origem: JuizoSintatico) -> Type:
  L.E<elaboracao(fonte, c, I.codigo(r), programa(fonte, origem)),
    L.E<derivacao(fonte, c, I.prova(r),
      Req.Certifica(c, I.codigo(r), programa(fonte, origem), ctx, I.argumentos(r))),
      L.E<Req.Certifica(c, I.codigo(r), programa(fonte, origem), ctx, I.argumentos(r)),
        L.E<derivacao(fonte, c, I.prova(r), I.ProgramaTermina(c, programa(fonte, origem))),
          I.ProgramaTermina(c, programa(fonte, origem))>>>>

def JuizoRecusado(~fonte: Fonte, -c: S.Configuracao, -r: P.Requisicao,
  -ctx: D.Contexto) -> Type:
  @p: S.Programa ->
    L.E<L.E<elaboracao(fonte, c, I.codigo(r), p), I.ProgramaTermina(c, p)>,
      derivacao(fonte, c, I.prova(r), Req.Certifica(c, I.codigo(r), p, ctx, I.argumentos(r)))> -> Empty

def JuizoClienteReal(~fonte: Fonte, -c: S.Configuracao, -r: P.Requisicao,
  -ctx: D.Contexto, +origem: JuizoSintatico, juizo: R.Juizo) -> Type:
  match juizo:
    case R.Aceitou{}: JuizoAceito(fonte, c, r, ctx, origem)
    case R.Recusou{}: JuizoRecusado(fonte, c, r, ctx)
    case R.ErroJuizo{id, fatal}: Unit
    case R.PendenteJuizo{}: Unit

# As denotacoes das declaracoes fechadas sao necessarias apenas depois
# da decisao do checker que as tornou observaveis. Nao incluem cronologia.
def JuizoDaFase(~fonte: Fonte, -c: S.Configuracao, +origem: JuizoSintatico,
  fase: R.FaseAntes) -> Type:
  match fase:
    case R.AposVerificar{r, ctx}: JuizoAceito(fonte, c, r, ctx, origem)
    case R.Executando{r, ctx, qs}: JuizoAceito(fonte, c, r, ctx, origem)
    case R.AposPreparar{r, ctx, qs, p}: JuizoAceito(fonte, c, r, ctx, origem)
    case _: Unit

def JuizoDoCaso(~fonte: Fonte, -c: S.Configuracao, +origem: JuizoSintatico,
  caso: R.Caso) -> Type:
  match caso:
    case R.GateRecusa{r, ctx, entrega}: JuizoRecusado(fonte, c, r, ctx)
    case R.Executada{r, ctx, qs, p, entrega}: JuizoAceito(fonte, c, r, ctx, origem)
    case R.FatalAposPublicacao{r, ctx, qs, p, etapa, id}: JuizoAceito(fonte, c, r, ctx, origem)
    case R.FalhaAntes{fase, etapa, id, fatal, entrega}: JuizoDaFase(fonte, c, origem, fase)
    case R.Pendente{fase}: JuizoDaFase(fonte, c, origem, fase)
    case _: Unit

# A configuracao visivel e sempre a da chamada, independentemente da rota.
def configuracao_de_origem(~fonte: Fonte,
  -c: S.Configuracao, ini: Maybe<&2, D.Estado>, qs: List<&2, Q.Quadro>,
  origem: Maybe<&2, JuizoSintatico>, t: Nat, -observada: S.Configuracao,
  fato: de_origem(fonte, c, ini, qs, origem, t, I.ConfiguracaoEmUso{observada})) ->
  {observada == c : S.Configuracao}:
  match origem:
    case None{}: L.e_direita({Q.posicao_observavel(qs, t) == True{} : Bool}, {observada == c : S.Configuracao}, fato)
    case Some{origem}: L.e_direita({Q.posicao_observavel(qs, t) == True{} : Bool}, {observada == c : S.Configuracao}, fato)

def configuracao_de_observacao(~fonte: Fonte,
  -c: S.Configuracao, dados: ObservacaoData, t: Nat, -observada: S.Configuracao,
  fato: de_observacao(fonte, c, dados, t, I.ConfiguracaoEmUso{observada})) ->
  {observada == c : S.Configuracao}:
  match dados:
    case ObservacaoData{ini, qs, origem}:
      configuracao_de_origem(fonte, c, ini, qs, origem, t, observada, fato)

def configuracao_da_rota(~fonte: Fonte, x: I.Cenario, t: Nat, -observada: S.Configuracao,
  fato: da_rota(fonte, x, t, I.ConfiguracaoEmUso{observada})) ->
  {observada == I.configuracao(x) : S.Configuracao}:
  match x:
    case I.Inicializar{+m, c, +s, pi}:
      configuracao_de_observacao(fonte, c, construir_inicial(identidade(fonte), c, s, inicial(fonte, m)), t, observada, fato)
    case I.Atender{+m, c, +s, r}:
      configuracao_de_observacao(fonte, c, construir_chamada(c, s, r, chamada(fonte, m)), t, observada, fato)

law configuracao_da_fonte:
  for ~fonte: Fonte
  for -k: String
  for x: I.Cenario
  for t: Nat
  for -observada: S.Configuracao
  for fato: I.Acontece(ambiente(fonte), k, x, t, I.ConfiguracaoEmUso{observada})
  {observada == I.configuracao(x) : S.Configuracao}
def configuracao_da_fonte(fonte, k, x, t, observada, fato):
  match x:
    case I.Inicializar{+m, c, +s, +pi}:
      match fato:
        case L.Ambos{nome, L.Ambos{canonico, obs}}:
          Equal.trans(S.Configuracao, observada, I.configuracao(cenario(fonte, m)), c,
            configuracao_da_rota(fonte, cenario(fonte, m), t, observada, obs),
            Equal.sym(S.Configuracao, c, I.configuracao(cenario(fonte, m)),
              Equal.cong(I.Cenario, S.Configuracao, I.configuracao, I.Inicializar{m, c, s, pi}, cenario(fonte, m), canonico)))
    case I.Atender{+m, c, +s, +r}:
      match fato:
        case L.Ambos{nome, L.Ambos{canonico, obs}}:
          Equal.trans(S.Configuracao, observada, I.configuracao(cenario(fonte, m)), c,
            configuracao_da_rota(fonte, cenario(fonte, m), t, observada, obs),
            Equal.sym(S.Configuracao, c, I.configuracao(cenario(fonte, m)),
              Equal.cong(I.Cenario, S.Configuracao, I.configuracao, I.Atender{m, c, s, r}, cenario(fonte, m), canonico)))

# Os termos abaixo sao as denotacoes das DUAS declaracoes fechadas e
# efetivamente checadas: Bindings.certificado e Bindings.termina. A fonte
# fixa seus corpos/alvos; o contrato da ferramenta liga a derivacao original
# a esses termos. Nao ha eliminador para Type arbitrario, axioma novo, ou
# callback de Lei4/Regra4/validade publicada.
def tornar_aceito(~fonte: Fonte, -c: S.Configuracao, -r: P.Requisicao,
  -ctx: D.Contexto, +origem: JuizoSintatico, +juizo: R.Juizo,
  aceito: {juizo == R.Aceitou{} : R.Juizo},
  prova: JuizoClienteReal(fonte, c, r, ctx, origem, juizo)) ->
  JuizoAceito(fonte, c, r, ctx, origem):
  %aceito : JuizoClienteReal(fonte, c, r, ctx, origem, _)
  prova

def certificado_de_juizo(~fonte: Fonte, -c: S.Configuracao,
  -r: P.Requisicao, -ctx: D.Contexto, +origem: JuizoSintatico,
  juizo: JuizoAceito(fonte, c, r, ctx, origem)) ->
  I.CertificadoValido(ambiente(fonte), c, r, ctx, programa(fonte, origem)):
  match juizo:
    case L.Ambos{elaborada, L.Ambos{derivada, L.Ambos{certificado, L.Ambos{td, termina}}}}:
      L.Ambos{L.Ambos{elaborada, termina}, L.Ambos{derivada, certificado}}

law fonte_aceita_fornece_certificado_exato:
  for ~fonte: Fonte
  for ~c: S.Configuracao
  for ~requisicoes: Nat -> P.Requisicao
  for ~contextos: Nat -> D.Contexto
  for ~origens: Nat -> JuizoSintatico
  for ~juizos: Nat -> R.Juizo
  for +mundo: Nat
  for aceito: {juizos(mundo) == R.Aceitou{} : R.Juizo}
  for testemunho: JuizoClienteReal(fonte, c, requisicoes(mundo), contextos(mundo), origens(mundo), juizos(mundo))
  I.CertificadoValido(ambiente(fonte), c, requisicoes(mundo), contextos(mundo), programa(fonte, origens(mundo)))
def fonte_aceita_fornece_certificado_exato(fonte, c, requisicoes, contextos, origens, juizos, mundo, aceito, testemunho):
  certificado_de_juizo(fonte, c, requisicoes(mundo), contextos(mundo), origens(mundo),
    tornar_aceito(fonte, c, requisicoes(mundo), contextos(mundo), origens(mundo), juizos(mundo), aceito, testemunho))

# Inicializacao: somente a declaracao fechada de validade do seed, nunca a
# validade de um estado publicado depois de executar uma transacao.
def JuizoInicialReal(~fonte: Fonte, -c: S.Configuracao, -s: D.Estado,
  -pi: String, juizo: R.Juizo) -> Type:
  match juizo:
    case R.Aceitou{}: L.E<derivacao(fonte, c, pi, Req.Valido(c, s)), Req.Valido(c, s)>
    case _: Unit

def inicial_tornar_aceito(~fonte: Fonte, -c: S.Configuracao, -s: D.Estado,
  -pi: String, +juizo: R.Juizo, igual: {juizo == R.Aceitou{} : R.Juizo},
  origem: JuizoInicialReal(fonte, c, s, pi, juizo)) ->
  L.E<derivacao(fonte, c, pi, Req.Valido(c, s)), Req.Valido(c, s)>:
  %igual : JuizoInicialReal(fonte, c, s, pi, _)
  origem

law fonte_inicial_aceita_e_valida:
  for ~fonte: Fonte
  for ~c: S.Configuracao
  for ~estados: Nat -> D.Estado
  for ~provas: Nat -> String
  for ~juizos: Nat -> R.Juizo
  for +mundo: Nat
  for aceito: {juizos(mundo) == R.Aceitou{} : R.Juizo}
  for testemunho: JuizoInicialReal(fonte, c, estados(mundo), provas(mundo), juizos(mundo))
  L.E<I.Deriva(ambiente(fonte), c, provas(mundo), Req.Valido(c, estados(mundo))), Req.Valido(c, estados(mundo))>
def fonte_inicial_aceita_e_valida(fonte, c, estados, provas, juizos, mundo, aceito, testemunho):
  inicial_tornar_aceito(fonte, c, estados(mundo), provas(mundo), juizos(mundo), aceito, testemunho)

# A mensagem pode falhar. Se ela devolve Pronta, o snapshot privado e o mesmo
# que o controlador publicou; a identidade e calculada, nao presumida.
def pronta_snapshot(-s: D.Estado, -decodificado: D.Estado, -r: P.Requisicao,
  -br: List<&2, U32>, -cap: Maybe<&2, B.Numero64>,
  fiel: Mensagens.LimiteMensagemFiel(E.Pronta{decodificado, r}, s, br, cap)) ->
  {decodificado == s : D.Estado}:
  match fiel:
    case (teto, L.Ambos{medida, L.Ambos{mesmo, requisicao}}): mesmo

law mensagem_pronta_conserva_snapshot:
  for +cap: Maybe<&2, B.Numero64>
  for +br: List<&2, U32>
  for +s: D.Estado
  for -decodificado: D.Estado
  for -r: P.Requisicao
  for pronta: {E.ler_mensagem(cap, br, s) == E.Pronta{decodificado, r} : E.PreAutenticacao}
  {decodificado == s : D.Estado}
def mensagem_pronta_conserva_snapshot(cap, br, s, decodificado, r, pronta):
  pronta_snapshot(s, decodificado, r, br, cap,
    (%pronta : Mensagens.LimiteMensagemFiel(_, s, br, cap)
      Mensagens.ler_mensagem_fiel(cap, br, s)))

law autenticar_pacote_usa_snapshot_canonico:
  for +cap: Maybe<&2, B.Numero64>
  for +br: List<&2, U32>
  for +s: D.Estado
  for +decodificado: D.Estado
  for +r: P.Requisicao
  for -pre: E.PreAutenticacao
  for canonico: {pre == E.ler_mensagem(cap, br, s) : E.PreAutenticacao}
  for pronta: {pre == E.Pronta{decodificado, r} : E.PreAutenticacao}
  {D.autenticar(decodificado, I.credencial(r)) == D.autenticar(s, I.credencial(r)) : Maybe<&2, D.Contexto>}
def autenticar_pacote_usa_snapshot_canonico(cap, br, s, decodificado, r, pre, canonico, pronta):
  Equal.cong(D.Estado, Maybe<&2, D.Contexto>, estado => D.autenticar(estado, I.credencial(r)), decodificado, s,
    mensagem_pronta_conserva_snapshot(cap, br, s, decodificado, r,
      Equal.trans(E.PreAutenticacao, E.ler_mensagem(cap, br, s), pre, E.Pronta{decodificado, r},
        Equal.sym(E.PreAutenticacao, pre, E.ler_mensagem(cap, br, s), canonico), pronta)))

# A observacao literal e ligada a unica rota canonica pelo mesmo J.
def introduzir_inicial_da_rota(~fonte: Fonte, ~c: S.Configuracao, +mundo: Nat,
  +s: D.Estado, +pi: String, +cf: JuizoSintatico, +sf: JuizoSintatico,
  +pf: JuizoSintatico, +j: R.Juizo, +resultado: R.ResultadoInicial, +micro: R.Micro, +t: Nat, -f: I.Fato,
  canonico: {I.Inicializar{mundo, c, s, pi} == cenario(fonte, mundo) : I.Cenario},
  origem: {inicial(fonte, mundo) == InicialData{cf, sf, pf, j, resultado, micro} : InicialData},
  obs: Q.observa_servico(c, sem_programa(), None{}, R.gerar_resultado_inicial(c, identidade(fonte), s, j, resultado, micro), t, f)) ->
  I.Acontece(ambiente(fonte), artefato(fonte), I.Inicializar{mundo, c, s, pi}, t, f):
  L.Ambos{{==},
    (%canonico : L.E<{I.Inicializar{mundo, c, s, pi} == _ : I.Cenario}, da_rota(fonte, _, t, f)>
      L.Ambos{{==},
        (%Equal.sym(InicialData, inicial(fonte, mundo), InicialData{cf, sf, pf, j, resultado, micro}, origem) :
          de_observacao(fonte, c, construir_inicial(identidade(fonte), c, s, _), t, f) obs)})}

def iniciar_da_consulta(~fonte: Fonte, ~c: S.Configuracao, +mundo: Nat,
  +s: D.Estado, +pi: String, +cf: JuizoSintatico, +sf: JuizoSintatico,
  +pf: JuizoSintatico, +micro: R.Micro,
  canonico: {I.Inicializar{mundo, c, s, pi} == cenario(fonte, mundo) : I.Cenario},
  origem: {inicial(fonte, mundo) == InicialData{cf, sf, pf, R.Aceitou{}, R.Finalizada{}, micro} : InicialData},
  consulta: &t: Nat -> {Q.consultar(R.gerar_inicial(c, identidade(fonte), s, R.Aceitou{}, micro), t) == Some{Q.Iniciada{s}} : Maybe<&2, Q.Quadro>}) ->
  I.EmAlgumMomento(ambiente(fonte), artefato(fonte), I.Inicializar{mundo, c, s, pi}, I.InstanciaIniciou{s}):
  match consulta:
    case (+t, obtida):
      (t, introduzir_inicial_da_rota(fonte, c, mundo, s, pi, cf, sf, pf, R.Aceitou{}, R.Finalizada{}, micro, t, I.InstanciaIniciou{s}, canonico, origem,
        Q.consulta_estabelece_observacao(c, sem_programa(), R.gerar_inicial(c, identidade(fonte), s, R.Aceitou{}, micro),
          t, Q.Iniciada{s}, I.InstanciaIniciou{s}, obtida, {==})))

law inicializacao_aprovada_atinge_inicio:
  for ~fonte: Fonte
  for ~c: S.Configuracao
  for +mundo: Nat
  for +s: D.Estado
  for +pi: String
  for +cf: JuizoSintatico
  for +sf: JuizoSintatico
  for +pf: JuizoSintatico
  for +micro: R.Micro
  for canonico: {I.Inicializar{mundo, c, s, pi} == cenario(fonte, mundo) : I.Cenario}
  for origem: {inicial(fonte, mundo) == InicialData{cf, sf, pf, R.Aceitou{}, R.Finalizada{}, micro} : InicialData}
  for configurada: {Config.valida(c, identidade(fonte)) == True{} : Bool}
  for valido: Req.Valido(c, s)
  I.EmAlgumMomento(ambiente(fonte), artefato(fonte), I.Inicializar{mundo, c, s, pi}, I.InstanciaIniciou{s})
def inicializacao_aprovada_atinge_inicio(fonte, c, mundo, s, pi, cf, sf, pf, micro, canonico, origem, configurada, valido):
  iniciar_da_consulta(fonte, c, mundo, s, pi, cf, sf, pf, micro, canonico, origem,
    Fases.seed_valido_tem_instancia_apos_aprovacao(c, identidade(fonte), s, micro, configurada, valido))

# Este antecedente e composto dos retornos das primitivas de verificacao,
# worker e cleanup. Entrega somente dados/fonte/resultados, nunca o evento
# de inicio. Nao e uma nova definicao de Processavel nem progresso assumido.
def InicialCompleta(~fonte: Fonte, -c: S.Configuracao, -mundo: Nat,
  -s: D.Estado, -pi: String) -> Type:
  I.Processavel(ambiente(fonte), I.Inicializar{mundo, c, s, pi}) ->
    I.Deriva(ambiente(fonte), c, pi, Req.Valido(c, s)) ->
      &cf: JuizoSintatico -> &sf: JuizoSintatico -> &pf: JuizoSintatico -> &micro: R.Micro ->
        L.E<{I.Inicializar{mundo, c, s, pi} == cenario(fonte, mundo) : I.Cenario},
          {inicial(fonte, mundo) == InicialData{cf, sf, pf, R.Aceitou{}, R.Finalizada{}, micro} : InicialData}>

def inicio_apos_checker(~fonte: Fonte, ~c: S.Configuracao, +mundo: Nat,
  +s: D.Estado, +pi: String, configurada: {Config.valida(c, identidade(fonte)) == True{} : Bool},
  valido: Req.Valido(c, s), resultado: &cf: JuizoSintatico -> &sf: JuizoSintatico ->
    &pf: JuizoSintatico -> &micro: R.Micro ->
      L.E<{I.Inicializar{mundo, c, s, pi} == cenario(fonte, mundo) : I.Cenario},
        {inicial(fonte, mundo) == InicialData{cf, sf, pf, R.Aceitou{}, R.Finalizada{}, micro} : InicialData}>) ->
  I.EmAlgumMomento(ambiente(fonte), artefato(fonte), I.Inicializar{mundo, c, s, pi}, I.InstanciaIniciou{s}):
  match resultado:
    case (cf, sf, pf, micro, L.Ambos{canonico, origem}):
      inicializacao_aprovada_atinge_inicio(fonte, c, mundo, s, pi, cf, sf, pf, micro, canonico, origem, configurada, valido)

def progresso_inicial_possivel(~fonte: Fonte, ~c: S.Configuracao, +mundo: Nat,
  +s: D.Estado, +pi: String, completa: InicialCompleta(fonte, c, mundo, s, pi),
  possivel: K.InicializacaoPossivel(ambiente(fonte), c, s, pi),
  processavel: I.Processavel(ambiente(fonte), I.Inicializar{mundo, c, s, pi})) ->
  I.EmAlgumMomento(ambiente(fonte), artefato(fonte), I.Inicializar{mundo, c, s, pi}, I.InstanciaIniciou{s}):
  match possivel:
    case L.Ambos{configurada, L.Ambos{derivada, valido}}:
      inicio_apos_checker(fonte, c, mundo, s, pi,
        Configuracao.configuracao_original_valida_e_aceita(ambiente(fonte), c, configurada), valido,
        completa(processavel, derivada))

law progresso_da_inicializacao:
  for ~fonte: Fonte
  for ~c: S.Configuracao
  for +mundo: Nat
  for +s: D.Estado
  for +pi: String
  for completa: InicialCompleta(fonte, c, mundo, s, pi)
  K.Progresso(I.Inicializar{mundo, c, s, pi}, ambiente(fonte), artefato(fonte))
def progresso_da_inicializacao(fonte, c, mundo, s, pi, completa):
  possivel => processavel => progresso_inicial_possivel(fonte, c, mundo, s, pi, completa, possivel, processavel)

# Os dois marcos do fim completo existem por construcao, inclusive em recusa.
law fim_completo_pontos:
  for +s: D.Estado
  for +r: S.Resposta
  for +bs: List<&2, U32>
  for +proxima: Bool
  L.E<{Q.consultar(R.render_conclusao(N.Conclusao{s, r, bs}, False{}, R.Completa{proxima}),
      Q.tamanho(Con{Q.Preparada{r, bs}, R.render_publicacao(r, s)})) == Some{Q.Concluida{r, s, False{}}} : Maybe<&2, Q.Quadro>},
    {Q.consultar(R.render_conclusao(N.Conclusao{s, r, bs}, False{}, R.Completa{proxima}),
      Succ{Q.tamanho(Con{Q.Preparada{r, bs}, R.render_publicacao(r, s)})}) == Some{Q.Entregue{bs}} : Maybe<&2, Q.Quadro>}>
def fim_completo_pontos(s, r, bs, proxima):
  Q.dois_quadros_apos_prefixo(Con{Q.Preparada{r, bs}, R.render_publicacao(r, s)},
    R.depois_entrega(False{}, s, proxima), Q.Concluida{r, s, False{}}, Q.Entregue{bs})

# A origem da requisicao e o segundo bloco REAL montado no pipe privado.
# Nao pressupoe que o decoder ou a autenticacao devolveram o pedido correto.
def ligar_corpo_recebido(-bs: List<&2, U32>, +be: List<&2, U32>, +br: List<&2, U32>,
  -r: P.Requisicao, -mundo: Nat, -c: S.Configuracao, -s: D.Estado, -entrada: X.Recepcao,
  separado: {T.separar(bs) == Some{T.Partes{be, br}} : Maybe<&2, T.Partes>},
  recebido: {X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{br} : X.Disposicao},
  origem: Mensagens.CorpoParaInterface(bs, r, mundo, c, s, entrada)) ->
  I.RequisicaoRecebida(I.Atender{mundo, c, s, entrada}, r):
  match origem:
    case (+be2, +br2, L.Ambos{separado2, L.Ambos{canonico, ligar}}):
      ligar(Equal.trans(X.Disposicao, X.decidir_recepcao(c, entrada), X.ProcessarCorpo{br}, X.ProcessarCorpo{br2}, recebido,
        Equal.cong(List<&2, U32>, X.Disposicao, corpo => X.ProcessarCorpo{corpo}, br, br2,
          Equal.cong(T.Partes, List<&2, U32>, Transporte.segunda, T.Partes{be, br}, T.Partes{be2, br2},
            F.algum_injetivo(T.Partes, T.Partes{be, br}, T.Partes{be2, br2},
              Equal.trans(Maybe<&2, T.Partes>, Some{T.Partes{be, br}}, T.separar(bs), Some{T.Partes{be2, br2}},
                Equal.sym(Maybe<&2, T.Partes>, T.separar(bs), Some{T.Partes{be, br}}, separado), separado2))))))

law requisicao_pronta_veio_do_corpo:
  for +be: List<&2, U32>
  for +br: List<&2, U32>
  for +bs: List<&2, U32>
  for +e: D.Esquema
  for +l: S.Limites
  for +s: D.Estado
  for +r: P.Requisicao
  for -mundo: Nat
  for -c: S.Configuracao
  for +entrada: X.Recepcao
  for montagem: {T.juntar(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>}
  for octetos_e: {B.octetos_validos(be) == True{} : Bool}
  for octetos_r: {B.octetos_validos(br) == True{} : Bool}
  for recebido: {X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{br} : X.Disposicao}
  for pronta: {E.decodificar(bs, e, l) == E.Pronta{s, r} : E.PreAutenticacao}
  I.RequisicaoRecebida(I.Atender{mundo, c, s, entrada}, r)
def requisicao_pronta_veio_do_corpo(be, br, bs, e, l, s, r, mundo, c, entrada, montagem, octetos_e, octetos_r, recebido, pronta):
  ligar_corpo_recebido(bs, be, br, r, mundo, c, s, entrada,
    Transporte.separar_inverte_toda_montagem_valida(be, br, bs, montagem, octetos_e, octetos_r), recebido,
    Mensagens.pronta_fornece_corpo_e_ligacao_a_interface_original(bs, e, l, s, r, mundo, c, entrada, pronta))
