# Fronteira entre o contrato matematico e um artefato nativo concreto.
#
# `Ambiente` e fixado pelo projeto (Bend, compilador, verificador e host).
# Nao e fornecido pelo cliente nem escolhido pelo implementador para fazer
# uma prova passar. Seus campos denotam semantica, nao booleans de confianca.
# `observa` descreve TODOS os fatos reais da execucao do artefato; nao e
# um log que o proprio artefato possa devolver ou omitir.
# Toda inspecao/efeito do programa fora dos eventos admitidos DEVE ser
# mapeada para InspecaoNaoModelada/EfeitoNaoModelado. Uma fronteira que
# silencie esses fatos nao e uma instancia deste contrato.
# Implementar/provar essa ligacao e parte da fronteira tecnica declarada.
# `nativo`/`k` identifica o artefato COMPLETO interpretado por este ambiente,
# com suas dependencias fixadas. Um nome/hash sem esse vinculo nao basta.
import Base
import ./Dados.bend as D
import ./Semantica.bend as S
import ./Requisitos.bend as R
import ./Protocolo.bend as P
import ./Recursos.bend as X
import ./Logica.bend as L

# mundo distingue execucoes e escolhas do host; e um indice semantico,
# nao um identificador ou recurso novo na interface do banco.
type Cenario is Type:
  Inicializar{mundo: Nat, configuracao: S.Configuracao, estado: D.Estado, prova: String}
  Atender{mundo: Nat, configuracao: S.Configuracao, estado: D.Estado, entrada: X.Recepcao}

def configuracao(x: Cenario) -> S.Configuracao:
  match x:
    case Inicializar{mundo, c, s, pi}:
      c
    case Atender{mundo, c, s, entrada}:
      c

def inicial(x: Cenario) -> D.Estado:
  match x:
    case Inicializar{mundo, c, s, pi}:
      s
    case Atender{mundo, c, s, entrada}:
      s

def credencial(r: P.Requisicao) -> String:
  P.Requisicao{cred, cod, arg, pi} = r
  cred

def codigo(r: P.Requisicao) -> String:
  P.Requisicao{cred, cod, arg, pi} = r
  cod

def argumentos(r: P.Requisicao) -> D.Valor:
  P.Requisicao{cred, cod, arg, pi} = r
  arg

def prova(r: P.Requisicao) -> String:
  P.Requisicao{cred, cod, arg, pi} = r
  pi

type Fato is Type:
  ConfiguracaoEmUso{configuracao: S.Configuracao}
  InspecaoNaoModelada{descricao: String}
  EfeitoNaoModelado{descricao: String}
  InstanciaIniciou{estado: D.Estado}
  InicializacaoRecusada{status: S.Status}
  ProvaInicialAceita{}
  Codificou{valor: D.Valor, resultado: Maybe<&2, List<&2, U32>>}
  Decodificou{bytes: List<&2, U32>, resultado: Maybe<&2, D.Valor>}
  Guardou{estado: D.Estado, representacao: List<&2, U32>, abstracao: D.Estado}
  # Operacao logica DO PROGRAMA. Leituras internas de autenticacao ou
  # validacao que nao entregam dados ao programa nao sao este evento.
  Operou{esquema: D.Esquema, estado: D.Estado, operacao: D.Operacao, resultado: D.ResultadoOp}
  ConferiuComprimento{posicao: Nat, quantidade: Nat}
  AlocouCampo{posicao: Nat, quantidade: Nat}
  LeuCorpo{lidos_antes: Nat, quantidade: Nat, declarado: Nat}
  RecebeuRequisicao{requisicao: P.Requisicao}
  Autenticou{requisicao: P.Requisicao, contexto: Maybe<&2, D.Contexto>}
  CertificadoAceito{requisicao: P.Requisicao, contexto: D.Contexto, programa: S.Programa}
  CertificadoRejeitado{requisicao: P.Requisicao, contexto: D.Contexto}
  ProgramaComecou{requisicao: P.Requisicao, contexto: D.Contexto, programa: S.Programa}
  Avaliou{requisicao: P.Requisicao, contexto: D.Contexto, programa: S.Programa, percurso: S.Percurso}
  Preparou{resposta: S.Resposta, bytes: List<&2, U32>}
  Publicou{estado: D.Estado}
  EstadoVisivel{estado: D.Estado}
  FalhouAmbiente{etapa: X.Etapa, identificador: String, fatal: Bool}
  Concluiu{resposta: S.Resposta, estado: D.Estado, fecha_canal: Bool}
  EntregouTudo{bytes: List<&2, U32>}
  EntregaInterrompida{prefixo: List<&2, U32>}
  EncerrouCanal{}
  ProximaChamada{final_anterior: D.Estado, inicial_seguinte: D.Estado}

type Ambiente is Type:
  Ambiente{identidade: String,
    elabora: S.Configuracao -> String -> S.Programa -> Type,
    deriva: S.Configuracao -> String -> Type -> Type,
    observa: String -> Cenario -> Nat -> Fato -> Type,
    processavel: Cenario -> Type,
    falha_real: String -> Cenario -> Nat -> X.Etapa -> String -> Bool -> Type,
    falha_entrega_real: String -> Cenario -> Nat -> Type}

# Identidade completa da configuracao do ambiente. Nao e uma prova baseada
# apenas na igualdade de hashes fornecidos pelo cliente.
def identidade(a: Ambiente) -> String:
  Ambiente{id, el, de, ob, pr, fr, er} = a
  id

# Elabora inclui sintaxe/tipos, fechamento das dependencias, origem exata
# da fonte e do codigo executado, pureza, ausencia de @unsafe/foreign/IO
# e ausencia de capturas do estado nativo nas continuacoes de Acao.
def Elabora(a: Ambiente, c: S.Configuracao, fonte: String, p: S.Programa) -> Type:
  Ambiente{id, el, de, ob, pr, fr, er} = a
  el(c, fonte, p)

# Deriva e a relacao de derivacao do sistema logico FIXO, nao "o verificador
# respondeu sim". A instancia de ambiente deve defini-la independentemente
# da implementacao candidata. Nao ha ampliacao por axiomas do cliente.
def Deriva(a: Ambiente, c: S.Configuracao, texto: String, alvo: Type) -> Type:
  Ambiente{id, el, de, ob, pr, fr, er} = a
  de(c, texto, alvo)

def Acontece(a: Ambiente, nativo: String, x: Cenario, t: Nat, f: Fato) -> Type:
  Ambiente{id, el, de, ob, pr, fr, er} = a
  ob(nativo, x, t, f)

# Processavel e a condicao externa do contrato: ambiente operacional,
# recursos suficientes para esta entrada e ausencia de falha real.
# Nao recebe o artefato candidato: a condicao nao pode se tornar falsa
# porque ele recusou, atrasou ou entrou em loop. Sua interpretacao e fixada
# externamente, nao pode ser um veto arbitrario dentro do JayDB.
# Nao promete teto fisico, prazo, medicao ou pre-empcao pelo nucleo.
def Processavel(a: Ambiente, x: Cenario) -> Type:
  Ambiente{id, el, de, ob, pr, fr, er} = a
  pr(x)

def FalhaReal(a: Ambiente, nativo: String, x: Cenario, t: Nat,
  etapa: X.Etapa, id: String, fatal: Bool) -> Type:
  Ambiente{ident, el, de, ob, pr, fr, er} = a
  fr(nativo, x, t, etapa, id, fatal)

def FalhaEntregaReal(a: Ambiente, nativo: String, x: Cenario, t: Nat) -> Type:
  Ambiente{id, el, de, ob, pr, fr, er} = a
  er(nativo, x, t)

def Antes(-a: Ambiente, -nativo: String, -x: Cenario, -t: Nat, -f: Fato) -> Type:
  &u: Nat -> L.E<{Nat.is_lt(u, t) == True{} : Bool}, Acontece(a, nativo, x, u, f)>

def EmAlgumMomento(-a: Ambiente, -nativo: String, -x: Cenario, -f: Fato) -> Type:
  &t: Nat -> Acontece(a, nativo, x, t, f)

def ConfiguracaoValida(-a: Ambiente, -c: S.Configuracao) -> Type:
  L.E<{R.configuracao_valida(c) == True{} : Bool},
    {S.ambiente(c) == identidade(a) : String}>

def Termina(-p: S.Programa, -e: D.Esquema, -s: D.Estado,
  -ctx: D.Contexto, -args: D.Valor) -> Type:
  &n: Nat -> &w: D.Estado -> &ts: List<&2, S.Evento> -> &r: S.Resposta ->
    {S.executar(n, p, e, s, ctx, args) == S.Final{w, ts, r} : S.Percurso}

def ProgramaTermina(-c: S.Configuracao, -p: S.Programa) -> Type:
  @s: D.Estado -> @ctx: D.Contexto -> @args: D.Valor ->
    Termina(p, S.esquema(c), s, ctx, args)

def Vinculado(-a: Ambiente, -c: S.Configuracao, -fonte: String, -p: S.Programa) -> Type:
  L.E<Elabora(a, c, fonte, p), ProgramaTermina(c, p)>

def CertificadoValido(-a: Ambiente, -c: S.Configuracao, -r: P.Requisicao,
  -ctx: D.Contexto, -p: S.Programa) -> Type:
  L.E<Vinculado(a, c, codigo(r), p),
    L.E<Deriva(a, c, prova(r), R.Certifica(c, codigo(r), p, ctx, argumentos(r))),
      R.Certifica(c, codigo(r), p, ctx, argumentos(r))>>

def RequisicaoRecebida(x: Cenario, -r: P.Requisicao) -> Type:
  match x:
    case Inicializar{mundo, c, s, pi}:
      Empty
    case Atender{mundo, c, s, entrada}:
      &bs: List<&2, U32> ->
        L.E<{X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{bs} : X.Disposicao},
          P.Codificacao(P.requisicao_valor(r), bs)>

def DecodificacaoCorreta(bs: List<&2, U32>, resultado: Maybe<&2, D.Valor>) -> Type:
  match resultado:
    case Some{v}:
      P.Decodificacao(bs, v)
    case None{}:
      @v: D.Valor -> P.Decodificacao(bs, v) -> Empty

def ExecucaoCorreta(-c: S.Configuracao, -s: D.Estado, -r: P.Requisicao,
  -ctx: D.Contexto, -p: S.Programa, -percurso: S.Percurso) -> Type:
  &n: Nat -> {percurso ==
    S.executar(n, p, S.esquema(c), s, ctx, argumentos(r)) : S.Percurso}

def RespostaDoPrograma(-a: Ambiente, -nativo: String, -x: Cenario,
  -t: Nat, -resposta: S.Resposta, -trabalho: D.Estado) -> Type:
  &r: P.Requisicao -> &ctx: D.Contexto -> &p: S.Programa ->
    &ts: List<&2, S.Evento> -> &proposta: S.Resposta ->
      L.E<Antes(a, nativo, x, t, Avaliou{r, ctx, p, S.Final{trabalho, ts, proposta}}),
        {R.finalizar(proposta, configuracao(x), trabalho) == resposta : S.Resposta}>

def ErroFixo(r: S.Resposta) -> Type:
  match r:
    case S.Resposta{S.Sucesso{}, v}:
      {D.valor_valido(v) == True{} : Bool}
    case S.Resposta{S.Recusa{}, v}:
      {D.valor_valido(v) == True{} : Bool}
    case S.Resposta{s, v}:
      {v == D.VAusente{} : D.Valor}

def SemCertificado(-a: Ambiente, -c: S.Configuracao, -r: P.Requisicao,
  -ctx: D.Contexto) -> Type:
  @p: S.Programa ->
    L.E<Vinculado(a, c, codigo(r), p),
      Deriva(a, c, prova(r), R.Certifica(c, codigo(r), p, ctx, argumentos(r)))> -> Empty

def EntradaInvalida(x: Cenario) -> Type:
  match x:
    case Inicializar{mundo, c, s, pi}:
      Empty
    case Atender{mundo, c, s, entrada}:
      L.Ou<
        L.Ou<{X.decidir_recepcao(c, entrada) == X.RecusarEncerrar{S.Entrada{}} : X.Disposicao},
          {X.decidir_recepcao(c, entrada) == X.RecusarContinuar{S.Entrada{}} : X.Disposicao}>,
        &bs: List<&2, U32> ->
          L.E<{X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{bs} : X.Disposicao},
            @r: P.Requisicao -> P.Codificacao(P.requisicao_valor(r), bs) -> Empty>>

def LimiteNaEntrada(x: Cenario) -> Type:
  match x:
    case Inicializar{mundo, c, s, pi}:
      Empty
    case Atender{mundo, c, s, entrada}:
      {X.decidir_recepcao(c, entrada) == X.RecusarEncerrar{S.Limite{}} : X.Disposicao}

# Limite de estado/resposta e calculado sobre a proposta final, em finalizar.
# Um estado de trabalho temporariamente maior nao e, sozinho, essa causa.
def RespostaJustificada(r: S.Resposta, -a: Ambiente, -nativo: String,
  x: Cenario, -t: Nat) -> Type:
  match r:
    case S.Resposta{S.Entrada{}, v}:
      EntradaInvalida(x)
    case S.Resposta{S.Autenticacao{}, v}:
      &req: P.Requisicao ->
        L.E<Antes(a, nativo, x, t, Autenticou{req, None{}}), RequisicaoRecebida(x, req)>
    case S.Resposta{S.Certificado{}, v}:
      &req: P.Requisicao -> &ctx: D.Contexto ->
        Antes(a, nativo, x, t, CertificadoRejeitado{req, ctx})
    case S.Resposta{S.Limite{}, v}:
      L.Ou<LimiteNaEntrada(x),
        &w: D.Estado -> RespostaDoPrograma(a, nativo, x, t, S.Resposta{S.Limite{}, v}, w)>
    case S.Resposta{S.Falha{}, v}:
      &etapa: X.Etapa -> &id: String -> &fatal: Bool ->
        Antes(a, nativo, x, t, FalhouAmbiente{etapa, id, fatal})
    case S.Resposta{s, v}:
      &w: D.Estado -> RespostaDoPrograma(a, nativo, x, t, S.Resposta{s, v}, w)

def FechamentoDisposicao(d: X.Disposicao, fecha: Bool) -> Type:
  match d:
    case X.RecusarEncerrar{s}:
      {fecha == True{} : Bool}
    case X.EncerrarSemResposta{}:
      {fecha == True{} : Bool}
    case _:
      {fecha == False{} : Bool}

def FechamentoCorreto(x: Cenario, fecha: Bool) -> Type:
  match x:
    case Inicializar{mundo, c, s, pi}:
      Unit
    case Atender{mundo, c, s, entrada}:
      FechamentoDisposicao(X.decidir_recepcao(c, entrada), fecha)

