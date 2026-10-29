# JayDB — AS OITO LEIS DO NUCLEO.
#
# Uma proposicao em Bend e um Type. LeiN(a, codigo_nativo) e uma obrigacao
# sobre aquele artefato, sob o ambiente fixado `a`. Definir esses tipos NAO
# os demonstra. A implementacao devera fornecer um termo de Contrato(a,k).
# Nao ha `assume`, axioma da aplicacao, prova circular ou implementacao aqui.
import Base
import ./Logica.bend as L
import ./Dados.bend as D
import ./Bytes.bend as B
import ./Protocolo.bend as P
import ./Semantica.bend as S
import ./Requisitos.bend as R
import ./Recursos.bend as X
import ./Interface.bend as I
import ./Vinculos.bend as V

# ----- Auxiliares da Lei 1 -----

def InicioCorreto(x: I.Cenario, -a: I.Ambiente, -k: String,
  -t: Nat, -publicado: D.Estado) -> Type:
  match x:
    case I.Inicializar{mundo, c, s, pi}:
      L.E<I.ConfiguracaoValida(a, c),
        L.E<I.Deriva(a, c, pi, R.Valido(c, s)),
          L.E<R.Valido(c, s),
            L.E<{publicado == s : D.Estado}, I.Antes(a, k, x, t, I.ProvaInicialAceita{})>>>>
    case I.Atender{mundo, c, s, entrada}:
      Empty

def ProvaInicialCorreta(x: I.Cenario, -a: I.Ambiente) -> Type:
  match x:
    case I.Inicializar{mundo, c, s, pi}:
      L.E<I.ConfiguracaoValida(a, c),
        L.E<I.Deriva(a, c, pi, R.Valido(c, s)), R.Valido(c, s)>>
    case I.Atender{mundo, c, s, entrada}:
      Empty

def Regra1(f: I.Fato, -a: I.Ambiente, -k: String, x: I.Cenario, -t: Nat) -> Type:
  match f:
    case I.InstanciaIniciou{s}:
      InicioCorreto(x, a, k, t, s)
    case I.ProvaInicialAceita{}:
      ProvaInicialCorreta(x, a)
    case I.ConfiguracaoEmUso{c}:
      {c == I.configuracao(x) : S.Configuracao}
    case I.InicializacaoRecusada{status}:
      @u: Nat -> @s: D.Estado -> I.Acontece(a, k, x, u, I.InstanciaIniciou{s}) -> Empty
    case _:
      Unit

# ----- Auxiliares da Lei 2 -----

def ComprimentoDeclarado(r: X.Recepcao, -n: Nat) -> Type:
  match r:
    case X.BodyTruncado{alto, baixo, corpo}:
      {X.declarado_igual(alto, baixo, n) == True{} : Bool}
    case X.CorpoRecebido{alto, baixo, corpo}:
      {X.declarado_igual(alto, baixo, n) == True{} : Bool}
    case _:
      Empty

def LeituraLimitada(x: I.Cenario, -antes: Nat, -quantidade: Nat, -declarado: Nat) -> Type:
  match x:
    case I.Inicializar{mundo, c, s, pi}:
      Empty
    case I.Atender{mundo, c, s, entrada}:
      L.E<ComprimentoDeclarado(entrada, declarado),
        L.E<{Nat.is_le(Nat.add(antes, quantidade), declarado) == True{} : Bool},
          {Nat.is_le(Nat.add(antes, quantidade), R.limite_mensagem(S.limites(c))) == True{} : Bool}>>

def Regra2(f: I.Fato, -a: I.Ambiente, -k: String, x: I.Cenario, -t: Nat) -> Type:
  match f:
    case I.Codificou{v, r}:
      {r == P.codificar(v) : Maybe<&2, List<&2, U32>>}
    case I.Decodificou{bs, r}:
      I.DecodificacaoCorreta(bs, r)
    case I.Guardou{s, representacao, abstracao}:
      {abstracao == s : D.Estado}
    case I.Operou{e, s, o, r}:
      {r == D.operar(e, s, o) : D.ResultadoOp}
    case I.RecebeuRequisicao{r}:
      I.RequisicaoRecebida(x, r)
    case I.AlocouCampo{pos, n}:
      I.Antes(a, k, x, t, I.ConferiuComprimento{pos, n})
    case I.LeuCorpo{antes, n, declarado}:
      LeituraLimitada(x, antes, n, declarado)
    case _:
      Unit

# ----- Auxiliares da Lei 3 -----

def Regra3(f: I.Fato, -a: I.Ambiente, -k: String, -x: I.Cenario, -t: Nat) -> Type:
  match f:
    case I.Autenticou{r, ctx}:
      L.E<{ctx == D.autenticar(I.inicial(x), I.credencial(r)) : Maybe<&2, D.Contexto>},
        I.Antes(a, k, x, t, I.RecebeuRequisicao{r})>
    case I.ProgramaComecou{r, ctx, p}:
      L.E<{D.autenticar(I.inicial(x), I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>},
        I.Antes(a, k, x, t, I.Autenticou{r, Some{ctx}})>
    case _:
      Unit

# ----- Auxiliares da Lei 4 -----

def Regra4(f: I.Fato, -a: I.Ambiente, -k: String, -x: I.Cenario, -t: Nat) -> Type:
  match f:
    case I.CertificadoAceito{r, ctx, p}:
      L.E<I.Antes(a, k, x, t, I.Autenticou{r, Some{ctx}}),
        I.CertificadoValido(a, I.configuracao(x), r, ctx, p)>
    case I.CertificadoRejeitado{r, ctx}:
      L.E<I.Antes(a, k, x, t, I.Autenticou{r, Some{ctx}}),
        I.SemCertificado(a, I.configuracao(x), r, ctx)>
    case I.ProgramaComecou{r, ctx, p}:
      I.Antes(a, k, x, t, I.CertificadoAceito{r, ctx, p})
    case _:
      Unit

# ----- Auxiliares da Lei 5 -----

def PrefixosEmOrdem(-a: I.Ambiente, -k: String, -x: I.Cenario, -t: Nat,
  -r: P.Requisicao, -ctx: D.Contexto, -p: S.Programa, -atual: S.Percurso) -> Type:
  @u: Nat -> @anterior: S.Percurso ->
    {Nat.is_lt(u, t) == True{} : Bool} ->
    I.Acontece(a, k, x, u, I.Avaliou{r, ctx, p, anterior}) ->
    L.Prefixo(S.Evento, S.eventos_percurso(anterior), S.eventos_percurso(atual))

def Regra5(f: I.Fato, -a: I.Ambiente, -k: String, -x: I.Cenario, -t: Nat) -> Type:
  match f:
    case I.Avaliou{r, ctx, p, percurso}:
      L.E<L.E<V.SemConclusaoAnterior(a, k, x, t), V.PrefixosNaoTerminaram(a, k, x, t)>,
        L.E<I.Antes(a, k, x, t, I.ProgramaComecou{r, ctx, p}),
          L.E<I.ExecucaoCorreta(I.configuracao(x), I.inicial(x), r, ctx, p, percurso),
          PrefixosEmOrdem(a, k, x, t, r, ctx, p, percurso)>>>
    case I.ProgramaComecou{r, ctx, p}:
      L.E<L.E<I.ConfiguracaoValida(a, I.configuracao(x)),
          L.E<R.Valido(I.configuracao(x), I.inicial(x)), V.SemConclusaoAnterior(a, k, x, t)>>,
        @u: Nat -> @r2: P.Requisicao -> @ctx2: D.Contexto -> @p2: S.Programa ->
        I.Acontece(a, k, x, u, I.ProgramaComecou{r2, ctx2, p2}) ->
          L.E<{u == t : Nat},
            L.E<{r2 == r : P.Requisicao},
              L.E<{ctx2 == ctx : D.Contexto}, {p2 == p : S.Programa}>>>>
    case I.Operou{e, s, o, resultado}:
      L.E<V.SemConclusaoAnterior(a, k, x, t),
        L.E<V.PrefixosNaoTerminaram(a, k, x, t), V.OperacaoVinculada(a, k, x, t, e, s, o, resultado)>>
    case I.InspecaoNaoModelada{descricao}:
      Empty
    case I.EfeitoNaoModelado{descricao}:
      Empty
    case _:
      Unit

# ----- Auxiliares da Lei 6 -----

def NenhumaPublicacao(-a: I.Ambiente, -k: String, -x: I.Cenario) -> Type:
  @t: Nat -> @s: D.Estado -> I.Acontece(a, k, x, t, I.Publicou{s}) -> Empty

def NaoPublicouAntes(-a: I.Ambiente, -k: String, -x: I.Cenario, -t: Nat) -> Type:
  @s: D.Estado -> I.Antes(a, k, x, t, I.Publicou{s}) -> Empty

def ConclusaoAtomica(r: S.Resposta, -a: I.Ambiente, -k: String,
  -x: I.Cenario, -t: Nat, -publicado: D.Estado) -> Type:
  match r:
    case S.Resposta{S.Sucesso{}, v}:
      I.Antes(a, k, x, t, I.Publicou{publicado})
    case _:
      L.E<{publicado == I.inicial(x) : D.Estado}, NenhumaPublicacao(a, k, x)>

def Regra6(f: I.Fato, -a: I.Ambiente, -k: String, -x: I.Cenario, -t: Nat) -> Type:
  match f:
    case I.Publicou{w}:
      L.E<R.Valido(I.configuracao(x), w),
        L.E<&v: D.Valor -> &bs: List<&2, U32> ->
          L.E<I.Antes(a, k, x, t, I.Preparou{S.Resposta{S.Sucesso{}, v}, bs}),
            I.RespostaDoPrograma(a, k, x, t, S.Resposta{S.Sucesso{}, v}, w)>,
          @u: Nat -> @w2: D.Estado -> I.Acontece(a, k, x, u, I.Publicou{w2}) ->
            L.E<{u == t : Nat}, {w2 == w : D.Estado}>>>
    case I.EstadoVisivel{s}:
      L.Ou<L.E<{s == I.inicial(x) : D.Estado}, NaoPublicouAntes(a, k, x, t)>,
        I.Antes(a, k, x, t, I.Publicou{s})>
    case I.Concluiu{r, s, fecha}:
      ConclusaoAtomica(r, a, k, x, t, s)
    case I.ProximaChamada{anterior, seguinte}:
      L.E<{seguinte == anterior : D.Estado},
        &r: S.Resposta -> &fecha: Bool -> I.Antes(a, k, x, t, I.Concluiu{r, anterior, fecha})>
    case _:
      Unit

# ----- Auxiliares da Lei 7 -----

def FalhaFatalAnterior(-a: I.Ambiente, -k: String, -x: I.Cenario, -t: Nat) -> Type:
  &etapa: X.Etapa -> &id: String -> I.Antes(a, k, x, t, I.FalhouAmbiente{etapa, id, True{}})

def FechamentoPermitido(-a: I.Ambiente, -k: String, -x: I.Cenario,
  -t: Nat, -fecha: Bool) -> Type:
  L.Ou<I.FechamentoCorreto(x, fecha),
    L.E<{fecha == True{} : Bool}, FalhaFatalAnterior(a, k, x, t)>>

def SemRespostaEsperada(x: I.Cenario) -> Type:
  match x:
    case I.Inicializar{mundo, c, s, pi}:
      Empty
    case I.Atender{mundo, c, s, entrada}:
      {X.decidir_recepcao(c, entrada) == X.EncerrarSemResposta{} : X.Disposicao}

def EntregaCompletaUnica(-a: I.Ambiente, -k: String, -x: I.Cenario,
  -t: Nat, -bs: List<&2, U32>) -> Type:
  L.E<@u: Nat -> @outros: List<&2, U32> ->
    I.Acontece(a, k, x, u, I.EntregouTudo{outros}) ->
      L.E<{u == t : Nat}, {outros == bs : List<&2, U32>}>,
    @u: Nat -> @prefixo: List<&2, U32> ->
      I.Acontece(a, k, x, u, I.EntregaInterrompida{prefixo}) -> Empty>

def EntregaInterrompidaUnica(-a: I.Ambiente, -k: String, -x: I.Cenario,
  -t: Nat, -bs: List<&2, U32>) -> Type:
  L.E<@u: Nat -> @outros: List<&2, U32> ->
    I.Acontece(a, k, x, u, I.EntregaInterrompida{outros}) ->
      L.E<{u == t : Nat}, {outros == bs : List<&2, U32>}>,
    @u: Nat -> @completo: List<&2, U32> ->
      I.Acontece(a, k, x, u, I.EntregouTudo{completo}) -> Empty>

def FechaEventualmente(fecha: Bool, -a: I.Ambiente, -k: String, -x: I.Cenario) -> Type:
  match fecha:
    case False{}:
      Unit
    case True{}:
      I.Processavel(a, x) -> I.EmAlgumMomento(a, k, x, I.EncerrouCanal{})

def Regra7(f: I.Fato, a: I.Ambiente, k: String, x: I.Cenario, t: Nat) -> Type:
  match f:
    case I.Preparou{r, bs}:
      L.E<I.ErroFixo(r),
        L.E<P.Mensagem(S.resposta_valor(r), bs),
          L.E<{R.cabe(R.limite_resposta(S.limites(I.configuracao(x))), S.resposta_valor(r)) == True{} : Bool},
            I.RespostaJustificada(r, a, k, x, t)>>>
    case I.Concluiu{r, s, fecha}:
      L.E<&bs: List<&2, U32> -> I.Antes(a, k, x, t, I.Preparou{r, bs}),
        L.E<L.E<FechamentoPermitido(a, k, x, t, fecha), FechaEventualmente(fecha, a, k, x)>,
          @u: Nat -> @r2: S.Resposta -> @s2: D.Estado -> @f2: Bool ->
            I.Acontece(a, k, x, u, I.Concluiu{r2, s2, f2}) ->
              L.E<{u == t : Nat}, L.E<{r2 == r : S.Resposta}, {s2 == s : D.Estado}>>>>
    case I.EntregouTudo{bs}:
      &r: S.Resposta -> &s: D.Estado -> &fecha: Bool ->
        L.E<I.Antes(a, k, x, t, I.Concluiu{r, s, fecha}),
          L.E<I.Antes(a, k, x, t, I.Preparou{r, bs}), EntregaCompletaUnica(a, k, x, t, bs)>>
    case I.EntregaInterrompida{prefixo}:
      &r: S.Resposta -> &s: D.Estado -> &fecha: Bool -> &bs: List<&2, U32> ->
        L.E<I.Antes(a, k, x, t, I.Concluiu{r, s, fecha}),
          L.E<I.Antes(a, k, x, t, I.Preparou{r, bs}),
            L.E<L.Prefixo(U32, prefixo, bs),
              L.E<EntregaInterrompidaUnica(a, k, x, t, prefixo), I.FalhaEntregaReal(a, k, x, t)>>>>
    case I.FalhouAmbiente{etapa, id, fatal}:
      I.FalhaReal(a, k, x, t, etapa, id, fatal)
    case I.EncerrouCanal{}:
      L.Ou<SemRespostaEsperada(x),
        L.Ou<FalhaFatalAnterior(a, k, x, t),
          L.Ou<&r: S.Resposta -> &s: D.Estado -> I.Antes(a, k, x, t, I.Concluiu{r, s, True{}}),
            &bs: List<&2, U32> -> I.Antes(a, k, x, t, I.EntregaInterrompida{bs})>>>
    case _:
      Unit

# ----- Auxiliares da Lei 8 -----
# Progresso sob condicoes externas, sem prazo/orcamento fisico.
# Processavel independe do artefato candidato e nao e um veto do servidor.

def InicializacaoPossivel(-a: I.Ambiente, -c: S.Configuracao,
  -s: D.Estado, -pi: String) -> Type:
  L.E<I.ConfiguracaoValida(a, c),
    L.E<I.Deriva(a, c, pi, R.Valido(c, s)), R.Valido(c, s)>>

def AtendimentoTermina(-a: I.Ambiente, -k: String, -x: I.Cenario) -> Type:
  L.Ou<L.E<SemRespostaEsperada(x), I.EmAlgumMomento(a, k, x, I.EncerrouCanal{})>,
    &r: S.Resposta -> &s: D.Estado -> &fecha: Bool ->
      L.E<I.EmAlgumMomento(a, k, x, I.Concluiu{r, s, fecha}),
        &bs: List<&2, U32> -> I.EmAlgumMomento(a, k, x, I.EntregouTudo{bs})>>

def Progresso(x: I.Cenario, -a: I.Ambiente, -k: String) -> Type:
  match x:
    case I.Inicializar{mundo, c, s, pi}:
      InicializacaoPossivel(a, c, s, pi) ->
        I.Processavel(a, x) -> I.EmAlgumMomento(a, k, x, I.InstanciaIniciou{s})
    case I.Atender{mundo, c, s, entrada}:
      I.ConfiguracaoValida(a, c) -> R.Valido(c, s) -> X.RecepcaoValida(entrada) ->
        I.Processavel(a, x) ->
          L.E<AtendimentoTermina(a, k, x),
            @r: P.Requisicao -> @ctx: D.Contexto -> @p: S.Programa ->
              I.RequisicaoRecebida(x, r) ->
              {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>} ->
              L.E<I.Vinculado(a, c, I.codigo(r), p),
                I.Deriva(a, c, I.prova(r), R.Certifica(c, I.codigo(r), p, ctx, I.argumentos(r)))> ->
                  L.E<I.EmAlgumMomento(a, k, x, I.CertificadoAceito{r, ctx, p}),
                    I.EmAlgumMomento(a, k, x, I.ProgramaComecou{r, ctx, p})>>

# 1. Inicializacao fiel e configuracao imutavel.
def Lei1(-a: I.Ambiente, -k: String) -> Type:
  @x: I.Cenario -> @t: Nat -> @f: I.Fato ->
    I.Acontece(a, k, x, t, f) -> Regra1(f, a, k, x, t)

# 2. Representacao exata, operacoes exatas e limites antes do acesso.
def Lei2(-a: I.Ambiente, -k: String) -> Type:
  @x: I.Cenario -> @t: Nat -> @f: I.Fato ->
    I.Acontece(a, k, x, t, f) -> Regra2(f, a, k, x, t)

# 3. Identidade proveniente da credencial e do estado publicado inicial.
def Lei3(-a: I.Ambiente, -k: String) -> Type:
  @x: I.Cenario -> @t: Nat -> @f: I.Fato ->
    I.Acontece(a, k, x, t, f) -> Regra3(f, a, k, x, t)

# 4. Prova para a fonte, dependencias, contexto e argumentos efetivos.
def Lei4(-a: I.Ambiente, -k: String) -> Type:
  @x: I.Cenario -> @t: Nat -> @f: I.Fato ->
    I.Acontece(a, k, x, t, f) -> Regra4(f, a, k, x, t)

# 5. Cada observacao real corresponde ao programa certificado.
def Lei5(-a: I.Ambiente, -k: String) -> Type:
  @x: I.Cenario -> @t: Nat -> @f: I.Fato ->
    I.Acontece(a, k, x, t, f) -> Regra5(f, a, k, x, t)

# 6. Uma publicacao inteira e valida; erros preservam o estado inicial.
def Lei6(-a: I.Ambiente, -k: String) -> Type:
  @x: I.Cenario -> @t: Nat -> @f: I.Fato ->
    I.Acontece(a, k, x, t, f) -> Regra6(f, a, k, x, t)

# 7. Respostas, interrupcoes, entrega e fechamento correspondem aos fatos.
def Lei7(-a: I.Ambiente, -k: String) -> Type:
  @x: I.Cenario -> @t: Nat -> @f: I.Fato ->
    I.Acontece(a, k, x, t, f) -> Regra7(f, a, k, x, t)

# 8. Dentro das condicoes especificadas, iniciar, admitir e concluir.
def Lei8(-a: I.Ambiente, -k: String) -> Type:
  @x: I.Cenario -> Progresso(x, a, k)

def Contrato(-a: I.Ambiente, -k: String) -> Type:
  L.E<Lei1(a, k),
    L.E<Lei2(a, k),
      L.E<Lei3(a, k),
        L.E<Lei4(a, k),
          L.E<Lei5(a, k),
            L.E<Lei6(a, k), L.E<Lei7(a, k), Lei8(a, k)>>>>>>>
