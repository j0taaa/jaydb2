# Inicializacao e configuracao: conteudo vem do termo inicial checado;
# ordem/exclusao vem do renderer real. Nenhuma Regra1 e recebida.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Interface.bend as I
import ../contrato/LAWS.bend as K
import ../contrato/Logica.bend as L
import ../contrato/Protocolo.bend as P
import ../contrato/Semantica.bend as S
import ./FonteServico.bend as Fonte
import ./RotasServico.bend as R
import ./ProtocoloServico.bend as Q
import ./FasesServico.bend as Fases
import ./Configuracao.bend as Configuracao
import ../src/Configuracao.bend as Config
import ./Chamada.bend as Chamada
import ../contrato/Recursos.bend as X
import ./RefinamentoServico.bend as Ref
import ./CenariosServico.bend as C
import ./HistoricoServico.bend as H
import ./ModeloServico.bend as Modelo

# O ramo aceito nunca emite uma recusa inicial, inclusive nos microquadros.
def codificacao_sem_recusa(q: Maybe<&2, List<&2, U32>>, -s: D.Estado) ->
  {Fases.ausente(Fases.RecusaInicial{}, R.render_inicial(q, s)) == True{} : Bool}:
  match q:
    case None{}: {==}
    case Some{bs}: {==}

def inicio_aceito_sem_recusa(+m: R.Micro, +s: D.Estado) ->
  {Fases.ausente(Fases.RecusaInicial{}, R.render(m, s, R.InicialOk{})) == True{} : Bool}:
  Fases.concatenar_ausencia(Fases.RecusaInicial{}, R.micro_saida(m), R.render_inicial(P.codificar(D.estado_valor(s)), s),
    Fases.micro_saida_sem_macros(Fases.RecusaInicial{}, m), codificacao_sem_recusa(P.codificar(D.estado_valor(s)), s))

def recusa_exclui_inicio(+m: R.Micro, +s: D.Estado, +j: R.Juizo, +resultado: R.ResultadoInicial, +valida: Bool,
  +t: Nat, +status: S.Status, recusa: {Q.consultar(R.render(m, s, R.decidir_juizo_inicial(j, resultado, valida)), t) == Some{Q.InicialRecusada{status}} : Maybe<&2, Q.Quadro>},
  u: Nat, +w: D.Estado, iniciou: {Q.consultar(R.render(m, s, R.decidir_juizo_inicial(j, resultado, valida)), u) == Some{Q.Iniciada{w}} : Maybe<&2, Q.Quadro>}) -> Empty:
  match j:
    case R.Aceitou{}:
      match resultado:
        case R.Finalizada{}:
          match valida:
            case False{}:
              Fases.ausente_exclui_consulta(Fases.Inicializacao{}, [Q.Configurada{}, Q.InicialRecusada{S.Dados{}}], u, Q.Iniciada{w}, {==}, {==}, iniciou)
            case True{}:
              Fases.ausente_exclui_consulta(Fases.RecusaInicial{}, R.render(m, s, R.InicialOk{}), t, Q.InicialRecusada{status}, inicio_aceito_sem_recusa(m, s), {==}, recusa)
        case R.FalhouInicial{aceita, etapa, id, fatal}:
          Fases.ausente_exclui_consulta(Fases.Inicializacao{}, R.render(m, s, R.InicialFalha{aceita && valida, etapa, id, fatal}), u, Q.Iniciada{w}, Fases.falha_inicial_sem_instancia(m, s, aceita && valida, etapa, id, fatal), {==}, iniciou)
        case R.PendenteInicial{aceita}:
          Fases.ausente_exclui_consulta(Fases.Inicializacao{}, R.render(m, s, R.InicialPendente{aceita && valida}), u, Q.Iniciada{w}, Fases.pendencia_inicial_sem_instancia(m, s, aceita && valida), {==}, iniciou)
    case R.Recusou{}:
      Fases.ausente_exclui_consulta(Fases.Inicializacao{}, [Q.Configurada{}, Q.InicialRecusada{S.Certificado{}}], u, Q.Iniciada{w}, {==}, {==}, iniciou)
    case R.ErroJuizo{id, fatal}:
      Fases.ausente_exclui_consulta(Fases.Inicializacao{}, R.render(m, s, R.InicialFalha{False{}, X.Verificar{}, id, fatal}), u, Q.Iniciada{w}, Fases.falha_inicial_sem_instancia(m, s, False{}, X.Verificar{}, id, fatal), {==}, iniciou)
    case R.PendenteJuizo{}:
      Fases.ausente_exclui_consulta(Fases.Inicializacao{}, R.render(m, s, R.InicialPendente{False{}}), u, Q.Iniciada{w}, Fases.pendencia_inicial_sem_instancia(m, s, False{}), {==}, iniciou)

def conteudo_apos_classificar(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  -mundo: Nat, +s: D.Estado, +pi: String, +j: R.Juizo,
  classe: L.E<{Config.valida(c, Fonte.identidade(fonte)) == True{} : Bool}, {j == R.Aceitou{} : R.Juizo}>,
  origem: Fonte.JuizoInicialReal(fonte, c, s, pi, j)) ->
  K.ProvaInicialCorreta(I.Inicializar{mundo, c, s, pi}, Fonte.ambiente(fonte)):
  match classe:
    case L.Ambos{configurada, aceito}:
      L.Ambos{Configuracao.aceita_satisfaz_configuracao_valida_original(Fonte.ambiente(fonte), c, configurada),
        Fonte.inicial_tornar_aceito(fonte, c, s, pi, j, aceito, origem)}

law prova_inicial_aceita_e_correta:
  for ~fonte: Fonte.Fonte
  for ~c: S.Configuracao
  for -mundo: Nat
  for +s: D.Estado
  for +pi: String
  for +j: R.Juizo
  for +resultado: R.ResultadoInicial
  for +m: R.Micro
  for +t: Nat
  for origem: Fonte.JuizoInicialReal(fonte, c, s, pi, j)
  for consulta: {Q.consultar(R.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, j, resultado, m), t) == Some{Q.InicialAceita{}} : Maybe<&2, Q.Quadro>}
  K.ProvaInicialCorreta(I.Inicializar{mundo, c, s, pi}, Fonte.ambiente(fonte))
def prova_inicial_aceita_e_correta(fonte, c, mundo, s, pi, j, resultado, m, t, origem, consulta):
  conteudo_apos_classificar(fonte, c, mundo, s, pi, j,
    Fases.inicio_resultado_exige_configuracao_e_juizo_aceitos(m, s, Config.valida(c, Fonte.identidade(fonte)), j, resultado, t, Q.InicialAceita{}, {==}, consulta), origem)

def inicio_com_conteudo(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  -mundo: Nat, -s: D.Estado, -pi: String, -t: Nat, -w: D.Estado,
  conteudo: K.ProvaInicialCorreta(I.Inicializar{mundo, c, s, pi}, Fonte.ambiente(fonte)),
  mesmo: {w == s : D.Estado},
  prova_antes: I.Antes(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t, I.ProvaInicialAceita{})) ->
  K.InicioCorreto(I.Inicializar{mundo, c, s, pi}, Fonte.ambiente(fonte), Fonte.artefato(fonte), t, w):
  match conteudo:
    case L.Ambos{configurada, L.Ambos{derivada, valido}}:
      L.Ambos{configurada, L.Ambos{derivada, L.Ambos{valido, L.Ambos{mesmo, prova_antes}}}}

def prova_anterior_no_modelo(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +mundo: Nat, +s: D.Estado, +pi: String, +cf: Fonte.JuizoSintatico,
  +sf: Fonte.JuizoSintatico, +pf: Fonte.JuizoSintatico, +m: R.Micro, -t: Nat,
  canonico: {I.Inicializar{mundo, c, s, pi} == Fonte.cenario(fonte, mundo) : I.Cenario},
  origem: {Fonte.inicial(fonte, mundo) == Fonte.InicialData{cf, sf, pf, R.Aceitou{}, R.Finalizada{}, m} : Fonte.InicialData},
  configurada: {Config.valida(c, Fonte.identidade(fonte)) == True{} : Bool},
  antes: &u: Nat -> L.E<{Nat.is_lt(u, t) == True{} : Bool},
    {Q.consultar(R.render(m, s, R.InicialOk{}), u) == Some{Q.InicialAceita{}} : Maybe<&2, Q.Quadro>}>) ->
  I.Antes(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t, I.ProvaInicialAceita{}):
  match antes:
    case (+u, L.Ambos{ordem, consulta}):
      (u, L.Ambos{ordem, Fonte.introduzir_inicial_da_rota(fonte, c, mundo, s, pi, cf, sf, pf, R.Aceitou{}, R.Finalizada{}, m, u, I.ProvaInicialAceita{}, canonico, origem,
        (%Equal.sym(Bool, Config.valida(c, Fonte.identidade(fonte)), True{}, configurada) :
          Q.observa_servico(c, Fonte.sem_programa(), None{}, R.render(m, s, R.decidir_inicial_casos(_, R.Aceitou{})), u, I.ProvaInicialAceita{})
          Q.consulta_estabelece_observacao(c, Fonte.sem_programa(), R.render(m, s, R.InicialOk{}), u,
            Q.InicialAceita{}, I.ProvaInicialAceita{}, consulta, {==})))})

def inicio_de_consultas(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +mundo: Nat, +s: D.Estado, +pi: String, +cf: Fonte.JuizoSintatico,
  +sf: Fonte.JuizoSintatico, +pf: Fonte.JuizoSintatico, +m: R.Micro, +t: Nat, +w: D.Estado,
  canonico: {I.Inicializar{mundo, c, s, pi} == Fonte.cenario(fonte, mundo) : I.Cenario},
  origem: {Fonte.inicial(fonte, mundo) == Fonte.InicialData{cf, sf, pf, R.Aceitou{}, R.Finalizada{}, m} : Fonte.InicialData},
  valores: Fonte.JuizoInicialReal(fonte, c, s, pi, R.Aceitou{}),
  flags: L.E<{Config.valida(c, Fonte.identidade(fonte)) == True{} : Bool}, {Config.valida(c, Fonte.identidade(fonte)) == True{} : Bool}>,
  consultas: L.E<{Q.consultar(R.render(m, s, R.InicialOk{}), t) == Some{Q.Iniciada{w}} : Maybe<&2, Q.Quadro>},
    {Q.consultar(R.render(m, s, R.InicialOk{}), t) == Some{Q.Iniciada{w}} : Maybe<&2, Q.Quadro>}>) ->
  K.InicioCorreto(I.Inicializar{mundo, c, s, pi}, Fonte.ambiente(fonte), Fonte.artefato(fonte), t, w):
  match flags consultas:
    case L.Ambos{cfg1, cfg2} L.Ambos{uma, duas}:
      inicio_com_conteudo(fonte, c, mundo, s, pi, t, w,
        L.Ambos{Configuracao.aceita_satisfaz_configuracao_valida_original(Fonte.ambiente(fonte), c, cfg1), valores},
        Fases.inicializacao_so_inicia_seed(m, s, t, w, uma),
        prova_anterior_no_modelo(fonte, c, mundo, s, pi, cf, sf, pf, m, t, canonico, origem, cfg2,
          Fases.instancia_so_comeca_apos_prova_inicial(m, s, t, w, duas)))

law instancia_aceita_e_correta:
  for ~fonte: Fonte.Fonte
  for ~c: S.Configuracao
  for +mundo: Nat
  for +s: D.Estado
  for +pi: String
  for +cf: Fonte.JuizoSintatico
  for +sf: Fonte.JuizoSintatico
  for +pf: Fonte.JuizoSintatico
  for +m: R.Micro
  for +t: Nat
  for +w: D.Estado
  for canonico: {I.Inicializar{mundo, c, s, pi} == Fonte.cenario(fonte, mundo) : I.Cenario}
  for origem: {Fonte.inicial(fonte, mundo) == Fonte.InicialData{cf, sf, pf, R.Aceitou{}, R.Finalizada{}, m} : Fonte.InicialData}
  for configurada: {Config.valida(c, Fonte.identidade(fonte)) == True{} : Bool}
  for valores: Fonte.JuizoInicialReal(fonte, c, s, pi, R.Aceitou{})
  for consulta: {Q.consultar(R.render(m, s, R.InicialOk{}), t) == Some{Q.Iniciada{w}} : Maybe<&2, Q.Quadro>}
  K.InicioCorreto(I.Inicializar{mundo, c, s, pi}, Fonte.ambiente(fonte), Fonte.artefato(fonte), t, w)
def instancia_aceita_e_correta(fonte, c, mundo, s, pi, cf, sf, pf, m, t, w, canonico, origem, configurada, valores, consulta):
  inicio_de_consultas(fonte, c, mundo, s, pi, cf, sf, pf, m, t, w, canonico, origem, valores,
    Chamada.duplicar_igualdade(Bool, Config.valida(c, Fonte.identidade(fonte)), True{}, configurada),
    Chamada.duplicar_igualdade(Maybe<&2, Q.Quadro>, Q.consultar(R.render(m, s, R.InicialOk{}), t), Some{Q.Iniciada{w}}, consulta))

law recusa_inicial_exclui_instancia:
  for ~fonte: Fonte.Fonte
  for ~c: S.Configuracao
  for +mundo: Nat
  for +s: D.Estado
  for +pi: String
  for +m: R.Micro
  for +valida: Bool
  for +j: R.Juizo
  for +resultado: R.ResultadoInicial
  for +t: Nat
  for +status: S.Status
  for recusa: {Q.consultar(R.render(m, s, R.decidir_juizo_inicial(j, resultado, valida)), t) == Some{Q.InicialRecusada{status}} : Maybe<&2, Q.Quadro>}
  for extrair_inicio: @u: Nat -> @w: D.Estado -> I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, u, I.InstanciaIniciou{w}) ->
    {Q.consultar(R.render(m, s, R.decidir_juizo_inicial(j, resultado, valida)), u) == Some{Q.Iniciada{w}} : Maybe<&2, Q.Quadro>}
  K.Regra1(I.InicializacaoRecusada{status}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t)
def recusa_inicial_exclui_instancia(fonte, c, mundo, s, pi, m, valida, j, resultado, t, status, recusa, extrair_inicio):
  +u => +w => iniciou => recusa_exclui_inicio(m, s, j, resultado, valida, t, status, recusa, u, w, extrair_inicio(u, w, iniciou))

# Fatos reais da mesma inicializacao conservam a mesma lista gerada.
def extrair_inicio_literal(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +mundo: Nat, +s: D.Estado, +pi: String, +cf: Fonte.JuizoSintatico,
  +sf: Fonte.JuizoSintatico, +pf: Fonte.JuizoSintatico, +j: R.Juizo, +resultado: R.ResultadoInicial,
  +m: R.Micro, +u: Nat, +w: D.Estado,
  origem: {Fonte.inicial(fonte, mundo) == Fonte.InicialData{cf, sf, pf, j, resultado, m} : Fonte.InicialData},
  literal: L.E<{Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
    L.E<{I.Inicializar{mundo, c, s, pi} == Fonte.cenario(fonte, mundo) : I.Cenario},
      Fonte.da_rota(fonte, I.Inicializar{mundo, c, s, pi}, u, I.InstanciaIniciou{w})>>) ->
  {Q.consultar(R.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, j, resultado, m), u) == Some{Q.Iniciada{w}} : Maybe<&2, Q.Quadro>}:
  match literal:
    case L.Ambos{nome, L.Ambos{canonico, obs}}:
      Q.observacao_quadro(c, Fonte.sem_programa(), R.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, j, resultado, m), u, I.InstanciaIniciou{w},
        (%origem : Fonte.de_observacao(fonte, c, Fonte.construir_inicial(Fonte.identidade(fonte), c, s, _), u, I.InstanciaIniciou{w}) obs))

def extrair_inicio(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +mundo: Nat, +s: D.Estado, +pi: String, +cf: Fonte.JuizoSintatico,
  +sf: Fonte.JuizoSintatico, +pf: Fonte.JuizoSintatico, +j: R.Juizo, +resultado: R.ResultadoInicial,
  +m: R.Micro, +u: Nat, +w: D.Estado,
  origem: {Fonte.inicial(fonte, mundo) == Fonte.InicialData{cf, sf, pf, j, resultado, m} : Fonte.InicialData},
  fato: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, u, I.InstanciaIniciou{w})) ->
  {Q.consultar(R.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, j, resultado, m), u) == Some{Q.Iniciada{w}} : Maybe<&2, Q.Quadro>}:
  extrair_inicio_literal(fonte, c, mundo, s, pi, cf, sf, pf, j, resultado, m, u, w, origem,
    Fonte.eliminar_fato_literal(fonte, Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, u, I.InstanciaIniciou{w}, fato))

def instancia_do_caso(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +mundo: Nat, +s: D.Estado, +pi: String, +cf: Fonte.JuizoSintatico,
  +sf: Fonte.JuizoSintatico, +pf: Fonte.JuizoSintatico, +j: R.Juizo, +resultado: R.ResultadoInicial, +valida: Bool,
  +m: R.Micro, +t: Nat, +w: D.Estado,
  exata: {Config.valida(c, Fonte.identidade(fonte)) == valida : Bool},
  canonico: {I.Inicializar{mundo, c, s, pi} == Fonte.cenario(fonte, mundo) : I.Cenario},
  origem: {Fonte.inicial(fonte, mundo) == Fonte.InicialData{cf, sf, pf, j, resultado, m} : Fonte.InicialData},
  valores: Fonte.JuizoInicialReal(fonte, c, s, pi, j),
  consulta: {Q.consultar(R.render(m, s, R.decidir_juizo_inicial(j, resultado, valida)), t) == Some{Q.Iniciada{w}} : Maybe<&2, Q.Quadro>}) ->
  K.InicioCorreto(I.Inicializar{mundo, c, s, pi}, Fonte.ambiente(fonte), Fonte.artefato(fonte), t, w):
  match j:
    case R.Aceitou{}:
      match resultado:
        case R.Finalizada{}:
          match valida:
            case False{}:
              L.ex_falso(K.InicioCorreto(I.Inicializar{mundo, c, s, pi}, Fonte.ambiente(fonte), Fonte.artefato(fonte), t, w),
            Fases.ausente_exclui_consulta(Fases.Inicializacao{}, [Q.Configurada{}, Q.InicialRecusada{S.Dados{}}], t, Q.Iniciada{w}, {==}, {==}, consulta))
            case True{}:
              instancia_aceita_e_correta(fonte, c, mundo, s, pi, cf, sf, pf, m, t, w, canonico, origem, exata, valores, consulta)
        case R.FalhouInicial{aceita, etapa, id, fatal}:
          L.ex_falso(K.InicioCorreto(I.Inicializar{mundo, c, s, pi}, Fonte.ambiente(fonte), Fonte.artefato(fonte), t, w),
            Fases.ausente_exclui_consulta(Fases.Inicializacao{}, R.render(m, s, R.InicialFalha{aceita && valida, etapa, id, fatal}), t, Q.Iniciada{w}, Fases.falha_inicial_sem_instancia(m, s, aceita && valida, etapa, id, fatal), {==}, consulta))
        case R.PendenteInicial{aceita}:
          L.ex_falso(K.InicioCorreto(I.Inicializar{mundo, c, s, pi}, Fonte.ambiente(fonte), Fonte.artefato(fonte), t, w),
            Fases.ausente_exclui_consulta(Fases.Inicializacao{}, R.render(m, s, R.InicialPendente{aceita && valida}), t, Q.Iniciada{w}, Fases.pendencia_inicial_sem_instancia(m, s, aceita && valida), {==}, consulta))
    case R.Recusou{}:
      L.ex_falso(K.InicioCorreto(I.Inicializar{mundo, c, s, pi}, Fonte.ambiente(fonte), Fonte.artefato(fonte), t, w),
            Fases.ausente_exclui_consulta(Fases.Inicializacao{}, [Q.Configurada{}, Q.InicialRecusada{S.Certificado{}}], t, Q.Iniciada{w}, {==}, {==}, consulta))
    case R.ErroJuizo{id, fatal}:
      L.ex_falso(K.InicioCorreto(I.Inicializar{mundo, c, s, pi}, Fonte.ambiente(fonte), Fonte.artefato(fonte), t, w),
            Fases.ausente_exclui_consulta(Fases.Inicializacao{}, R.render(m, s, R.InicialFalha{False{}, X.Verificar{}, id, fatal}), t, Q.Iniciada{w}, Fases.falha_inicial_sem_instancia(m, s, False{}, X.Verificar{}, id, fatal), {==}, consulta))
    case R.PendenteJuizo{}:
      L.ex_falso(K.InicioCorreto(I.Inicializar{mundo, c, s, pi}, Fonte.ambiente(fonte), Fonte.artefato(fonte), t, w),
            Fases.ausente_exclui_consulta(Fases.Inicializacao{}, R.render(m, s, R.InicialPendente{False{}}), t, Q.Iniciada{w}, Fases.pendencia_inicial_sem_instancia(m, s, False{}), {==}, consulta))

def instancia_com_metadados(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +mundo: Nat, +s: D.Estado, +pi: String, +cf: Fonte.JuizoSintatico,
  +sf: Fonte.JuizoSintatico, +pf: Fonte.JuizoSintatico, +j: R.Juizo, +resultado: R.ResultadoInicial,
  +m: R.Micro, +t: Nat, +w: D.Estado,
  canonico: {I.Inicializar{mundo, c, s, pi} == Fonte.cenario(fonte, mundo) : I.Cenario},
  origens: L.E<{Fonte.inicial(fonte, mundo) == Fonte.InicialData{cf, sf, pf, j, resultado, m} : Fonte.InicialData},
    {Fonte.inicial(fonte, mundo) == Fonte.InicialData{cf, sf, pf, j, resultado, m} : Fonte.InicialData}>,
  valores: Fonte.JuizoInicialReal(fonte, c, s, pi, j),
  fato: Fonte.da_rota(fonte, I.Inicializar{mundo, c, s, pi}, t, I.InstanciaIniciou{w})) ->
  K.InicioCorreto(I.Inicializar{mundo, c, s, pi}, Fonte.ambiente(fonte), Fonte.artefato(fonte), t, w):
  match origens:
    case L.Ambos{real, ler}:
      instancia_do_caso(fonte, c, mundo, s, pi, cf, sf, pf, j, resultado, Config.valida(c, Fonte.identidade(fonte)), m, t, w, {==}, canonico, real, valores,
        Q.observacao_quadro(c, Fonte.sem_programa(), R.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, j, resultado, m), t, I.InstanciaIniciou{w},
          (%ler : Fonte.de_observacao(fonte, c, Fonte.construir_inicial(Fonte.identidade(fonte), c, s, _), t, I.InstanciaIniciou{w}) fato)))

# Origem e somente o julgamento dos modulos puros da inicializacao.
def JuizoDosDados(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado,
  -pi: String, dados: Fonte.InicialData) -> Type:
  match dados:
    case Fonte.InicialData{cf, sf, pf, j, resultado, micro}: Fonte.JuizoInicialReal(fonte, c, s, pi, j)

def recusa_com_metadados(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +mundo: Nat, +s: D.Estado, +pi: String, +cf: Fonte.JuizoSintatico,
  +sf: Fonte.JuizoSintatico, +pf: Fonte.JuizoSintatico, +j: R.Juizo, +resultado: R.ResultadoInicial,
  +m: R.Micro, +t: Nat, +status: S.Status,
  origens: L.E<{Fonte.inicial(fonte, mundo) == Fonte.InicialData{cf, sf, pf, j, resultado, m} : Fonte.InicialData},
    {Fonte.inicial(fonte, mundo) == Fonte.InicialData{cf, sf, pf, j, resultado, m} : Fonte.InicialData}>,
  fato: Fonte.da_rota(fonte, I.Inicializar{mundo, c, s, pi}, t, I.InicializacaoRecusada{status})) ->
  K.Regra1(I.InicializacaoRecusada{status}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t):
  match origens:
    case L.Ambos{ler, real}:
      recusa_inicial_exclui_instancia(fonte, c, mundo, s, pi, m, Config.valida(c, Fonte.identidade(fonte)), j, resultado, t, status,
        Q.observacao_quadro(c, Fonte.sem_programa(), R.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, j, resultado, m), t, I.InicializacaoRecusada{status},
          (%ler : Fonte.de_observacao(fonte, c, Fonte.construir_inicial(Fonte.identidade(fonte), c, s, _), t, I.InicializacaoRecusada{status}) fato)),
        +u => +w => inicio => extrair_inicio(fonte, c, mundo, s, pi, cf, sf, pf, j, resultado, m, u, w, real, inicio))

def regra1_inicial_dados(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +mundo: Nat, +s: D.Estado, +pi: String, dados: Fonte.InicialData, +t: Nat, f: I.Fato,
  canonico: {I.Inicializar{mundo, c, s, pi} == Fonte.cenario(fonte, mundo) : I.Cenario},
  origem: {Fonte.inicial(fonte, mundo) == dados : Fonte.InicialData},
  valores: JuizoDosDados(fonte, c, s, pi, dados),
  fato: Fonte.da_rota(fonte, I.Inicializar{mundo, c, s, pi}, t, f)) ->
  K.Regra1(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t):
  match dados:
    case Fonte.InicialData{+cf, +sf, +pf, +j, +resultado, +m}:
      match f:
        case I.ConfiguracaoEmUso{observada}:
          Fonte.configuracao_da_rota(fonte, I.Inicializar{mundo, c, s, pi}, t, observada, fato)
        case I.InstanciaIniciou{+w}:
          instancia_com_metadados(fonte, c, mundo, s, pi, cf, sf, pf, j, resultado, m, t, w, canonico,
            Chamada.duplicar_igualdade(Fonte.InicialData, Fonte.inicial(fonte, mundo), Fonte.InicialData{cf, sf, pf, j, resultado, m}, origem), valores, fato)
        case I.ProvaInicialAceita{}:
          prova_inicial_aceita_e_correta(fonte, c, mundo, s, pi, j, resultado, m, t, valores,
            Q.observacao_quadro(c, Fonte.sem_programa(), R.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, j, resultado, m), t, I.ProvaInicialAceita{},
              (%origem : Fonte.de_observacao(fonte, c, Fonte.construir_inicial(Fonte.identidade(fonte), c, s, _), t, I.ProvaInicialAceita{}) fato)))
        case I.InicializacaoRecusada{+status}:
          recusa_com_metadados(fonte, c, mundo, s, pi, cf, sf, pf, j, resultado, m, t, status,
            Chamada.duplicar_igualdade(Fonte.InicialData, Fonte.inicial(fonte, mundo), Fonte.InicialData{cf, sf, pf, j, resultado, m}, origem), fato)
        case I.InspecaoNaoModelada{_a0}: Unit{}
        case I.EfeitoNaoModelado{_a0}: Unit{}
        case I.Codificou{_a0, _a1}: Unit{}
        case I.Decodificou{_a0, _a1}: Unit{}
        case I.Guardou{_a0, _a1, _a2}: Unit{}
        case I.Operou{_a0, _a1, _a2, _a3}: Unit{}
        case I.ConferiuComprimento{_a0, _a1}: Unit{}
        case I.AlocouCampo{_a0, _a1}: Unit{}
        case I.LeuCorpo{_a0, _a1, _a2}: Unit{}
        case I.RecebeuRequisicao{_a0}: Unit{}
        case I.Autenticou{_a0, _a1}: Unit{}
        case I.CertificadoAceito{_a0, _a1, _a2}: Unit{}
        case I.CertificadoRejeitado{_a0, _a1}: Unit{}
        case I.ProgramaComecou{_a0, _a1, _a2}: Unit{}
        case I.Avaliou{_a0, _a1, _a2, _a3}: Unit{}
        case I.Preparou{_a0, _a1}: Unit{}
        case I.Publicou{_a0}: Unit{}
        case I.EstadoVisivel{_a0}: Unit{}
        case I.FalhouAmbiente{_a0, _a1, _a2}: Unit{}
        case I.Concluiu{_a0, _a1, _a2}: Unit{}
        case I.EntregouTudo{_a0}: Unit{}
        case I.EntregaInterrompida{_a0}: Unit{}
        case I.EncerrouCanal{}: Unit{}
        case I.ProximaChamada{_a0, _a1}: Unit{}

def negar_instancia_atender(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +mundo: Nat, +s: D.Estado, +recepcao: X.Recepcao, dados: Fonte.ChamadaData,
  +t: Nat, +w: D.Estado, origem: {Fonte.chamada(fonte, mundo) == dados : Fonte.ChamadaData},
  fato: Fonte.da_rota(fonte, I.Atender{mundo, c, s, recepcao}, t, I.InstanciaIniciou{w})) -> Empty:
  match dados:
    case Fonte.ChamadaData{cf, +ps, cert, termina, +bs, +ferramentas, +micro}:
      Fases.ausente_exclui_consulta(Fases.InicioComProva{}, R.gerar(c, recepcao, bs, s, ferramentas, micro), t, Q.Iniciada{w},
        Fases.atendimento_sem_inicio_com_prova(c, recepcao, bs, s, ferramentas, micro), {==},
        Q.observacao_quadro(c, Fonte.programa(fonte, ps), R.gerar(c, recepcao, bs, s, ferramentas, micro), t, I.InstanciaIniciou{w},
          (%origem : Fonte.de_observacao(fonte, c, Fonte.construir_chamada(c, s, recepcao, _), t, I.InstanciaIniciou{w}) fato)))

def negar_prova_atender(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +mundo: Nat, +s: D.Estado, +recepcao: X.Recepcao, dados: Fonte.ChamadaData,
  +t: Nat, origem: {Fonte.chamada(fonte, mundo) == dados : Fonte.ChamadaData},
  fato: Fonte.da_rota(fonte, I.Atender{mundo, c, s, recepcao}, t, I.ProvaInicialAceita{})) -> Empty:
  match dados:
    case Fonte.ChamadaData{cf, +ps, cert, termina, +bs, +ferramentas, +micro}:
      Fases.ausente_exclui_consulta(Fases.InicioComProva{}, R.gerar(c, recepcao, bs, s, ferramentas, micro), t, Q.InicialAceita{},
        Fases.atendimento_sem_inicio_com_prova(c, recepcao, bs, s, ferramentas, micro), {==},
        Q.observacao_quadro(c, Fonte.programa(fonte, ps), R.gerar(c, recepcao, bs, s, ferramentas, micro), t, I.ProvaInicialAceita{},
          (%origem : Fonte.de_observacao(fonte, c, Fonte.construir_chamada(c, s, recepcao, _), t, I.ProvaInicialAceita{}) fato)))

def regra1_atender_dados(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +mundo: Nat, +s: D.Estado, +recepcao: X.Recepcao, +dados: Fonte.ChamadaData,
  +t: Nat, f: I.Fato, origem: {Fonte.chamada(fonte, mundo) == dados : Fonte.ChamadaData},
  fato: Fonte.da_rota(fonte, I.Atender{mundo, c, s, recepcao}, t, f)) ->
  K.Regra1(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t):
  match f:
    case I.ConfiguracaoEmUso{observada}:
      Fonte.configuracao_da_rota(fonte, I.Atender{mundo, c, s, recepcao}, t, observada, fato)
    case I.InstanciaIniciou{+w}: negar_instancia_atender(fonte, c, mundo, s, recepcao, dados, t, w, origem, fato)
    case I.ProvaInicialAceita{}: negar_prova_atender(fonte, c, mundo, s, recepcao, dados, t, origem, fato)
    case I.InicializacaoRecusada{status}:
      +u => +w => inicio => negar_instancia_atender(fonte, c, mundo, s, recepcao, dados, u, w, origem,
        Ref.retirar_guardas({Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
          {I.Atender{mundo, c, s, recepcao} == Fonte.cenario(fonte, mundo) : I.Cenario},
          Fonte.da_rota(fonte, I.Atender{mundo, c, s, recepcao}, u, I.InstanciaIniciou{w}), Fonte.eliminar_fato_literal(fonte, Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, u, I.InstanciaIniciou{w}, inicio)))
    case I.InspecaoNaoModelada{_a0}: Unit{}
    case I.EfeitoNaoModelado{_a0}: Unit{}
    case I.Codificou{_a0, _a1}: Unit{}
    case I.Decodificou{_a0, _a1}: Unit{}
    case I.Guardou{_a0, _a1, _a2}: Unit{}
    case I.Operou{_a0, _a1, _a2, _a3}: Unit{}
    case I.ConferiuComprimento{_a0, _a1}: Unit{}
    case I.AlocouCampo{_a0, _a1}: Unit{}
    case I.LeuCorpo{_a0, _a1, _a2}: Unit{}
    case I.RecebeuRequisicao{_a0}: Unit{}
    case I.Autenticou{_a0, _a1}: Unit{}
    case I.CertificadoAceito{_a0, _a1, _a2}: Unit{}
    case I.CertificadoRejeitado{_a0, _a1}: Unit{}
    case I.ProgramaComecou{_a0, _a1, _a2}: Unit{}
    case I.Avaliou{_a0, _a1, _a2, _a3}: Unit{}
    case I.Preparou{_a0, _a1}: Unit{}
    case I.Publicou{_a0}: Unit{}
    case I.EstadoVisivel{_a0}: Unit{}
    case I.FalhouAmbiente{_a0, _a1, _a2}: Unit{}
    case I.Concluiu{_a0, _a1, _a2}: Unit{}
    case I.EntregouTudo{_a0}: Unit{}
    case I.EntregaInterrompida{_a0}: Unit{}
    case I.EncerrouCanal{}: Unit{}
    case I.ProximaChamada{_a0, _a1}: Unit{}

# O julgamento inicial so e necessario nos mundos que realmente inicializam.
def OrigemDoMomento(~fonte: Fonte.Fonte, ~seed: Unit -> D.Estado,
  -c: S.Configuracao, -pi: String, momento: C.Momento, +mundo: Nat) -> Type:
  match momento:
    case C.Inicializacao{}: JuizoDosDados(fonte, c, seed(Unit{}), pi, Fonte.inicial(fonte, mundo))
    case C.Atendimento{recepcao}: Unit

def regra1_do_momento(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  ~seed: Unit -> D.Estado, ~historico: Nat -> List<&2, H.Registro>, ~pi: String,
  momento: C.Momento, +mundo: Nat, +t: Nat, f: I.Fato,
  canonico: {C.de_momento(c, seed, historico, pi, momento, mundo) == Fonte.cenario(fonte, mundo) : I.Cenario},
  origem: OrigemDoMomento(fonte, seed, c, pi, momento, mundo),
  fato: Fonte.da_rota(fonte, C.de_momento(c, seed, historico, pi, momento, mundo), t, f)) ->
  K.Regra1(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), C.de_momento(c, seed, historico, pi, momento, mundo), t):
  match momento:
    case C.Inicializacao{}:
      regra1_inicial_dados(fonte, c, mundo, seed(Unit{}), pi, Fonte.inicial(fonte, mundo), t, f, canonico, {==}, origem, fato)
    case C.Atendimento{+recepcao}:
      regra1_atender_dados(fonte, c, mundo, H.estado(historico(mundo), seed(Unit{})), recepcao,
        Fonte.chamada(fonte, mundo), t, f, {==}, fato)

# Levantamento: a rota e unica e canonica; apenas o alvo x e transportado.
def regra1_do_cenario(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, H.Registro>, ~momentos: Nat -> C.Momento, ~pi: String,
  x: I.Cenario, +t: Nat, f: I.Fato,
  origens: @m: Nat -> OrigemDoMomento(Modelo.fonte(base, c, seed, historico, momentos, pi), seed, c, pi, momentos(m), m),
  fato: I.Acontece(Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momentos, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momentos, pi)), x, t, f)) ->
  K.Regra1(f, Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momentos, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momentos, pi)), x, t):
  match x:
    case I.Inicializar{+mundo, configuracao, +s, +prova}:
      match fato:
        case L.Ambos{nome, L.Ambos{igual, obs}}:
          %Equal.sym(I.Cenario, I.Inicializar{mundo, configuracao, s, prova}, C.canonico(c, seed, historico, momentos, pi, mundo),
            Equal.trans(I.Cenario, I.Inicializar{mundo, configuracao, s, prova}, Fonte.cenario(Modelo.fonte(base, c, seed, historico, momentos, pi), mundo),
              C.canonico(c, seed, historico, momentos, pi, mundo), igual, Modelo.cenario_do_modelo(base, c, seed, historico, momentos, pi, mundo))) :
            K.Regra1(f, Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momentos, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momentos, pi)), _, t)
          regra1_do_momento(Modelo.fonte(base, c, seed, historico, momentos, pi), c, seed, historico, pi, momentos(mundo), mundo, t, f,
            Equal.sym(I.Cenario, Fonte.cenario(Modelo.fonte(base, c, seed, historico, momentos, pi), mundo), C.canonico(c, seed, historico, momentos, pi, mundo),
              Modelo.cenario_do_modelo(base, c, seed, historico, momentos, pi, mundo)), origens(mundo),
            (%Modelo.cenario_do_modelo(base, c, seed, historico, momentos, pi, mundo) : Fonte.da_rota(Modelo.fonte(base, c, seed, historico, momentos, pi), _, t, f) obs))
    case I.Atender{+mundo, configuracao, +s, +recepcao}:
      match fato:
        case L.Ambos{nome, L.Ambos{igual, obs}}:
          %Equal.sym(I.Cenario, I.Atender{mundo, configuracao, s, recepcao}, C.canonico(c, seed, historico, momentos, pi, mundo),
            Equal.trans(I.Cenario, I.Atender{mundo, configuracao, s, recepcao}, Fonte.cenario(Modelo.fonte(base, c, seed, historico, momentos, pi), mundo),
              C.canonico(c, seed, historico, momentos, pi, mundo), igual, Modelo.cenario_do_modelo(base, c, seed, historico, momentos, pi, mundo))) :
            K.Regra1(f, Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momentos, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momentos, pi)), _, t)
          regra1_do_momento(Modelo.fonte(base, c, seed, historico, momentos, pi), c, seed, historico, pi, momentos(mundo), mundo, t, f,
            Equal.sym(I.Cenario, Fonte.cenario(Modelo.fonte(base, c, seed, historico, momentos, pi), mundo), C.canonico(c, seed, historico, momentos, pi, mundo),
              Modelo.cenario_do_modelo(base, c, seed, historico, momentos, pi, mundo)), origens(mundo),
            (%Modelo.cenario_do_modelo(base, c, seed, historico, momentos, pi, mundo) : Fonte.da_rota(Modelo.fonte(base, c, seed, historico, momentos, pi), _, t, f) obs))

law lei1_do_modelo:
  for ~base: Fonte.Fonte
  for ~c: S.Configuracao
  for ~seed: Unit -> D.Estado
  for ~historico: Nat -> List<&2, H.Registro>
  for ~momentos: Nat -> C.Momento
  for ~pi: String
  for origens: @m: Nat -> OrigemDoMomento(Modelo.fonte(base, c, seed, historico, momentos, pi), seed, c, pi, momentos(m), m)
  K.Lei1(Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momentos, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momentos, pi)))
def lei1_do_modelo(base, c, seed, historico, momentos, pi, origens):
  x => +t => f => fato => regra1_do_cenario(base, c, seed, historico, momentos, pi, x, t, f, origens, fato)
