# Respostas e IO do mesmo protocolo gerado, sob contratos primitivos explicitos.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../contrato/Interface.bend as I
import ../contrato/Semantica.bend as S
import ../contrato/Recursos.bend as X
import ../contrato/LAWS.bend as K
import ./FonteServico.bend as Fonte
import ./RotasServico.bend as Rota
import ./ProtocoloServico.bend as Q
import ./ConclusaoServico.bend as C
import ./CanalServico.bend as Canal
import ./FechosServico.bend as Fechos
import ./LigacaoServico.bend as Lig
import ./VisibilidadeServico.bend as Vis
import ./EntradaServico.bend as Copia
import ./Lei2Servico.bend as Dois
import ./Lei5Servico.bend as Cinco
import ./HistoricoServico.bend as Historico
import ./CenariosServico.bend as Cenarios
import ./ModeloServico.bend as Modelo
import ../contrato/Requisitos.bend as Req
import ./Fundamentos.bend as F
import ./FasesServico.bend as Fases
import ./Lei8Servico.bend as Oito
import ./Lei6Servico.bend as Seis
import ../src/Configuracao.bend as Config

# Origem dos bytes, dos resultados tecnicos e dos efeitos POSIX reais.
# Nenhum campo fornece uma Regra7, RespostaJustificada ou conclusao do banco.
def OrigemDaChamada7(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado,
  +rx: X.Recepcao, +dados: Fonte.ChamadaData) -> Type:
  match dados:
    case Fonte.ChamadaData{cf, pf, cert, termina, +be, +ferramentas, +micro}:
      L.E<Copia.EstadoCopiado(c, s, be),
        L.E<Copia.CorpoCopiado(c, rx),
          L.E<Dois.OctetosRecebidos(X.decidir_recepcao(c, rx)),
            L.E<C.EnquadramentoAlcancado(Rota.preprocessamento(ferramentas), X.decidir_recepcao(c, rx)),
              L.E<C.EscritasDisponiveis(fonte, c, mundo, s, rx, Fechos.fecho_do_caso(micro, s, Rota.decidir(c, rx, be, ferramentas))),
                L.E<C.PrefixosDoFecho(Fechos.fecho_do_caso(micro, s, Rota.decidir(c, rx, be, ferramentas))),
                  L.E<Canal.FalhasReais(fonte, I.Atender{mundo, c, s, rx}, Rota.gerar(c, rx, be, s, ferramentas, micro)),
                    Canal.FalhasDeEntregaReais(fonte, I.Atender{mundo, c, s, rx}, Rota.gerar(c, rx, be, s, ferramentas, micro))>>>>>>>

# Configuracao/seed/historia/execucao sao a mesma origem da Lei5/Pub6.
def OrigemDoMomento7(~fonte: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, +mundo: Nat, momento: Cenarios.Momento) -> Type:
  match momento:
    case Cenarios.Inicializacao{}:
      Canal.FalhasReais(fonte, Fonte.cenario(fonte, mundo), Vis.quadros_inicial(fonte, c, seed(Unit{}), Fonte.inicial(fonte, mundo)))
    case Cenarios.Atendimento{+rx}:
      L.E<Cinco.OrigemDoMomento(fonte, c, seed, historico, mundo, Cenarios.Atendimento{rx}),
        OrigemDaChamada7(fonte, c, mundo, Historico.estado(historico(mundo), seed(Unit{})), rx, Fonte.chamada(fonte, mundo))>

def preparo_inicial_excluido(~fonte: Fonte.Fonte, ~c: S.Configuracao, +s: D.Estado,
  dados: Fonte.InicialData, +t: Nat, +r: S.Resposta, +bs: List<&2, U32>,
  consulta: {Q.consultar(Vis.quadros_inicial(fonte, c, s, dados), t) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>}) -> Empty:
  match dados:
    case Fonte.InicialData{cf, sf, pf, j, resultado, micro}:
      Fechos.inicializacao_sem_preparo(micro, s, j, resultado, Config.valida(c, Fonte.identidade(fonte)))(r, bs, t, consulta)

def entregas_iniciais_ausentes(~fonte: Fonte.Fonte, ~c: S.Configuracao, +s: D.Estado, dados: Fonte.InicialData) ->
  L.E<{Fases.ausente(Fases.Completa{}, Vis.quadros_inicial(fonte, c, s, dados)) == True{} : Bool},
    {Fases.ausente(Fases.Interrompida{}, Vis.quadros_inicial(fonte, c, s, dados)) == True{} : Bool}>:
  match dados:
    case Fonte.InicialData{cf, sf, pf, +j, +resultado, +micro}:
      L.e_direita({Fases.ausente(Fases.Conclusao{}, Rota.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, j, resultado, micro)) == True{} : Bool},
        L.E<{Fases.ausente(Fases.Completa{}, Rota.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, j, resultado, micro)) == True{} : Bool},
          {Fases.ausente(Fases.Interrompida{}, Rota.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, j, resultado, micro)) == True{} : Bool}>,
        Fechos.inicializacao_sem_conclusao_entrega(micro, s, j, resultado, Config.valida(c, Fonte.identidade(fonte))))

def falha_inicial_com_origem(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +pi: String,
  +t: Nat, +etapa: X.Etapa, +id: String, +fatal: Bool,
  reais: Canal.FalhasReais(fonte, Fonte.cenario(fonte, mundo), Vis.quadros_inicial(fonte, c, s, Fonte.inicial(fonte, mundo))),
  literal: L.E<{Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
    L.E<{I.Inicializar{mundo, c, s, pi} == Fonte.cenario(fonte, mundo) : I.Cenario},
      Fonte.da_rota(fonte, I.Inicializar{mundo, c, s, pi}, t, I.FalhouAmbiente{etapa, id, fatal})>>) ->
  I.FalhaReal(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t, etapa, id, fatal):
  match literal:
    case L.Ambos{nome, L.Ambos{canonico, raw}}:
      %Equal.sym(I.Cenario, I.Inicializar{mundo, c, s, pi}, Fonte.cenario(fonte, mundo), canonico) :
        I.FalhaReal(Fonte.ambiente(fonte), Fonte.artefato(fonte), _, t, etapa, id, fatal)
      reais(t, etapa, id, fatal, Canal.extrair_inicial_dados(fonte, c, s, Fonte.inicial(fonte, mundo), t, I.FalhouAmbiente{etapa, id, fatal}, Unit{}, raw))

def regra7_inicial(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +pi: String, +t: Nat, f: I.Fato,
  reais: Canal.FalhasReais(fonte, Fonte.cenario(fonte, mundo), Vis.quadros_inicial(fonte, c, s, Fonte.inicial(fonte, mundo))),
  fato: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t, f)) ->
  K.Regra7(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t):
  match f:
    case I.Preparou{+r, +bs}:
      L.ex_falso(K.Regra7(I.Preparou{r, bs}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t),
        preparo_inicial_excluido(fonte, c, s, Fonte.inicial(fonte, mundo), t, r, bs,
          Canal.extrair_inicial(fonte, c, mundo, s, pi, t, I.Preparou{r, bs}, Unit{}, Fonte.eliminar_fato_literal(fonte, Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t, I.Preparou{r, bs}, fato))))
    case I.Concluiu{+r, +w, +fecha}:
      L.ex_falso(K.Regra7(I.Concluiu{r, w, fecha}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t),
        Seis.conclusao_inicial_e_impossivel(fonte, c, mundo, s, pi, t, r, w, fecha, fato))
    case I.EntregouTudo{+bs}:
      L.ex_falso(K.Regra7(I.EntregouTudo{bs}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t),
        Fases.ausente_exclui_consulta(Fases.Completa{}, Vis.quadros_inicial(fonte, c, s, Fonte.inicial(fonte, mundo)), t, Q.Entregue{bs},
          L.e_esquerda({Fases.ausente(Fases.Completa{}, Vis.quadros_inicial(fonte, c, s, Fonte.inicial(fonte, mundo))) == True{} : Bool},
            {Fases.ausente(Fases.Interrompida{}, Vis.quadros_inicial(fonte, c, s, Fonte.inicial(fonte, mundo))) == True{} : Bool},
            entregas_iniciais_ausentes(fonte, c, s, Fonte.inicial(fonte, mundo))), {==},
          Canal.extrair_inicial(fonte, c, mundo, s, pi, t, I.EntregouTudo{bs}, Unit{}, Fonte.eliminar_fato_literal(fonte, Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t, I.EntregouTudo{bs}, fato))))
    case I.EntregaInterrompida{+bs}:
      L.ex_falso(K.Regra7(I.EntregaInterrompida{bs}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t),
        Fases.ausente_exclui_consulta(Fases.Interrompida{}, Vis.quadros_inicial(fonte, c, s, Fonte.inicial(fonte, mundo)), t, Q.Interrompida{bs},
          L.e_direita({Fases.ausente(Fases.Completa{}, Vis.quadros_inicial(fonte, c, s, Fonte.inicial(fonte, mundo))) == True{} : Bool},
            {Fases.ausente(Fases.Interrompida{}, Vis.quadros_inicial(fonte, c, s, Fonte.inicial(fonte, mundo))) == True{} : Bool},
            entregas_iniciais_ausentes(fonte, c, s, Fonte.inicial(fonte, mundo))), {==},
          Canal.extrair_inicial(fonte, c, mundo, s, pi, t, I.EntregaInterrompida{bs}, Unit{}, Fonte.eliminar_fato_literal(fonte, Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t, I.EntregaInterrompida{bs}, fato))))
    case I.FalhouAmbiente{+etapa, +id, +fatal}:
      falha_inicial_com_origem(fonte, c, mundo, s, pi, t, etapa, id, fatal, reais,
        Fonte.eliminar_fato_literal(fonte, Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t, I.FalhouAmbiente{etapa, id, fatal}, fato))
    case I.EncerrouCanal{}:
      L.ex_falso(K.Regra7(I.EncerrouCanal{}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t),
        Canal.encerramento_da_inicializacao_impossivel(fonte, c, mundo, s, pi, t, fato))
    case I.ConfiguracaoEmUso{v}: Unit{}
    case I.InspecaoNaoModelada{v}: Unit{}
    case I.EfeitoNaoModelado{v}: Unit{}
    case I.InstanciaIniciou{v}: Unit{}
    case I.InicializacaoRecusada{v}: Unit{}
    case I.ProvaInicialAceita{}: Unit{}
    case I.Codificou{a, b}: Unit{}
    case I.Decodificou{a, b}: Unit{}
    case I.Guardou{a, b, d}: Unit{}
    case I.Operou{a, b, d, e}: Unit{}
    case I.ConferiuComprimento{a, b}: Unit{}
    case I.AlocouCampo{a, b}: Unit{}
    case I.LeuCorpo{a, b, d}: Unit{}
    case I.RecebeuRequisicao{a}: Unit{}
    case I.Autenticou{a, b}: Unit{}
    case I.CertificadoAceito{a, b, p}: Unit{}
    case I.CertificadoRejeitado{a, b}: Unit{}
    case I.ProgramaComecou{a, b, p}: Unit{}
    case I.Avaliou{a, b, p, v}: Unit{}
    case I.Publicou{a}: Unit{}
    case I.EstadoVisivel{a}: Unit{}
    case I.ProximaChamada{a, b}: Unit{}

# Abre a metadata UMA vez; os getters preservam a mesma tupla de fatos.
def IOAberto(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado,
  +rx: X.Recepcao, +dados: Fonte.ChamadaData) -> Type:
  L.E<C.EstadoDaChamada(c, s, dados),
    L.E<Copia.CorpoCopiado(c, rx),
      L.E<Dois.OctetosRecebidos(X.decidir_recepcao(c, rx)),
        L.E<C.AlcancouPacote(c, rx, dados),
          L.E<C.EscritasDisponiveis(fonte, c, mundo, s, rx, Fechos.fecho_do_caso(Lig.micro_dos_dados(dados), s, Lig.caso_dos_dados(c, rx, dados))),
            L.E<C.PrefixosDoFecho(Fechos.fecho_do_caso(Lig.micro_dos_dados(dados), s, Lig.caso_dos_dados(c, rx, dados))),
              L.E<Canal.FalhasReais(fonte, I.Atender{mundo, c, s, rx}, Vis.quadros_chamada(c, s, rx, dados)),
                Canal.FalhasDeEntregaReais(fonte, I.Atender{mundo, c, s, rx}, Vis.quadros_chamada(c, s, rx, dados))>>>>>>>

def abrir_io(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado,
  +rx: X.Recepcao, dados: Fonte.ChamadaData, io: OrigemDaChamada7(fonte, c, mundo, s, rx, dados)) -> IOAberto(fonte, c, mundo, s, rx, dados):
  match dados:
    case Fonte.ChamadaData{cf, pf, cert, termina, be, ferramentas, micro}: io

# O proprio fato ja contem a igualdade ao cenario canonico.
def encerramento7(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado,
  +rx: X.Recepcao, +t: Nat,
  origem: L.E<{Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
    L.E<{I.Atender{mundo, c, s, rx} == Fonte.cenario(fonte, mundo) : I.Cenario}, Fonte.da_rota(fonte, I.Atender{mundo, c, s, rx}, t, I.EncerrouCanal{})>>) ->
  K.Regra7(I.EncerrouCanal{}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t):
  match origem:
    case L.Ambos{nome, L.Ambos{canonico, obs}}:
      Canal.encerro_da_causa(fonte, c, mundo, s, rx, t, canonico,
        Canal.causas_semanticas_da_chamada(c, mundo, s, rx, Fonte.chamada(fonte, mundo))(t,
          Lig.quadro_da_observacao(fonte, c, s, rx, Fonte.chamada(fonte, mundo), t, I.EncerrouCanal{}, Unit{}, obs)))

def regra7_atendimento_aberto(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +rx: X.Recepcao,
  +t: Nat, cfg: {Req.configuracao_valida(c) == True{} : Bool}, estrutura: {D.estrutura(S.esquema(c), s) == True{} : Bool},
  real: Cinco.ChamadaReal(fonte, c, s, rx, Fonte.chamada(fonte, mundo)),
  io: IOAberto(fonte, c, mundo, s, rx, Fonte.chamada(fonte, mundo)), f: I.Fato,
  fato: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t, f)) ->
  K.Regra7(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t):
  match io:
    case L.Ambos{estado, L.Ambos{corpo, L.Ambos{octetos, L.Ambos{alcancado, L.Ambos{escritas, L.Ambos{prefixos, L.Ambos{falhas, falhas_entrega}}}}}}}:
      match f:
        case I.Preparou{+r, +bs}: C.preparo_da_fonte_obedece_regra7(fonte, c, mundo, s, rx, t, r, bs, real, estado, corpo, octetos, estrutura, cfg, fato)
        case I.Concluiu{+r, +w, +fecha}: C.conclusao_da_chamada_obedece_regra7(fonte, c, mundo, s, rx, t, r, w, fecha, alcancado, escritas, fato)
        case I.EntregouTudo{+bs}: C.entrega_da_chamada_obedece_regra7(fonte, c, mundo, s, rx, t, C.CompletaObservada{bs}, prefixos, falhas_entrega, fato)
        case I.EntregaInterrompida{+bs}: C.entrega_da_chamada_obedece_regra7(fonte, c, mundo, s, rx, t, C.ParcialObservada{bs}, prefixos, falhas_entrega, fato)
        case I.FalhouAmbiente{+etapa, +id, +fatal}: Canal.falha_real_da_chamada(fonte, c, mundo, s, rx, t, etapa, id, fatal, falhas, fato)
        case I.EncerrouCanal{}: encerramento7(fonte, c, mundo, s, rx, t, Fonte.eliminar_fato_literal(fonte, Fonte.artefato(fonte), I.Atender{mundo, c, s, rx}, t, I.EncerrouCanal{}, fato))
        case I.ConfiguracaoEmUso{a0}: Unit{}
        case I.InspecaoNaoModelada{a0}: Unit{}
        case I.EfeitoNaoModelado{a0}: Unit{}
        case I.InstanciaIniciou{a0}: Unit{}
        case I.InicializacaoRecusada{a0}: Unit{}
        case I.ProvaInicialAceita{}: Unit{}
        case I.Codificou{a0, a1}: Unit{}
        case I.Decodificou{a0, a1}: Unit{}
        case I.Guardou{a0, a1, a2}: Unit{}
        case I.Operou{a0, a1, a2, a3}: Unit{}
        case I.ConferiuComprimento{a0, a1}: Unit{}
        case I.AlocouCampo{a0, a1}: Unit{}
        case I.LeuCorpo{a0, a1, a2}: Unit{}
        case I.RecebeuRequisicao{a0}: Unit{}
        case I.Autenticou{a0, a1}: Unit{}
        case I.CertificadoAceito{a0, a1, a2}: Unit{}
        case I.CertificadoRejeitado{a0, a1}: Unit{}
        case I.ProgramaComecou{a0, a1, a2}: Unit{}
        case I.Avaliou{a0, a1, a2, a3}: Unit{}
        case I.Publicou{a0}: Unit{}
        case I.EstadoVisivel{a0}: Unit{}
        case I.ProximaChamada{a0, a1}: Unit{}

def regra7_atendimento(~fonte: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, +mundo: Nat, +rx: X.Recepcao, +t: Nat, f: I.Fato,
  origem: OrigemDoMomento7(fonte, c, seed, historico, mundo, Cenarios.Atendimento{rx}),
  fato: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, Historico.estado(historico(mundo), seed(Unit{})), rx}, t, f)) ->
  K.Regra7(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, Historico.estado(historico(mundo), seed(Unit{})), rx}, t):
  match origem:
    case L.Ambos{L.Ambos{cfg, L.Ambos{inicial, L.Ambos{fontes, real}}}, io}:
      F.com_par(K.Regra7(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, Historico.estado(historico(mundo), seed(Unit{})), rx}, t),
        {Req.configuracao_valida(c) == True{} : Bool}, {S.ambiente(c) == I.identidade(Fonte.ambiente(fonte)) : String}, cfg,
        configurada => identidade => F.com_par(K.Regra7(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, Historico.estado(historico(mundo), seed(Unit{})), rx}, t),
          {Req.estrutura(c, Historico.estado(historico(mundo), seed(Unit{}))) == True{} : Bool}, S.Cumpre(c, S.Estavel{Historico.estado(historico(mundo), seed(Unit{}))}),
          Historico.historico_preserva_validade(c, historico(mundo), seed(Unit{}), inicial, fontes),
          estrutura => leis => regra7_atendimento_aberto(fonte, c, mundo, Historico.estado(historico(mundo), seed(Unit{})), rx, t, configurada,
            Oito.estrutura_do_estado(c, Historico.estado(historico(mundo), seed(Unit{})), estrutura), real,
            abrir_io(fonte, c, mundo, Historico.estado(historico(mundo), seed(Unit{})), rx, Fonte.chamada(fonte, mundo), io), f, fato)))

def regra7_no_momento(~fonte: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~pi: String, +mundo: Nat, +momento: Cenarios.Momento,
  +t: Nat, f: I.Fato, origem: OrigemDoMomento7(fonte, c, seed, historico, mundo, momento),
  obs: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), Cenarios.de_momento(c, seed, historico, pi, momento, mundo), t, f)) ->
  K.Regra7(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), Cenarios.de_momento(c, seed, historico, pi, momento, mundo), t):
  match momento:
    case Cenarios.Inicializacao{}: regra7_inicial(fonte, c, mundo, seed(Unit{}), pi, t, f, origem, obs)
    case Cenarios.Atendimento{r}: regra7_atendimento(fonte, c, seed, historico, mundo, r, t, f, origem, obs)

def regra7_da_origem(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String,
  -x: I.Cenario, +mundo: Nat, +t: Nat, f: I.Fato,
  origem: OrigemDoMomento7(Modelo.fonte(base, c, seed, historico, momento, pi), c, seed, historico, mundo, momento(mundo)),
  observado: L.E<{Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)) == Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)) : String},
    L.E<{x == Fonte.cenario(Modelo.fonte(base, c, seed, historico, momento, pi), mundo) : I.Cenario},
      Fonte.da_rota(Modelo.fonte(base, c, seed, historico, momento, pi), Fonte.cenario(Modelo.fonte(base, c, seed, historico, momento, pi), mundo), t, f)>>) ->
  K.Regra7(f, Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momento, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)), x, t):
  match observado:
    case L.Ambos{nome, L.Ambos{igual, raw}}:
      %Equal.sym(I.Cenario, x, Cenarios.canonico(c, seed, historico, momento, pi, mundo),
        Equal.trans(I.Cenario, x, Fonte.cenario(Modelo.fonte(base, c, seed, historico, momento, pi), mundo),
          Cenarios.canonico(c, seed, historico, momento, pi, mundo), igual, Modelo.cenario_do_modelo(base, c, seed, historico, momento, pi, mundo))) :
        K.Regra7(f, Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momento, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)), _, t)
      regra7_no_momento(Modelo.fonte(base, c, seed, historico, momento, pi), c, seed, historico, pi, mundo, momento(mundo), t, f, origem,
        Seis.fato_no_momento(Modelo.fonte(base, c, seed, historico, momento, pi), c, seed, historico, pi, mundo, momento(mundo), t, f,
          Modelo.cenario_do_modelo(base, c, seed, historico, momento, pi, mundo), raw))

def lei7_do_cenario(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String,
  origens: @m: Nat -> OrigemDoMomento7(Modelo.fonte(base, c, seed, historico, momento, pi), c, seed, historico, m, momento(m)),
  x: I.Cenario, +t: Nat, f: I.Fato,
  observado: I.Acontece(Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momento, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)), x, t, f)) ->
  K.Regra7(f, Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momento, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)), x, t):
  match x:
    case I.Inicializar{+m, original, +s, +prova}:
      regra7_da_origem(base, c, seed, historico, momento, pi, I.Inicializar{m, original, s, prova}, m, t, f, origens(m),
        Fonte.eliminar_fato(Modelo.fonte(base, c, seed, historico, momento, pi), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)), I.Inicializar{m, original, s, prova}, t, f, observado))
    case I.Atender{+m, original, +s, +recepcao}:
      regra7_da_origem(base, c, seed, historico, momento, pi, I.Atender{m, original, s, recepcao}, m, t, f, origens(m),
        Fonte.eliminar_fato(Modelo.fonte(base, c, seed, historico, momento, pi), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)), I.Atender{m, original, s, recepcao}, t, f, observado))

def lei7_do_modelo(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String,
  origens: @m: Nat -> OrigemDoMomento7(Modelo.fonte(base, c, seed, historico, momento, pi), c, seed, historico, m, momento(m))) ->
  K.Lei7(Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momento, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi))):
  x => +t => f => observado => lei7_do_cenario(base, c, seed, historico, momento, pi, origens, x, t, f, observado)
