# Visibilidade do ambiente real gerado: consumidor da Lei6, sem nova semantica de store.
import Base
import ../src/Configuracao.bend as Config
import ../contrato/Dados.bend as D
import ../contrato/Semantica.bend as S
import ../contrato/Interface.bend as I
import ../contrato/Recursos.bend as X
import ../contrato/Logica.bend as L
import ../contrato/LAWS.bend as K
import ./ProtocoloServico.bend as Q
import ./RotasServico.bend as H
import ./FonteServico.bend as Fonte
import ./FasesServico.bend as Fases
import ./Fundamentos.bend as F

# Apenas a substituicao J da igualdade ao cenario canonico.
def observar_literal(~fonte: Fonte.Fonte, -x: I.Cenario, -t: Nat, -f: I.Fato) -> Type:
  L.E<{x == Fonte.cenario(fonte, Fonte.mundo(x)) : I.Cenario}, Fonte.da_rota(fonte, x, t, f)>

def quadros_chamada(~c: S.Configuracao, +s: D.Estado, recepcao: X.Recepcao, dados: Fonte.ChamadaData) -> List<&2, Q.Quadro>:
  match dados:
    case Fonte.ChamadaData{cf, pf, cert, termina, estado, ferramentas, micro}:
      H.gerar(c, recepcao, estado, s, ferramentas, micro)

def visivel_igual(+m: Maybe<&2, D.Estado>, +s: D.Estado, h: Q.visivel(m, s)) ->
  {m == Some{s} : Maybe<&2, D.Estado>}:
  match m:
    case None{}: L.ex_falso({None{} == Some{s} : Maybe<&2, D.Estado>}, h)
    case Some{+w}: Equal.cong(D.Estado, Maybe<&2, D.Estado>, x => Some{x}, w, s, Equal.sym(D.Estado, s, w, h))

def visivel_no_ponto(+inicial: Maybe<&2, D.Estado>, +xs: List<&2, Q.Quadro>, +t: Nat, +s: D.Estado,
  h: L.E<{Q.posicao_observavel(xs, t) == True{} : Bool}, Q.visivel(Q.estado_em(xs, t, inicial), s)>) ->
  {Q.estado_em(xs, t, inicial) == Some{s} : Maybe<&2, D.Estado>}:
  match h:
    case L.Ambos{posicao, conteudo}: visivel_igual(Q.estado_em(xs, t, inicial), s, conteudo)

def origem_da_chamada(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +s: D.Estado, +recepcao: X.Recepcao, +dados: Fonte.ChamadaData, +t: Nat, +w: D.Estado,
  h: Fonte.de_observacao(fonte, c, Fonte.construir_chamada(c, s, recepcao, dados), t, I.EstadoVisivel{w})) ->
  Fases.Origem(quadros_chamada(c, s, recepcao, dados), t, s, w):
  match dados:
    case Fonte.ChamadaData{cf, pf, cert, termina, +estado, +ferramentas, +micro}:
      Fases.origem_do_estado_visivel(t, H.gerar(c, recepcao, estado, s, ferramentas, micro), s, w,
        Fases.atendimento_sem_inicio(c, recepcao, estado, s, ferramentas, micro),
        visivel_no_ponto(Some{s}, H.gerar(c, recepcao, estado, s, ferramentas, micro), t, w, h))

def introduzir_publicacao_chamada(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +s: D.Estado, +recepcao: X.Recepcao, +dados: Fonte.ChamadaData, +t: Nat, +w: D.Estado,
  h: {Q.consultar(quadros_chamada(c, s, recepcao, dados), t) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>}) ->
  Fonte.de_observacao(fonte, c, Fonte.construir_chamada(c, s, recepcao, dados), t, I.Publicou{w}):
  match dados:
    case Fonte.ChamadaData{cf, pf, cert, termina, estado, ferramentas, micro}:
      Q.consulta_estabelece_observacao(c, Fonte.programa(fonte, pf), H.gerar(c, recepcao, estado, s, ferramentas, micro), t, Q.Publicada{w}, I.Publicou{w}, h, {==})

def extrair_publicacao_chamada(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +s: D.Estado, +recepcao: X.Recepcao, +dados: Fonte.ChamadaData, +t: Nat, +w: D.Estado,
  h: Fonte.de_observacao(fonte, c, Fonte.construir_chamada(c, s, recepcao, dados), t, I.Publicou{w})) ->
  {Q.consultar(quadros_chamada(c, s, recepcao, dados), t) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>}:
  match dados:
    case Fonte.ChamadaData{cf, pf, cert, termina, estado, ferramentas, micro}:
      Q.observacao_quadro(c, Fonte.programa(fonte, pf), H.gerar(c, recepcao, estado, s, ferramentas, micro), t, I.Publicou{w}, h)

def eliminar_publicacao_fonte(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat,
  +s: D.Estado, +recepcao: X.Recepcao, +t: Nat, +w: D.Estado,
  h: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t, I.Publicou{w})) ->
  {Q.consultar(quadros_chamada(c, s, recepcao, Fonte.chamada(fonte, mundo)), t) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>}:
  F.com_par({Q.consultar(quadros_chamada(c, s, recepcao, Fonte.chamada(fonte, mundo)), t) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>},
    {Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
    observar_literal(fonte, I.Atender{mundo, c, s, recepcao}, t, I.Publicou{w}),
    Fonte.eliminar_fato_literal(fonte, Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t, I.Publicou{w}, h),
    nome => observado =>
      F.com_par({Q.consultar(quadros_chamada(c, s, recepcao, Fonte.chamada(fonte, mundo)), t) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>},
        {I.Atender{mundo, c, s, recepcao} == Fonte.cenario(fonte, mundo) : I.Cenario},
        Fonte.de_observacao(fonte, c,
          Fonte.construir_chamada(c, s, recepcao, Fonte.chamada(fonte, mundo)), t, I.Publicou{w}), observado,
        cenario => conteudo => extrair_publicacao_chamada(fonte, c, s, recepcao, Fonte.chamada(fonte, mundo), t, w, conteudo)))

def visivel_com_cenario(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat,
  +s: D.Estado, +recepcao: X.Recepcao, +t: Nat, +w: D.Estado,
  origem: L.E<{I.Atender{mundo, c, s, recepcao} == Fonte.cenario(fonte, mundo) : I.Cenario},
    Fonte.de_observacao(fonte, c,
      Fonte.construir_chamada(c, s, recepcao, Fonte.chamada(fonte, mundo)), t, I.EstadoVisivel{w})>) ->
  K.Regra6(I.EstadoVisivel{w}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t):
  match origem:
    case L.Ambos{cenario, conteudo}:
      Fases.origem_para_regra6(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t,
        quadros_chamada(c, s, recepcao, Fonte.chamada(fonte, mundo)), w,
        origem_da_chamada(fonte, c, s, recepcao, Fonte.chamada(fonte, mundo), t, w, conteudo),
        +u => +v => consulta => Fonte.introduzir_fato(fonte, Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, u, I.Publicou{v}, {==},
          Fonte.origem_canonica(fonte, I.Atender{mundo, c, s, recepcao}, Fonte.cenario(fonte, mundo), u, I.Publicou{v}, cenario,
            introduzir_publicacao_chamada(fonte, c, s, recepcao, Fonte.chamada(fonte, mundo), u, v, consulta))),
        +u => +v => fato => eliminar_publicacao_fonte(fonte, c, mundo, s, recepcao, u, v, fato))

law visibilidade_atendimento_fonte_obedece_regra6:
  for ~fonte: Fonte.Fonte
  for ~c: S.Configuracao
  for +mundo: Nat
  for +s: D.Estado
  for +recepcao: X.Recepcao
  for +t: Nat
  for +w: D.Estado
  for fato: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t, I.EstadoVisivel{w})
  K.Regra6(I.EstadoVisivel{w}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t)
def visibilidade_atendimento_fonte_obedece_regra6(fonte, c, mundo, s, recepcao, t, w, fato):
  F.com_par(K.Regra6(I.EstadoVisivel{w}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t),
    {Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
    observar_literal(fonte, I.Atender{mundo, c, s, recepcao}, t, I.EstadoVisivel{w}),
    Fonte.eliminar_fato_literal(fonte, Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t, I.EstadoVisivel{w}, fato),
    nome => observacao => visivel_com_cenario(fonte, c, mundo, s, recepcao, t, w, observacao))

def quadros_inicial(~fonte: Fonte.Fonte, ~c: S.Configuracao, +s: D.Estado, dados: Fonte.InicialData) -> List<&2, Q.Quadro>:
  match dados:
    case Fonte.InicialData{cf, sf, pf, juizo, resultado, micro}: H.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, juizo, resultado, micro)

def origem_da_inicializacao(~fonte: Fonte.Fonte, ~c: S.Configuracao, +s: D.Estado,
  +dados: Fonte.InicialData, +t: Nat, +w: D.Estado,
  h: Fonte.de_observacao(fonte, c, Fonte.construir_inicial(Fonte.identidade(fonte), c, s, dados), t, I.EstadoVisivel{w})) ->
  Fases.Origem(quadros_inicial(fonte, c, s, dados), t, s, w):
  match dados:
    case Fonte.InicialData{cf, sf, pf, +juizo, +resultado, +micro}:
      Fases.origem_do_resultado_inicial_casos(micro, s, juizo, resultado, Config.valida(c, Fonte.identidade(fonte)), t, w,
        visivel_no_ponto(None{}, H.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, juizo, resultado, micro), t, w, h))

def introduzir_publicacao_inicial(~fonte: Fonte.Fonte, ~c: S.Configuracao, +s: D.Estado,
  +dados: Fonte.InicialData, +t: Nat, +w: D.Estado,
  h: {Q.consultar(quadros_inicial(fonte, c, s, dados), t) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>}) ->
  Fonte.de_observacao(fonte, c, Fonte.construir_inicial(Fonte.identidade(fonte), c, s, dados), t, I.Publicou{w}):
  match dados:
    case Fonte.InicialData{cf, sf, pf, juizo, resultado, micro}:
      Q.consulta_estabelece_observacao(c, Fonte.sem_programa(), H.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, juizo, resultado, micro), t, Q.Publicada{w}, I.Publicou{w}, h, {==})

def extrair_publicacao_inicial(~fonte: Fonte.Fonte, ~c: S.Configuracao, +s: D.Estado,
  +dados: Fonte.InicialData, +t: Nat, +w: D.Estado,
  h: Fonte.de_observacao(fonte, c, Fonte.construir_inicial(Fonte.identidade(fonte), c, s, dados), t, I.Publicou{w})) ->
  {Q.consultar(quadros_inicial(fonte, c, s, dados), t) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>}:
  match dados:
    case Fonte.InicialData{cf, sf, pf, juizo, resultado, micro}:
      Q.observacao_quadro(c, Fonte.sem_programa(), H.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, juizo, resultado, micro), t, I.Publicou{w}, h)

def eliminar_publicacao_fonte_inicial(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado,
  +pi: String, +t: Nat, +w: D.Estado,
  h: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t, I.Publicou{w})) ->
  {Q.consultar(quadros_inicial(fonte, c, s, Fonte.inicial(fonte, mundo)), t) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>}:
  F.com_par({Q.consultar(quadros_inicial(fonte, c, s, Fonte.inicial(fonte, mundo)), t) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>},
    {Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
    observar_literal(fonte, I.Inicializar{mundo, c, s, pi}, t, I.Publicou{w}),
    Fonte.eliminar_fato_literal(fonte, Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t, I.Publicou{w}, h), nome => observado =>
      F.com_par({Q.consultar(quadros_inicial(fonte, c, s, Fonte.inicial(fonte, mundo)), t) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>},
        {I.Inicializar{mundo, c, s, pi} == Fonte.cenario(fonte, mundo) : I.Cenario},
        Fonte.de_observacao(fonte, c, Fonte.construir_inicial(Fonte.identidade(fonte), c, s, Fonte.inicial(fonte, mundo)), t, I.Publicou{w}), observado,
        cenario => conteudo => extrair_publicacao_inicial(fonte, c, s, Fonte.inicial(fonte, mundo), t, w, conteudo)))

def inicial_visivel_com_cenario(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat,
  +s: D.Estado, +pi: String, +t: Nat, +w: D.Estado,
  origem: L.E<{I.Inicializar{mundo, c, s, pi} == Fonte.cenario(fonte, mundo) : I.Cenario},
    Fonte.de_observacao(fonte, c, Fonte.construir_inicial(Fonte.identidade(fonte), c, s, Fonte.inicial(fonte, mundo)), t, I.EstadoVisivel{w})>) ->
  K.Regra6(I.EstadoVisivel{w}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t):
  match origem:
    case L.Ambos{cenario, conteudo}:
      Fases.origem_para_regra6(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t,
        quadros_inicial(fonte, c, s, Fonte.inicial(fonte, mundo)), w,
        origem_da_inicializacao(fonte, c, s, Fonte.inicial(fonte, mundo), t, w, conteudo),
        +u => +v => consulta => Fonte.introduzir_fato(fonte, Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, u, I.Publicou{v}, {==},
          Fonte.origem_canonica(fonte, I.Inicializar{mundo, c, s, pi}, Fonte.cenario(fonte, mundo), u, I.Publicou{v}, cenario,
            introduzir_publicacao_inicial(fonte, c, s, Fonte.inicial(fonte, mundo), u, v, consulta))),
        +u => +v => fato => eliminar_publicacao_fonte_inicial(fonte, c, mundo, s, pi, u, v, fato))

law visibilidade_inicial_fonte_obedece_regra6:
  for ~fonte: Fonte.Fonte
  for ~c: S.Configuracao
  for +mundo: Nat
  for +s: D.Estado
  for +pi: String
  for +t: Nat
  for +w: D.Estado
  for fato: I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t, I.EstadoVisivel{w})
  K.Regra6(I.EstadoVisivel{w}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t)
def visibilidade_inicial_fonte_obedece_regra6(fonte, c, mundo, s, pi, t, w, fato):
  F.com_par(K.Regra6(I.EstadoVisivel{w}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t),
    {Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
    observar_literal(fonte, I.Inicializar{mundo, c, s, pi}, t, I.EstadoVisivel{w}),
    Fonte.eliminar_fato_literal(fonte, Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t, I.EstadoVisivel{w}, fato),
    nome => observacao => inicial_visivel_com_cenario(fonte, c, mundo, s, pi, t, w, observacao))
