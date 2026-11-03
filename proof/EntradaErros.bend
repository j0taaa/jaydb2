# Classificacao dos erros pelas funcoes reais de Entrada, antes e depois
# da autenticacao. As hipoteses descrevem somente resultados locais;
# nenhuma lei do codec, Contrato ou ambiente e presumido ou reprovado.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Semantica.bend as S
import ../contrato/Protocolo.bend as P
import ../contrato/Requisitos.bend as R
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ../src/Entrada.bend as A
import ../src/Estado.bend as E
import ../src/Requisicao.bend as Q
import ../src/Transporte.bend as T
import ./EntradaMedida.bend as Medida

law autenticar_pre_preserva_erro_mensagem:
  for -status: S.Status
  {A.autenticar_pre(A.ErroMensagem{status}) == A.Rejeitada{status} : A.Analise}
def autenticar_pre_preserva_erro_mensagem(status):
  {==}

law autenticar_pre_preserva_erro_transporte:
  {A.autenticar_pre(A.ErroTransporte{}) == A.TransporteInvalido{} : A.Analise}
def autenticar_pre_preserva_erro_transporte():
  {==}

law envelope_ausente_e_entrada:
  for -estado: D.Estado
  {A.envelope(None{}, estado) == A.ErroMensagem{S.Entrada{}} : A.PreAutenticacao}
def envelope_ausente_e_entrada(estado):
  {==}

law mensagem_entrada_e_entrada:
  for -estado: D.Estado
  {A.mensagem(C.Entrada{}, estado) == A.ErroMensagem{S.Entrada{}} : A.PreAutenticacao}
def mensagem_entrada_e_entrada(estado):
  {==}

law mensagem_limite_interno_e_entrada:
  for -estado: D.Estado
  {A.mensagem(C.Limite{}, estado) == A.ErroMensagem{S.Entrada{}} : A.PreAutenticacao}
def mensagem_limite_interno_e_entrada(estado):
  {==}

law mensagem_sem_envelope_e_entrada:
  for +valor: D.Valor
  for +estado: D.Estado
  for ausente: {Q.extrair(valor) == None{} : Maybe<&2, P.Requisicao>}
  {A.mensagem(C.Decodificado{valor}, estado) == A.ErroMensagem{S.Entrada{}} : A.PreAutenticacao}
def mensagem_sem_envelope_e_entrada(valor, estado, ausente):
  Equal.cong(Maybe<&2, P.Requisicao>, A.PreAutenticacao,
    r => A.envelope(r, estado), Q.extrair(valor), None{}, ausente)

law mensagem_bytes_entrada:
  for +bytes: List<&2, U32>
  for corpo: B.Numero64
  for +limite: B.Numero64
  for +estado: D.Estado
  for medido: {B.nat64(B.comprimento(bytes)) == Some{corpo} : Maybe<&2, B.Numero64>}
  for cabe: {C.menor_igual64(corpo, limite) == True{} : Bool}
  for recusado: {C.decodificar(bytes, limite) == C.Entrada{} : C.Resultado}
  {A.ler_mensagem(Some{limite}, bytes, estado) == A.ErroMensagem{S.Entrada{}} : A.PreAutenticacao}
def mensagem_bytes_entrada(bytes, corpo, limite, estado, medido, cabe, recusado):
  %recusado : {A.ler_mensagem(Some{limite}, bytes, estado) == A.mensagem(_, estado) : A.PreAutenticacao}
  Medida.corpo_admitido_preserva_resultado_do_codec(bytes, corpo, limite, estado, medido, cabe)

law mensagem_bytes_limite_interno_admitido:
  for +bytes: List<&2, U32>
  for corpo: B.Numero64
  for +limite: B.Numero64
  for +estado: D.Estado
  for medido: {B.nat64(B.comprimento(bytes)) == Some{corpo} : Maybe<&2, B.Numero64>}
  for cabe: {C.menor_igual64(corpo, limite) == True{} : Bool}
  for recusado: {C.decodificar(bytes, limite) == C.Limite{} : C.Resultado}
  {A.ler_mensagem(Some{limite}, bytes, estado) == A.ErroMensagem{S.Entrada{}} : A.PreAutenticacao}
def mensagem_bytes_limite_interno_admitido(bytes, corpo, limite, estado, medido, cabe, recusado):
  Medida.limite_interno_no_corpo_admitido_e_entrada(bytes, corpo, limite, estado, medido, cabe, recusado)

law mensagem_bytes_sem_envelope:
  for +bytes: List<&2, U32>
  for +limite: B.Numero64
  for +valor: D.Valor
  for +estado: D.Estado
  for +lido: {C.decodificar(bytes, limite) == C.Decodificado{valor} : C.Resultado}
  for ausente: {Q.extrair(valor) == None{} : Maybe<&2, P.Requisicao>}
  {A.ler_mensagem(Some{limite}, bytes, estado) == A.ErroMensagem{S.Entrada{}} : A.PreAutenticacao}
def mensagem_bytes_sem_envelope(bytes, limite, valor, estado, lido, ausente):
  %ausente : {A.ler_mensagem(Some{limite}, bytes, estado) == A.envelope(_, estado) : A.PreAutenticacao}
  %lido : {A.ler_mensagem(Some{limite}, bytes, estado) == A.mensagem(_, estado) : A.PreAutenticacao}
  Medida.decodificacao_aceita_preserva_mensagem(bytes, limite, estado, valor, lido)

law estado_entrada_e_erro_transporte:
  for -esquema: D.Esquema
  for -corpo: List<&2, U32>
  for -limite: Maybe<&2, B.Numero64>
  {A.estado_decodificado(C.Entrada{}, esquema, corpo, limite) == A.ErroTransporte{} : A.PreAutenticacao}
def estado_entrada_e_erro_transporte(esquema, corpo, limite):
  {==}

law estado_limite_e_erro_transporte:
  for -esquema: D.Esquema
  for -corpo: List<&2, U32>
  for -limite: Maybe<&2, B.Numero64>
  {A.estado_decodificado(C.Limite{}, esquema, corpo, limite) == A.ErroTransporte{} : A.PreAutenticacao}
def estado_limite_e_erro_transporte(esquema, corpo, limite):
  {==}

law estado_ausente_e_erro_transporte:
  for -corpo: List<&2, U32>
  for -limite: Maybe<&2, B.Numero64>
  {A.estado_lido(None{}, corpo, limite) == A.ErroTransporte{} : A.PreAutenticacao}
def estado_ausente_e_erro_transporte(corpo, limite):
  {==}

law estado_valor_invalido_e_erro_transporte:
  for +valor: D.Valor
  for +esquema: D.Esquema
  for +corpo: List<&2, U32>
  for +limite: Maybe<&2, B.Numero64>
  for invalido: {E.decodificar(valor, esquema) == None{} : Maybe<&2, D.Estado>}
  {A.estado_decodificado(C.Decodificado{valor}, esquema, corpo, limite) == A.ErroTransporte{} : A.PreAutenticacao}
def estado_valor_invalido_e_erro_transporte(valor, esquema, corpo, limite, invalido):
  Equal.cong(Maybe<&2, D.Estado>, A.PreAutenticacao,
    s => A.estado_lido(s, corpo, limite), E.decodificar(valor, esquema), None{}, invalido)

law limite_estado_ausente_e_erro_transporte:
  for -esquema: D.Esquema
  for -estado: List<&2, U32>
  for -corpo: List<&2, U32>
  for -limite_msg: Maybe<&2, B.Numero64>
  {A.ler_estado(None{}, esquema, estado, corpo, limite_msg) == A.ErroTransporte{} : A.PreAutenticacao}
def limite_estado_ausente_e_erro_transporte(esquema, estado, corpo, limite_msg):
  {==}

law limite_mensagem_ausente_e_erro_transporte:
  for -corpo: List<&2, U32>
  for -estado: D.Estado
  {A.ler_mensagem(None{}, corpo, estado) == A.ErroTransporte{} : A.PreAutenticacao}
def limite_mensagem_ausente_e_erro_transporte(corpo, estado):
  {==}

# A falta do limite de mensagem da transporte invalido mesmo quando o
# estado falha antes. Nao se troca essa classificacao por S.Limite.
law estado_lido_sem_limite_mensagem:
  for estado: Maybe<&2, D.Estado>
  for -corpo: List<&2, U32>
  {A.estado_lido(estado, corpo, None{}) == A.ErroTransporte{} : A.PreAutenticacao}
def estado_lido_sem_limite_mensagem(estado, corpo):
  match estado:
    case None{}:
      {==}
    case Some{s}:
      {==}

law estado_decodificado_sem_limite_mensagem:
  for resultado: C.Resultado
  for +esquema: D.Esquema
  for +corpo: List<&2, U32>
  {A.estado_decodificado(resultado, esquema, corpo, None{}) == A.ErroTransporte{} : A.PreAutenticacao}
def estado_decodificado_sem_limite_mensagem(resultado, esquema, corpo):
  match resultado:
    case C.Entrada{}:
      {==}
    case C.Limite{}:
      {==}
    case C.Decodificado{v}:
      estado_lido_sem_limite_mensagem(E.decodificar(v, esquema), corpo)

law ler_estado_sem_limite_mensagem:
  for limite: Maybe<&2, B.Numero64>
  for +esquema: D.Esquema
  for +estado: List<&2, U32>
  for +corpo: List<&2, U32>
  {A.ler_estado(limite, esquema, estado, corpo, None{}) == A.ErroTransporte{} : A.PreAutenticacao}
def ler_estado_sem_limite_mensagem(limite, esquema, estado, corpo):
  match limite:
    case None{}:
      {==}
    case Some{n}:
      estado_decodificado_sem_limite_mensagem(C.decodificar(estado, n), esquema, corpo)

law partes_sem_limite_estado:
  for partes: Maybe<&2, T.Partes>
  for +esquema: D.Esquema
  for +limites: S.Limites
  for ausente: {B.nat64(R.limite_estado(limites)) == None{} : Maybe<&2, B.Numero64>}
  {A.partes(partes, esquema, limites) == A.ErroTransporte{} : A.PreAutenticacao}
def partes_sem_limite_estado(partes, esquema, limites, ausente):
  match partes:
    case None{}:
      {==}
    case Some{T.Partes{estado, corpo}}:
      Equal.cong(Maybe<&2, B.Numero64>, A.PreAutenticacao,
        n => A.ler_estado(n, esquema, estado, corpo, B.nat64(R.limite_mensagem(limites))),
        B.nat64(R.limite_estado(limites)), None{}, ausente)

law partes_sem_limite_mensagem:
  for partes: Maybe<&2, T.Partes>
  for +esquema: D.Esquema
  for +limites: S.Limites
  for ausente: {B.nat64(R.limite_mensagem(limites)) == None{} : Maybe<&2, B.Numero64>}
  {A.partes(partes, esquema, limites) == A.ErroTransporte{} : A.PreAutenticacao}
def partes_sem_limite_mensagem(partes, esquema, limites, ausente):
  match partes:
    case None{}:
      {==}
    case Some{T.Partes{+estado, +corpo}}:
      Equal.trans(A.PreAutenticacao, A.partes(Some{T.Partes{estado, corpo}}, esquema, limites),
        A.ler_estado(B.nat64(R.limite_estado(limites)), esquema, estado, corpo, None{}), A.ErroTransporte{},
        Equal.cong(Maybe<&2, B.Numero64>, A.PreAutenticacao,
          n => A.ler_estado(B.nat64(R.limite_estado(limites)), esquema, estado, corpo, n),
          B.nat64(R.limite_mensagem(limites)), None{}, ausente),
        ler_estado_sem_limite_mensagem(B.nat64(R.limite_estado(limites)), esquema, estado, corpo))

# Fatoracoes do pipeline: as conclusoes ainda chamam as funcoes reais
# da proxima etapa, em vez de postular a classificacao final.
law decodificar_estado_separado:
  for +bytes: List<&2, U32>
  for +esquema: D.Esquema
  for +limites: S.Limites
  for +estado: List<&2, U32>
  for +corpo: List<&2, U32>
  for +teto: B.Numero64
  for separado: {T.separar(bytes) == Some{T.Partes{estado, corpo}} : Maybe<&2, T.Partes>}
  for medido: {B.nat64(R.limite_estado(limites)) == Some{teto} : Maybe<&2, B.Numero64>}
  {A.decodificar(bytes, esquema, limites) ==
    A.estado_decodificado(C.decodificar(estado, teto), esquema, corpo,
      B.nat64(R.limite_mensagem(limites))) : A.PreAutenticacao}
def decodificar_estado_separado(bytes, esquema, limites, estado, corpo, teto, separado, medido):
  %medido : {A.decodificar(bytes, esquema, limites) ==
    A.ler_estado(_, esquema, estado, corpo, B.nat64(R.limite_mensagem(limites))) : A.PreAutenticacao}
  %separado : {A.decodificar(bytes, esquema, limites) == A.partes(_, esquema, limites) : A.PreAutenticacao}
  {==}

law decodificar_estado_lido:
  for +bytes: List<&2, U32>
  for +esquema: D.Esquema
  for +limites: S.Limites
  for +estado: List<&2, U32>
  for +corpo: List<&2, U32>
  for +teto: B.Numero64
  for +valor: D.Valor
  for +s: D.Estado
  for separado: {T.separar(bytes) == Some{T.Partes{estado, corpo}} : Maybe<&2, T.Partes>}
  for medido: {B.nat64(R.limite_estado(limites)) == Some{teto} : Maybe<&2, B.Numero64>}
  for lido: {C.decodificar(estado, teto) == C.Decodificado{valor} : C.Resultado}
  for extraido: {E.decodificar(valor, esquema) == Some{s} : Maybe<&2, D.Estado>}
  {A.decodificar(bytes, esquema, limites) ==
    A.ler_mensagem(B.nat64(R.limite_mensagem(limites)), corpo, s) : A.PreAutenticacao}
def decodificar_estado_lido(bytes, esquema, limites, estado, corpo, teto, valor, s,
  separado, medido, lido, extraido):
  %extraido : {A.decodificar(bytes, esquema, limites) ==
    A.estado_lido(_, corpo, B.nat64(R.limite_mensagem(limites))) : A.PreAutenticacao}
  %lido : {A.decodificar(bytes, esquema, limites) ==
    A.estado_decodificado(_, esquema, corpo, B.nat64(R.limite_mensagem(limites))) : A.PreAutenticacao}
  decodificar_estado_separado(bytes, esquema, limites, estado, corpo, teto, separado, medido)

# A analise autentica exatamente o resultado da decodificacao.
# Reune as duas igualdades sem repetir o transporte em cada caso de erro.
def com_autenticacao(+pre: A.PreAutenticacao, +resultado: A.PreAutenticacao,
  +igual: {pre == resultado : A.PreAutenticacao}) ->
  L.E<{pre == resultado : A.PreAutenticacao},
    {A.autenticar_pre(pre) == A.autenticar_pre(resultado) : A.Analise}>:
  L.Ambos{igual, Equal.cong(A.PreAutenticacao, A.Analise, A.autenticar_pre,
    pre, resultado, igual)}

# Cada lei de pipeline fornece as duas saidas exatas: decodificar e analisar.
law pipeline_transporte_invalido:
  for +bytes: List<&2, U32>
  for +esquema: D.Esquema
  for +limites: S.Limites
  for separado: {T.separar(bytes) == None{} : Maybe<&2, T.Partes>}
  L.E<{A.decodificar(bytes, esquema, limites) == A.ErroTransporte{} : A.PreAutenticacao},
    {A.analisar(bytes, esquema, limites) == A.TransporteInvalido{} : A.Analise}>
def pipeline_transporte_invalido(bytes, esquema, limites, separado):
  +pre = Equal.cong(Maybe<&2, T.Partes>, A.PreAutenticacao,
    p => A.partes(p, esquema, limites), T.separar(bytes), None{}, separado)
  com_autenticacao(A.decodificar(bytes, esquema, limites), A.ErroTransporte{}, pre)

law pipeline_limite_estado_nao_representavel:
  for +bytes: List<&2, U32>
  for +esquema: D.Esquema
  for +limites: S.Limites
  for ausente: {B.nat64(R.limite_estado(limites)) == None{} : Maybe<&2, B.Numero64>}
  L.E<{A.decodificar(bytes, esquema, limites) == A.ErroTransporte{} : A.PreAutenticacao},
    {A.analisar(bytes, esquema, limites) == A.TransporteInvalido{} : A.Analise}>
def pipeline_limite_estado_nao_representavel(bytes, esquema, limites, ausente):
  +pre = partes_sem_limite_estado(T.separar(bytes), esquema, limites, ausente)
  com_autenticacao(A.decodificar(bytes, esquema, limites), A.ErroTransporte{}, pre)

law pipeline_limite_mensagem_nao_representavel:
  for +bytes: List<&2, U32>
  for +esquema: D.Esquema
  for +limites: S.Limites
  for ausente: {B.nat64(R.limite_mensagem(limites)) == None{} : Maybe<&2, B.Numero64>}
  L.E<{A.decodificar(bytes, esquema, limites) == A.ErroTransporte{} : A.PreAutenticacao},
    {A.analisar(bytes, esquema, limites) == A.TransporteInvalido{} : A.Analise}>
def pipeline_limite_mensagem_nao_representavel(bytes, esquema, limites, ausente):
  +pre = partes_sem_limite_mensagem(T.separar(bytes), esquema, limites, ausente)
  com_autenticacao(A.decodificar(bytes, esquema, limites), A.ErroTransporte{}, pre)

law pipeline_estado_entrada:
  for +bytes: List<&2, U32>
  for +esquema: D.Esquema
  for +limites: S.Limites
  for +estado: List<&2, U32>
  for +corpo: List<&2, U32>
  for +teto: B.Numero64
  for separado: {T.separar(bytes) == Some{T.Partes{estado, corpo}} : Maybe<&2, T.Partes>}
  for medido: {B.nat64(R.limite_estado(limites)) == Some{teto} : Maybe<&2, B.Numero64>}
  for recusado: {C.decodificar(estado, teto) == C.Entrada{} : C.Resultado}
  L.E<{A.decodificar(bytes, esquema, limites) == A.ErroTransporte{} : A.PreAutenticacao},
    {A.analisar(bytes, esquema, limites) == A.TransporteInvalido{} : A.Analise}>
def pipeline_estado_entrada(bytes, esquema, limites, estado, corpo, teto, separado, medido, recusado):
  +pre = Equal.trans(A.PreAutenticacao, A.decodificar(bytes, esquema, limites),
    A.estado_decodificado(C.decodificar(estado, teto), esquema, corpo, B.nat64(R.limite_mensagem(limites))),
    A.ErroTransporte{},
    decodificar_estado_separado(bytes, esquema, limites, estado, corpo, teto, separado, medido),
    Equal.cong(C.Resultado, A.PreAutenticacao,
      r => A.estado_decodificado(r, esquema, corpo, B.nat64(R.limite_mensagem(limites))),
      C.decodificar(estado, teto), C.Entrada{}, recusado))
  com_autenticacao(A.decodificar(bytes, esquema, limites), A.ErroTransporte{}, pre)

law pipeline_estado_limite:
  for +bytes: List<&2, U32>
  for +esquema: D.Esquema
  for +limites: S.Limites
  for +estado: List<&2, U32>
  for +corpo: List<&2, U32>
  for +teto: B.Numero64
  for separado: {T.separar(bytes) == Some{T.Partes{estado, corpo}} : Maybe<&2, T.Partes>}
  for medido: {B.nat64(R.limite_estado(limites)) == Some{teto} : Maybe<&2, B.Numero64>}
  for recusado: {C.decodificar(estado, teto) == C.Limite{} : C.Resultado}
  L.E<{A.decodificar(bytes, esquema, limites) == A.ErroTransporte{} : A.PreAutenticacao},
    {A.analisar(bytes, esquema, limites) == A.TransporteInvalido{} : A.Analise}>
def pipeline_estado_limite(bytes, esquema, limites, estado, corpo, teto, separado, medido, recusado):
  +pre = Equal.trans(A.PreAutenticacao, A.decodificar(bytes, esquema, limites),
    A.estado_decodificado(C.decodificar(estado, teto), esquema, corpo, B.nat64(R.limite_mensagem(limites))),
    A.ErroTransporte{},
    decodificar_estado_separado(bytes, esquema, limites, estado, corpo, teto, separado, medido),
    Equal.cong(C.Resultado, A.PreAutenticacao,
      r => A.estado_decodificado(r, esquema, corpo, B.nat64(R.limite_mensagem(limites))),
      C.decodificar(estado, teto), C.Limite{}, recusado))
  com_autenticacao(A.decodificar(bytes, esquema, limites), A.ErroTransporte{}, pre)

law pipeline_estado_nao_extraido:
  for +bytes: List<&2, U32>
  for +esquema: D.Esquema
  for +limites: S.Limites
  for +estado: List<&2, U32>
  for +corpo: List<&2, U32>
  for +teto: B.Numero64
  for +valor: D.Valor
  for separado: {T.separar(bytes) == Some{T.Partes{estado, corpo}} : Maybe<&2, T.Partes>}
  for medido: {B.nat64(R.limite_estado(limites)) == Some{teto} : Maybe<&2, B.Numero64>}
  for lido: {C.decodificar(estado, teto) == C.Decodificado{valor} : C.Resultado}
  for invalido: {E.decodificar(valor, esquema) == None{} : Maybe<&2, D.Estado>}
  L.E<{A.decodificar(bytes, esquema, limites) == A.ErroTransporte{} : A.PreAutenticacao},
    {A.analisar(bytes, esquema, limites) == A.TransporteInvalido{} : A.Analise}>
def pipeline_estado_nao_extraido(bytes, esquema, limites, estado, corpo, teto, valor,
  separado, medido, lido, invalido):
  +pre = Equal.trans(A.PreAutenticacao, A.decodificar(bytes, esquema, limites),
    A.estado_decodificado(C.decodificar(estado, teto), esquema, corpo, B.nat64(R.limite_mensagem(limites))),
    A.ErroTransporte{},
    decodificar_estado_separado(bytes, esquema, limites, estado, corpo, teto, separado, medido),
    Equal.trans(A.PreAutenticacao,
      A.estado_decodificado(C.decodificar(estado, teto), esquema, corpo, B.nat64(R.limite_mensagem(limites))),
      A.estado_decodificado(C.Decodificado{valor}, esquema, corpo, B.nat64(R.limite_mensagem(limites))),
      A.ErroTransporte{},
      Equal.cong(C.Resultado, A.PreAutenticacao,
        r => A.estado_decodificado(r, esquema, corpo, B.nat64(R.limite_mensagem(limites))),
        C.decodificar(estado, teto), C.Decodificado{valor}, lido),
      estado_valor_invalido_e_erro_transporte(valor, esquema, corpo, B.nat64(R.limite_mensagem(limites)), invalido)))
  com_autenticacao(A.decodificar(bytes, esquema, limites), A.ErroTransporte{}, pre)

# Fatoracao ate o corpo, incluindo os dois limites nat64 originais.
law decodificar_mensagem_separada:
  for +bytes: List<&2, U32>
  for +esquema: D.Esquema
  for +limites: S.Limites
  for +estado: List<&2, U32>
  for +corpo: List<&2, U32>
  for +teto_estado: B.Numero64
  for +teto_msg: B.Numero64
  for +valor_estado: D.Valor
  for +s: D.Estado
  for separado: {T.separar(bytes) == Some{T.Partes{estado, corpo}} : Maybe<&2, T.Partes>}
  for medido_estado: {B.nat64(R.limite_estado(limites)) == Some{teto_estado} : Maybe<&2, B.Numero64>}
  for medido_msg: {B.nat64(R.limite_mensagem(limites)) == Some{teto_msg} : Maybe<&2, B.Numero64>}
  for lido: {C.decodificar(estado, teto_estado) == C.Decodificado{valor_estado} : C.Resultado}
  for extraido: {E.decodificar(valor_estado, esquema) == Some{s} : Maybe<&2, D.Estado>}
  {A.decodificar(bytes, esquema, limites) == A.ler_mensagem(Some{teto_msg}, corpo, s) : A.PreAutenticacao}
def decodificar_mensagem_separada(bytes, esquema, limites, estado, corpo, teto_estado,
  teto_msg, valor_estado, s, separado, medido_estado, medido_msg, lido, extraido):
  %medido_msg : {A.decodificar(bytes, esquema, limites) == A.ler_mensagem(_, corpo, s) : A.PreAutenticacao}
  decodificar_estado_lido(bytes, esquema, limites, estado, corpo, teto_estado, valor_estado, s,
    separado, medido_estado, lido, extraido)

law pipeline_mensagem_entrada:
  for +bytes: List<&2, U32>
  for +esquema: D.Esquema
  for +limites: S.Limites
  for +estado: List<&2, U32>
  for +corpo: List<&2, U32>
  for +teto_estado: B.Numero64
  for +teto_msg: B.Numero64
  for +valor_estado: D.Valor
  for +s: D.Estado
  for quantidade: B.Numero64
  for separado: {T.separar(bytes) == Some{T.Partes{estado, corpo}} : Maybe<&2, T.Partes>}
  for medido_estado: {B.nat64(R.limite_estado(limites)) == Some{teto_estado} : Maybe<&2, B.Numero64>}
  for medido_msg: {B.nat64(R.limite_mensagem(limites)) == Some{teto_msg} : Maybe<&2, B.Numero64>}
  for lido: {C.decodificar(estado, teto_estado) == C.Decodificado{valor_estado} : C.Resultado}
  for extraido: {E.decodificar(valor_estado, esquema) == Some{s} : Maybe<&2, D.Estado>}
  for medido_corpo: {B.nat64(B.comprimento(corpo)) == Some{quantidade} : Maybe<&2, B.Numero64>}
  for cabe: {C.menor_igual64(quantidade, teto_msg) == True{} : Bool}
  for recusado: {C.decodificar(corpo, teto_msg) == C.Entrada{} : C.Resultado}
  L.E<{A.decodificar(bytes, esquema, limites) == A.ErroMensagem{S.Entrada{}} : A.PreAutenticacao},
    {A.analisar(bytes, esquema, limites) == A.Rejeitada{S.Entrada{}} : A.Analise}>
def pipeline_mensagem_entrada(bytes, esquema, limites, estado, corpo, teto_estado,
  teto_msg, valor_estado, s, quantidade, separado, medido_estado, medido_msg, lido, extraido,
  medido_corpo, cabe, recusado):
  +pre = Equal.trans(A.PreAutenticacao, A.decodificar(bytes, esquema, limites),
    A.ler_mensagem(Some{teto_msg}, corpo, s), A.ErroMensagem{S.Entrada{}},
    decodificar_mensagem_separada(bytes, esquema, limites, estado, corpo, teto_estado,
      teto_msg, valor_estado, s, separado, medido_estado, medido_msg, lido, extraido),
    mensagem_bytes_entrada(corpo, quantidade, teto_msg, s, medido_corpo, cabe, recusado))
  com_autenticacao(A.decodificar(bytes, esquema, limites), A.ErroMensagem{S.Entrada{}}, pre)

law pipeline_mensagem_limite_interno_admitido:
  for +bytes: List<&2, U32>
  for +esquema: D.Esquema
  for +limites: S.Limites
  for +estado: List<&2, U32>
  for +corpo: List<&2, U32>
  for +teto_estado: B.Numero64
  for +teto_msg: B.Numero64
  for +valor_estado: D.Valor
  for +s: D.Estado
  for quantidade: B.Numero64
  for separado: {T.separar(bytes) == Some{T.Partes{estado, corpo}} : Maybe<&2, T.Partes>}
  for medido_estado: {B.nat64(R.limite_estado(limites)) == Some{teto_estado} : Maybe<&2, B.Numero64>}
  for medido_msg: {B.nat64(R.limite_mensagem(limites)) == Some{teto_msg} : Maybe<&2, B.Numero64>}
  for lido: {C.decodificar(estado, teto_estado) == C.Decodificado{valor_estado} : C.Resultado}
  for extraido: {E.decodificar(valor_estado, esquema) == Some{s} : Maybe<&2, D.Estado>}
  for medido_corpo: {B.nat64(B.comprimento(corpo)) == Some{quantidade} : Maybe<&2, B.Numero64>}
  for cabe: {C.menor_igual64(quantidade, teto_msg) == True{} : Bool}
  for recusado: {C.decodificar(corpo, teto_msg) == C.Limite{} : C.Resultado}
  L.E<{A.decodificar(bytes, esquema, limites) == A.ErroMensagem{S.Entrada{}} : A.PreAutenticacao},
    {A.analisar(bytes, esquema, limites) == A.Rejeitada{S.Entrada{}} : A.Analise}>
def pipeline_mensagem_limite_interno_admitido(bytes, esquema, limites, estado, corpo, teto_estado,
  teto_msg, valor_estado, s, quantidade, separado, medido_estado, medido_msg, lido, extraido,
  medido_corpo, cabe, recusado):
  +pre = Equal.trans(A.PreAutenticacao, A.decodificar(bytes, esquema, limites),
    A.ler_mensagem(Some{teto_msg}, corpo, s), A.ErroMensagem{S.Entrada{}},
    decodificar_mensagem_separada(bytes, esquema, limites, estado, corpo, teto_estado,
      teto_msg, valor_estado, s, separado, medido_estado, medido_msg, lido, extraido),
    mensagem_bytes_limite_interno_admitido(corpo, quantidade, teto_msg, s, medido_corpo, cabe, recusado))
  com_autenticacao(A.decodificar(bytes, esquema, limites), A.ErroMensagem{S.Entrada{}}, pre)

# O excesso e da quantidade real recebida, independentemente do codec.
law pipeline_mensagem_corpo_acima_do_teto:
  for +bytes: List<&2, U32>
  for +esquema: D.Esquema
  for +limites: S.Limites
  for +estado: List<&2, U32>
  for +corpo: List<&2, U32>
  for +teto_estado: B.Numero64
  for +teto_msg: B.Numero64
  for +valor_estado: D.Valor
  for +s: D.Estado
  for quantidade: B.Numero64
  for separado: {T.separar(bytes) == Some{T.Partes{estado, corpo}} : Maybe<&2, T.Partes>}
  for medido_estado: {B.nat64(R.limite_estado(limites)) == Some{teto_estado} : Maybe<&2, B.Numero64>}
  for medido_msg: {B.nat64(R.limite_mensagem(limites)) == Some{teto_msg} : Maybe<&2, B.Numero64>}
  for lido: {C.decodificar(estado, teto_estado) == C.Decodificado{valor_estado} : C.Resultado}
  for extraido: {E.decodificar(valor_estado, esquema) == Some{s} : Maybe<&2, D.Estado>}
  for medido_corpo: {B.nat64(B.comprimento(corpo)) == Some{quantidade} : Maybe<&2, B.Numero64>}
  for acima: {C.menor_igual64(quantidade, teto_msg) == False{} : Bool}
  L.E<{A.decodificar(bytes, esquema, limites) == A.ErroMensagem{S.Limite{}} : A.PreAutenticacao},
    {A.analisar(bytes, esquema, limites) == A.Rejeitada{S.Limite{}} : A.Analise}>
def pipeline_mensagem_corpo_acima_do_teto(bytes, esquema, limites, estado, corpo, teto_estado,
  teto_msg, valor_estado, s, quantidade, separado, medido_estado, medido_msg, lido, extraido,
  medido_corpo, acima):
  +pre = Equal.trans(A.PreAutenticacao, A.decodificar(bytes, esquema, limites),
    A.ler_mensagem(Some{teto_msg}, corpo, s), A.ErroMensagem{S.Limite{}},
    decodificar_mensagem_separada(bytes, esquema, limites, estado, corpo, teto_estado,
      teto_msg, valor_estado, s, separado, medido_estado, medido_msg, lido, extraido),
    Medida.corpo_real_acima_do_teto_produz_limite(corpo, quantidade, teto_msg, s, medido_corpo, acima))
  com_autenticacao(A.decodificar(bytes, esquema, limites), A.ErroMensagem{S.Limite{}}, pre)

law pipeline_envelope_invalido:
  for +bytes: List<&2, U32>
  for +esquema: D.Esquema
  for +limites: S.Limites
  for +estado: List<&2, U32>
  for +corpo: List<&2, U32>
  for +teto_estado: B.Numero64
  for +teto_msg: B.Numero64
  for +valor_estado: D.Valor
  for +s: D.Estado
  for +valor_msg: D.Valor
  for separado: {T.separar(bytes) == Some{T.Partes{estado, corpo}} : Maybe<&2, T.Partes>}
  for medido_estado: {B.nat64(R.limite_estado(limites)) == Some{teto_estado} : Maybe<&2, B.Numero64>}
  for medido_msg: {B.nat64(R.limite_mensagem(limites)) == Some{teto_msg} : Maybe<&2, B.Numero64>}
  for lido_estado: {C.decodificar(estado, teto_estado) == C.Decodificado{valor_estado} : C.Resultado}
  for extraido: {E.decodificar(valor_estado, esquema) == Some{s} : Maybe<&2, D.Estado>}
  for lido_msg: {C.decodificar(corpo, teto_msg) == C.Decodificado{valor_msg} : C.Resultado}
  for ausente: {Q.extrair(valor_msg) == None{} : Maybe<&2, P.Requisicao>}
  L.E<{A.decodificar(bytes, esquema, limites) == A.ErroMensagem{S.Entrada{}} : A.PreAutenticacao},
    {A.analisar(bytes, esquema, limites) == A.Rejeitada{S.Entrada{}} : A.Analise}>
def pipeline_envelope_invalido(bytes, esquema, limites, estado, corpo, teto_estado,
  teto_msg, valor_estado, s, valor_msg, separado, medido_estado, medido_msg, lido_estado,
  extraido, lido_msg, ausente):
  +pre = Equal.trans(A.PreAutenticacao, A.decodificar(bytes, esquema, limites),
    A.ler_mensagem(Some{teto_msg}, corpo, s), A.ErroMensagem{S.Entrada{}},
    decodificar_mensagem_separada(bytes, esquema, limites, estado, corpo, teto_estado,
      teto_msg, valor_estado, s, separado, medido_estado, medido_msg, lido_estado, extraido),
    mensagem_bytes_sem_envelope(corpo, teto_msg, valor_msg, s, lido_msg, ausente))
  com_autenticacao(A.decodificar(bytes, esquema, limites), A.ErroMensagem{S.Entrada{}}, pre)
