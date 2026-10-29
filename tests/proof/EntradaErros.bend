# Reaplicacoes universais das dez classes de erro do pipeline real.
import Base
import ../../contrato/Bytes.bend as B
import ../../contrato/Dados.bend as D
import ../../contrato/Semantica.bend as S
import ../../contrato/Protocolo.bend as P
import ../../contrato/Requisitos.bend as R
import ../../contrato/Logica.bend as L
import ../../src/Codec.bend as C
import ../../src/Entrada.bend as A
import ../../src/Estado.bend as E
import ../../src/Requisicao.bend as Q
import ../../src/Transporte.bend as T
import ../../proof/EntradaErros.bend as G

law reaplicar_pipeline_transporte_invalido:
  for +bytes: List<&2, U32>
  for +esquema: D.Esquema
  for +limites: S.Limites
  for separado: {T.separar(bytes) == None{} : Maybe<&2, T.Partes>}
  L.E<{A.decodificar(bytes, esquema, limites) == A.ErroTransporte{} : A.PreAutenticacao},
    {A.analisar(bytes, esquema, limites) == A.TransporteInvalido{} : A.Analise}>
def reaplicar_pipeline_transporte_invalido(bytes, esquema, limites, separado):
  G.pipeline_transporte_invalido(bytes, esquema, limites, separado)

law reaplicar_pipeline_limite_estado_nao_representavel:
  for +bytes: List<&2, U32>
  for +esquema: D.Esquema
  for +limites: S.Limites
  for ausente: {B.nat64(R.limite_estado(limites)) == None{} : Maybe<&2, B.Numero64>}
  L.E<{A.decodificar(bytes, esquema, limites) == A.ErroTransporte{} : A.PreAutenticacao},
    {A.analisar(bytes, esquema, limites) == A.TransporteInvalido{} : A.Analise}>
def reaplicar_pipeline_limite_estado_nao_representavel(bytes, esquema, limites, ausente):
  G.pipeline_limite_estado_nao_representavel(bytes, esquema, limites, ausente)

law reaplicar_pipeline_limite_mensagem_nao_representavel:
  for +bytes: List<&2, U32>
  for +esquema: D.Esquema
  for +limites: S.Limites
  for ausente: {B.nat64(R.limite_mensagem(limites)) == None{} : Maybe<&2, B.Numero64>}
  L.E<{A.decodificar(bytes, esquema, limites) == A.ErroTransporte{} : A.PreAutenticacao},
    {A.analisar(bytes, esquema, limites) == A.TransporteInvalido{} : A.Analise}>
def reaplicar_pipeline_limite_mensagem_nao_representavel(bytes, esquema, limites, ausente):
  G.pipeline_limite_mensagem_nao_representavel(bytes, esquema, limites, ausente)

law reaplicar_pipeline_estado_entrada:
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
def reaplicar_pipeline_estado_entrada(bytes, esquema, limites, estado, corpo, teto, separado, medido, recusado):
  G.pipeline_estado_entrada(bytes, esquema, limites, estado, corpo, teto, separado, medido, recusado)

law reaplicar_pipeline_estado_limite:
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
def reaplicar_pipeline_estado_limite(bytes, esquema, limites, estado, corpo, teto, separado, medido, recusado):
  G.pipeline_estado_limite(bytes, esquema, limites, estado, corpo, teto, separado, medido, recusado)

law reaplicar_pipeline_estado_nao_extraido:
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
def reaplicar_pipeline_estado_nao_extraido(bytes, esquema, limites, estado, corpo, teto, valor,
  separado, medido, lido, invalido):
  G.pipeline_estado_nao_extraido(bytes, esquema, limites, estado, corpo, teto, valor,
  separado, medido, lido, invalido)

law reaplicar_pipeline_mensagem_entrada:
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
def reaplicar_pipeline_mensagem_entrada(bytes, esquema, limites, estado, corpo, teto_estado,
  teto_msg, valor_estado, s, quantidade, separado, medido_estado, medido_msg, lido, extraido,
  medido_corpo, cabe, recusado):
  G.pipeline_mensagem_entrada(bytes, esquema, limites, estado, corpo, teto_estado,
  teto_msg, valor_estado, s, quantidade, separado, medido_estado, medido_msg, lido, extraido,
  medido_corpo, cabe, recusado)

law reaplicar_pipeline_mensagem_limite_interno_admitido:
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
def reaplicar_pipeline_mensagem_limite_interno_admitido(bytes, esquema, limites, estado, corpo, teto_estado,
  teto_msg, valor_estado, s, quantidade, separado, medido_estado, medido_msg, lido, extraido,
  medido_corpo, cabe, recusado):
  G.pipeline_mensagem_limite_interno_admitido(bytes, esquema, limites, estado, corpo, teto_estado,
  teto_msg, valor_estado, s, quantidade, separado, medido_estado, medido_msg, lido, extraido,
  medido_corpo, cabe, recusado)

law reaplicar_pipeline_mensagem_corpo_acima_do_teto:
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
def reaplicar_pipeline_mensagem_corpo_acima_do_teto(bytes, esquema, limites, estado, corpo, teto_estado,
  teto_msg, valor_estado, s, quantidade, separado, medido_estado, medido_msg, lido, extraido,
  medido_corpo, acima):
  G.pipeline_mensagem_corpo_acima_do_teto(bytes, esquema, limites, estado, corpo, teto_estado,
  teto_msg, valor_estado, s, quantidade, separado, medido_estado, medido_msg, lido, extraido,
  medido_corpo, acima)

law reaplicar_pipeline_envelope_invalido:
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
def reaplicar_pipeline_envelope_invalido(bytes, esquema, limites, estado, corpo, teto_estado,
  teto_msg, valor_estado, s, valor_msg, separado, medido_estado, medido_msg, lido_estado,
  extraido, lido_msg, ausente):
  G.pipeline_envelope_invalido(bytes, esquema, limites, estado, corpo, teto_estado,
  teto_msg, valor_estado, s, valor_msg, separado, medido_estado, medido_msg, lido_estado,
  extraido, lido_msg, ausente)
