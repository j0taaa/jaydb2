# Regressao do comprimento interno forjado; nenhum teste E2E/Codec global.
import Base
import ../../contrato/Bytes.bend as B
import ../../contrato/Dados.bend as D
import ../../contrato/Semantica.bend as S
import ../../contrato/Recursos.bend as X
import ../../contrato/Interface.bend as I
import ../../contrato/Logica.bend as L
import ../../src/Codec.bend as C
import ../../src/Entrada.bend as E
import ../../proof/EntradaMedida.bend as G
import ../../proof/EntradaRecusas.bend as R

def forjado(tag: U32) -> List<&2, U32>:
  [tag, 255, 255, 255, 255, 255, 255, 255, 255]

def estado() -> D.Estado:
  D.Estado{Nil{}, Nil{}}

def configuracao() -> S.Configuracao:
  S.Configuracao{D.Esquema{Nil{}}, S.NenhumaLei{},
    S.Limites{9n, 9n, 9n}, "sem-instanciar-ambiente"}

def recepcao() -> X.Recepcao:
  X.CorpoRecebido{0, 9, forjado(4)}

law caso_original_codec_intacto_ainda_devolve_limite:
  {C.decodificar(forjado(4), B.Numero64{0, 32768}) == C.Limite{} : C.Resultado}
def caso_original_codec_intacto_ainda_devolve_limite():
  {==}

law caso_original_nove_bytes_no_teto_32768_devolve_entrada:
  {E.ler_mensagem(Some{B.Numero64{0, 32768}}, forjado(4), estado()) == E.ErroMensagem{S.Entrada{}} : E.PreAutenticacao}
def caso_original_nove_bytes_no_teto_32768_devolve_entrada():
  G.limite_interno_no_corpo_admitido_e_entrada(forjado(4), B.Numero64{0, 9}, B.Numero64{0, 32768},
    estado(), {==}, {==}, caso_original_codec_intacto_ainda_devolve_limite())

law contagem_lista_overflow_em_corpo_pequeno_e_entrada:
  {E.ler_mensagem(Some{B.Numero64{0, 32768}}, forjado(5), estado()) == E.ErroMensagem{S.Entrada{}} : E.PreAutenticacao}
def contagem_lista_overflow_em_corpo_pequeno_e_entrada():
  {==}

law contagem_registro_overflow_em_corpo_pequeno_e_entrada:
  {E.ler_mensagem(Some{B.Numero64{0, 32768}}, forjado(6), estado()) == E.ErroMensagem{S.Entrada{}} : E.PreAutenticacao}
def contagem_registro_overflow_em_corpo_pequeno_e_entrada():
  {==}

law corpo_real_acima_do_teto_preserva_limite:
  {E.ler_mensagem(Some{B.Numero64{0, 1}}, [0, 0], estado()) == E.ErroMensagem{S.Limite{}} : E.PreAutenticacao}
def corpo_real_acima_do_teto_preserva_limite():
  G.corpo_real_acima_do_teto_produz_limite([0, 0], B.Numero64{0, 2}, B.Numero64{0, 1}, estado(), {==}, {==})

law quantidade_real_exatamente_no_teto_nao_e_limite:
  {E.ler_mensagem(Some{B.Numero64{0, 1}}, [0], estado()) == E.ErroMensagem{S.Entrada{}} : E.PreAutenticacao}
def quantidade_real_exatamente_no_teto_nao_e_limite():
  {==}

law erro_interno_admitido_tem_classificacao_e_justificativa_originais:
  L.E<{E.mensagem(C.Limite{}, estado()) == E.ErroMensagem{S.Entrada{}} : E.PreAutenticacao},
    L.E<{E.ler_mensagem(Some{B.Numero64{0, 9}}, forjado(4), estado()) == E.ErroMensagem{S.Entrada{}} : E.PreAutenticacao},
      I.EntradaInvalida(I.Atender{0n, configuracao(), estado(), recepcao()})>>
def erro_interno_admitido_tem_classificacao_e_justificativa_originais():
  R.limite_interno_admitido_e_entrada_justificada_original(0n, configuracao(), estado(), recepcao(),
    forjado(4), B.Numero64{0, 9}, B.Numero64{0, 9}, {==}, {==}, {==}, {==}, {==})

law erro_de_corpo_completo_exige_canal_continuar:
  L.E<I.FechamentoCorreto(I.Atender{0n, configuracao(), estado(), recepcao()}, False{}),
    {X.corpo_invalido() == X.RecusarContinuar{S.Entrada{}} : X.Disposicao}>
def erro_de_corpo_completo_exige_canal_continuar():
  R.corpo_processado_preserva_fechamento_original(0n, configuracao(), estado(), recepcao(), forjado(4), {==})
