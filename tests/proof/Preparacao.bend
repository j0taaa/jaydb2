# Regressao tecnica. Propostas que violam as leis de T nao sao admitidas;
# estes casos exercitam diretamente finalizar/preparar, sem simular admissao.
import Base
import ../../contrato/Dados.bend as D
import ../../contrato/Semantica.bend as S
import ../../contrato/Requisitos.bend as R
import ../../src/Nucleo.bend as N
import ../../proof/Publicacao.bend as U
import ./Certificado.bend as T

def vazio() -> D.Estado:
  D.Estado{Nil{}, [T.usuario("a", ""), T.usuario("b", "segunda")]}

def duplicado() -> D.Estado:
  D.Estado{Nil{}, [T.usuario("a", "x"), T.usuario("b", "x")]}

def grande() -> D.Valor:
  D.VTexto{String.repeat("x", 300n)}

law sucesso_com_credencial_vazia_e_dados:
  {R.finalizar(T.resposta(), T.configuracao(), vazio()) == S.resposta_erro(S.Dados{}) : S.Resposta}
def sucesso_com_credencial_vazia_e_dados():
  {==}

law sucesso_com_credencial_duplicada_e_dados:
  {R.finalizar(T.resposta(), T.configuracao(), duplicado()) == S.resposta_erro(S.Dados{}) : S.Resposta}
def sucesso_com_credencial_duplicada_e_dados():
  {==}

law recusa_descarta_provisorio_sem_exigir_credenciais_validas:
  {R.finalizar(S.Resposta{S.Recusa{}, D.VBool{True{}}}, T.configuracao(), duplicado()) ==
    S.Resposta{S.Recusa{}, D.VBool{True{}}} : S.Resposta}
def recusa_descarta_provisorio_sem_exigir_credenciais_validas():
  {==}

law unicode_invalido_na_resposta_e_dados:
  {R.finalizar(S.Resposta{S.Sucesso{}, D.VTexto{SCon{Chr{55296}, SNil{}}}}, T.configuracao(), T.inicial()) ==
    S.resposta_erro(S.Dados{}) : S.Resposta}
def unicode_invalido_na_resposta_e_dados():
  {==}

law resposta_grande_nao_e_truncada:
  {R.finalizar(S.Resposta{S.Sucesso{}, grande()}, T.configuracao(), T.inicial()) == S.resposta_erro(S.Limite{}) : S.Resposta}
def resposta_grande_nao_e_truncada():
  {==}

law recusa_grande_tambem_e_limite:
  {R.finalizar(S.Resposta{S.Recusa{}, grande()}, T.configuracao(), vazio()) == S.resposta_erro(S.Limite{}) : S.Resposta}
def recusa_grande_tambem_e_limite():
  {==}

law dados_invalidos_precedem_limite_de_resposta:
  {R.finalizar(S.Resposta{S.Sucesso{}, grande()}, T.configuracao(), duplicado()) == S.resposta_erro(S.Dados{}) : S.Resposta}
def dados_invalidos_precedem_limite_de_resposta():
  {==}

law falha_nao_carrega_diagnostico_privado:
  {R.finalizar(S.Resposta{S.Falha{}, D.VTexto{"segredo"}}, T.configuracao(), duplicado()) ==
    S.resposta_erro(S.Falha{}) : S.Resposta}
def falha_nao_carrega_diagnostico_privado():
  {==}

law todos_os_erros_e_recusas_descartam_trabalho:
  for r: S.Resposta
  for sem_sucesso: {U.status_sucesso(r) == False{} : Bool}
  {S.publica(r, T.inicial(), duplicado()) == T.inicial() : D.Estado}
def todos_os_erros_e_recusas_descartam_trabalho(r, sem_sucesso):
  U.todo_status_sem_sucesso_preserva_publicado(r, T.inicial(), duplicado(), sem_sucesso)

law final_nao_apaga_observacao_antes_do_erro:
  {N.instantaneo(N.avancar(N.EmCurso{T.inicial(),
    S.Acessar{D.LerCelula{D.Aplicacao{"inexistente"}, "a", "x"}, retorno => S.Terminar{D.VAusente{}}},
    T.traco(T.inicial())}, S.esquema(T.configuracao()))) ==
      S.Final{T.inicial(), S.acrescentar(T.traco(T.inicial()),
        S.Evento{D.LerCelula{D.Aplicacao{"inexistente"}, "a", "x"}, S.ErroDeDados{}}),
        S.resposta_erro(S.Dados{})} : S.Percurso}
def final_nao_apaga_observacao_antes_do_erro():
  {==}

law prefixos_depois_de_terminar_nao_reexecutam_leitura:
  {N.percorrer(12n, T.maquina_final(), S.esquema(T.configuracao())) ==
    S.Final{T.inicial(), T.traco(T.inicial()), T.resposta()} : S.Percurso}
def prefixos_depois_de_terminar_nao_reexecutam_leitura():
  N.parada_absorve(12n, T.inicial(), T.traco(T.inicial()), T.resposta(), S.esquema(T.configuracao()))
