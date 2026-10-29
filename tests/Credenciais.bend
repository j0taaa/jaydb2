# Regressao da decisao explicita: nao vazio e unicidade so na publicacao.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Semantica.bend as S
import ../contrato/Requisitos.bend as R
import ../src/Nucleo.bend as N

def esquema() -> D.Esquema:
  D.Esquema{Nil{}}

def usuario(+id: String, credencial: String) -> D.Linha:
  D.Linha{id, [D.Campo{"credencial", D.VTexto{credencial}},
    D.Campo{"id", D.VTexto{id}}, D.Campo{"tipo", D.VTexto{"pessoa"}}]}

def inicial() -> D.Estado:
  D.Estado{Nil{}, [usuario("u1", "a"), usuario("u2", "b")]}

def vazio() -> D.Estado:
  D.Estado{Nil{}, [usuario("u1", ""), usuario("u2", "b")]}

def trocado() -> D.Estado:
  D.Estado{Nil{}, [usuario("u1", "b"), usuario("u2", "a")]}

def configuracao() -> S.Configuracao:
  S.Configuracao{esquema(), S.NenhumaLei{},
    S.Limites{4096n, 4096n, 1024n, 1048576n,
      1000000n, 1000000n, 1000000n, 1000000n, 1000000n}, "testes"}

def contexto() -> D.Contexto:
  D.Contexto{"u1", "pessoa"}

def escrever(credencial: String, proxima: S.Acao) -> S.Acao:
  S.Acessar{D.DefinirColuna{D.Usuarios{}, "u1", "credencial", D.VTexto{credencial}},
    retorno => proxima}

def reparado() -> S.Programa:
  S.Programa{ctx => args => escrever("", escrever("a", S.Terminar{D.VAusente{}}))}

def sem_reparo() -> S.Programa:
  S.Programa{ctx => args => escrever("", S.Terminar{D.VAusente{}})}

def recusa() -> S.Programa:
  S.Programa{ctx => args => escrever("", S.Recusar{D.VTexto{"recusado"}})}

def troca() -> S.Programa:
  S.Programa{ctx => args => escrever("b",
    S.Acessar{D.DefinirColuna{D.Usuarios{}, "u2", "credencial", D.VTexto{"a"}},
      retorno => S.Terminar{D.VAusente{}}})}

def removido() -> S.Programa:
  S.Programa{ctx => args => escrever("",
    S.Acessar{D.RemoverLinha{D.Usuarios{}, "u1"}, retorno => S.Terminar{D.VAusente{}}})}

def iniciar(p: S.Programa) -> N.Maquina:
  N.iniciar(p, contexto(), D.VAusente{}, inicial())

def um(p: S.Programa) -> N.Maquina:
  N.avancar(iniciar(p), esquema())

def dois(p: S.Programa) -> N.Maquina:
  N.avancar(um(p), esquema())

def tres(p: S.Programa) -> N.Maquina:
  N.avancar(dois(p), esquema())

def resumir_conclusao(c: N.Conclusao) -> Maybe<&1, D.Estado & S.Resposta>:
  N.Conclusao{publicado, resposta, bytes} = c
  Some{(publicado, resposta)}

def resumir(p: Maybe<&2, N.Preparada>) -> Maybe<&1, D.Estado & S.Resposta>:
  match p:
    case None{}:
      None{}
    case Some{preparada}:
      resumir_conclusao(N.concluir(preparada, inicial()))

law vazio_na_inicializacao_e_invalido:
  {R.estrutura(configuracao(), vazio()) == False{} : Bool}
def vazio_na_inicializacao_e_invalido():
  {==}

law vazio_na_autenticacao_e_recusado:
  {D.autenticar(inicial(), "") == None{} : Maybe<&2, D.Contexto>}
def vazio_na_autenticacao_e_recusado():
  {==}

law escrita_vazia_provisoria_permitida:
  {N.instantaneo(um(reparado())) == S.Prefixo{vazio(),
    [S.Evento{D.DefinirColuna{D.Usuarios{}, "u1", "credencial", D.VTexto{""}}, S.Escrita{}}]} : S.Percurso}
def escrita_vazia_provisoria_permitida():
  {==}

law reparar_antes_da_publicacao_permitido:
  {resumir(N.preparar(tres(reparado()), configuracao())) ==
    Some{(inicial(), S.Resposta{S.Sucesso{}, D.VAusente{}})} : Maybe<&1, D.Estado & S.Resposta>}
def reparar_antes_da_publicacao_permitido():
  {==}

law vazio_final_produz_dados_e_rollback:
  {resumir(N.preparar(dois(sem_reparo()), configuracao())) ==
    Some{(inicial(), S.resposta_erro(S.Dados{}))} : Maybe<&1, D.Estado & S.Resposta>}
def vazio_final_produz_dados_e_rollback():
  {==}

law recusa_nao_exige_reparar_estado_descartado:
  {resumir(N.preparar(dois(recusa()), configuracao())) ==
    Some{(inicial(), S.Resposta{S.Recusa{}, D.VTexto{"recusado"}})} : Maybe<&1, D.Estado & S.Resposta>}
def recusa_nao_exige_reparar_estado_descartado():
  {==}

law troca_atomica_de_credenciais_permitida:
  {resumir(N.preparar(tres(troca()), configuracao())) ==
    Some{(trocado(), S.Resposta{S.Sucesso{}, D.VAusente{}})} : Maybe<&1, D.Estado & S.Resposta>}
def troca_atomica_de_credenciais_permitida():
  {==}

law remover_usuario_com_credencial_provisoria_permitido:
  {resumir(N.preparar(tres(removido()), configuracao())) ==
    Some{(D.Estado{Nil{}, [usuario("u2", "b")]}, S.Resposta{S.Sucesso{}, D.VAusente{}})} : Maybe<&1, D.Estado & S.Resposta>}
def remover_usuario_com_credencial_provisoria_permitido():
  {==}
