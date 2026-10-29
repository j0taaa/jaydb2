import Base
import ./Bytes.bend as B
import ./Dados.bend as D

# Formato canonico (tags decimais): 0 ausencia, 1 false, 2 true,
# 3 inteiro64, 4 texto UTF-8, 5 lista, 6 registro. Comprimentos e
# contagens usam u64 big endian. Um nome de registro usa texto com tag 4.
# None significa valor invalido ou comprimento nao representavel; nunca
# ha truncamento, wraparound de comprimento ou resposta parcial.

def concatenar_opcional(a: Maybe<&2, List<&2, U32>>, b: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match a b:
    case Some{xs} Some{ys}:
      Some{B.concatenar(xs, ys)}
    case _ _:
      None{}

def prefixar_tamanho(tag: U32, tamanho: Maybe<&2, List<&2, U32>>, conteudo: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match tamanho:
    case None{}:
      None{}
    case Some{cabecalho}:
      Some{Con{tag, B.concatenar(cabecalho, conteudo)}}

def campo_variavel(tag: U32, n: Nat, conteudo: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  prefixar_tamanho(tag, B.comprimento64(n), conteudo)

def texto_casos(valido: Bool, +bytes: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match valido:
    case False{}:
      None{}
    case True{}:
      campo_variavel(4, B.comprimento(bytes), bytes)

def texto(+s: String) -> Maybe<&2, List<&2, U32>>:
  texto_casos(B.texto_valido(s), B.utf8(s))

type Parcial is Data:
  Impossivel{}
  Atomo{bytes: List<&2, U32>}
  Lista{numero: Nat, bytes: List<&2, U32>}
  Registro{numero: Nat, bytes: List<&2, U32>}

def finalizar(p: Parcial) -> Maybe<&2, List<&2, U32>>:
  match p:
    case Impossivel{}:
      None{}
    case Atomo{bytes}:
      Some{bytes}
    case Lista{n, bytes}:
      campo_variavel(5, n, bytes)
    case Registro{n, bytes}:
      campo_variavel(6, n, bytes)

def atomo_opcional(p: Maybe<&2, List<&2, U32>>) -> Parcial:
  match p:
    case None{}:
      Impossivel{}
    case Some{bytes}:
      Atomo{bytes}

def booleano(b: Bool) -> Parcial:
  match b:
    case False{}:
      Atomo{[1]}
    case True{}:
      Atomo{[2]}

def lista_casos(h: Maybe<&2, List<&2, U32>>, t: Parcial) -> Parcial:
  match h t:
    case Some{cabeca} Lista{n, cauda}:
      Lista{1n+n, B.concatenar(cabeca, cauda)}
    case _ _:
      Impossivel{}

def registro_casos(n: Maybe<&2, List<&2, U32>>, v: Maybe<&2, List<&2, U32>>, r: Parcial) -> Parcial:
  match n v r:
    case Some{nome} Some{valor} Registro{q, resto}:
      Registro{1n+q, B.concatenar(nome, B.concatenar(valor, resto))}
    case _ _ _:
      Impossivel{}

def codificar_parcial(v: D.Valor) -> Parcial:
  match v:
    case D.VAusente{}:
      Atomo{[0]}
    case D.VBool{b}:
      booleano(b)
    case D.VInt{alto, baixo}:
      Atomo{Con{3, B.be64(alto, baixo)}}
    case D.VTexto{s}:
      atomo_opcional(texto(s))
    case D.VListaVazia{}:
      Lista{0n, Nil{}}
    case D.VLista{h, t}:
      lista_casos(finalizar(codificar_parcial(h)), codificar_parcial(t))
    case D.VRegistroVazio{}:
      Registro{0n, Nil{}}
    case D.VRegistro{n, v, r}:
      registro_casos(texto(n), finalizar(codificar_parcial(v)), codificar_parcial(r))

def codificar_casos(valido: Bool, resultado: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match valido:
    case False{}:
      None{}
    case True{}:
      resultado

def codificar(+v: D.Valor) -> Maybe<&2, List<&2, U32>>:
  codificar_casos(D.valor_valido(v), finalizar(codificar_parcial(v)))

def representavel_resultado(r: Maybe<&2, List<&2, U32>>) -> Bool:
  match r:
    case None{}:
      False{}
    case Some{bytes}:
      True{}

def representavel(v: D.Valor) -> Bool:
  representavel_resultado(codificar(v))

def Codificacao(v: D.Valor, bytes: List<&2, U32>) -> Type:
  {codificar(v) == Some{bytes} : Maybe<&2, List<&2, U32>>}

# Decodificar significa encontrar exatamente um valor cuja codificacao
# canonica coincide com todos os bytes. Esta relacao nao aceita bytes extras,
# variantes de UTF-8, registros fora de ordem ou nomes duplicados.
def Decodificacao(bytes: List<&2, U32>, v: D.Valor) -> Type:
  Codificacao(v, bytes)

def enquadrar_conteudo(+bytes: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  concatenar_opcional(B.comprimento64(B.comprimento(bytes)), Some{bytes})

def enquadrar_resultado(r: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match r:
    case None{}:
      None{}
    case Some{bytes}:
      enquadrar_conteudo(bytes)

def enquadrar(v: D.Valor) -> Maybe<&2, List<&2, U32>>:
  enquadrar_resultado(codificar(v))

def Mensagem(v: D.Valor, bytes: List<&2, U32>) -> Type:
  {enquadrar(v) == Some{bytes} : Maybe<&2, List<&2, U32>>}

# A identidade textual de codigo/prova inclui todos os caracteres; seu
# fechamento de dependencias pertence ao contrato de admissao do nucleo.
type Requisicao is Data:
  Requisicao{credencial: String, codigo: String, argumentos: D.Valor, prova: String}

def requisicao_valor(r: Requisicao) -> D.Valor:
  Requisicao{credencial, codigo, argumentos, prova} = r
  D.VRegistro{"argumentos", argumentos,
    D.VRegistro{"codigo", D.VTexto{codigo},
      D.VRegistro{"credencial", D.VTexto{credencial},
        D.VRegistro{"prova", D.VTexto{prova}, D.VRegistroVazio{}}}}}

def RequisicaoCodificada(r: Requisicao, bytes: List<&2, U32>) -> Type:
  Mensagem(requisicao_valor(r), bytes)

type Status is Data:
  Entrada{}
  Autenticacao{}
  Certificado{}
  Dados{}
  Limite{}
  Falha{}
  Recusa{}
  Sucesso{}

def status_texto(s: Status) -> String:
  match s:
    case Entrada{}:
      "entrada"
    case Autenticacao{}:
      "autenticacao"
    case Certificado{}:
      "certificado"
    case Dados{}:
      "dados"
    case Limite{}:
      "limite"
    case Falha{}:
      "falha"
    case Recusa{}:
      "recusa"
    case Sucesso{}:
      "sucesso"

type Resposta is Data:
  Resposta{status: Status, valor: D.Valor}

def resposta_valor(r: Resposta) -> D.Valor:
  Resposta{s, v} = r
  D.VRegistro{"status", D.VTexto{status_texto(s)},
    D.VRegistro{"valor", v, D.VRegistroVazio{}}}

def valor_resposta_valido(s: Status, v: D.Valor) -> Bool:
  match s v:
    case Sucesso{} _:
      D.valor_valido(v)
    case Recusa{} _:
      D.valor_valido(v)
    case _ D.VAusente{}:
      True{}
    case _ _:
      False{}

def resposta_valida(r: Resposta) -> Bool:
  Resposta{s, v} = r
  valor_resposta_valido(s, v)

def RespostaCodificada(+r: Resposta, bytes: List<&2, U32>) -> Type:
  {resposta_valida(r) == True{} : Bool} &
  Mensagem(resposta_valor(r), bytes)
