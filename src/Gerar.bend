# Reificacao dos valores publicos realmente decodificados/autenticados.
# Argumentos usam octetos canonicos em literal escapado, sem AST aninhada.
# Nenhum dado do estado privado e inserido no modulo de certificado.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Bytes.bend as B
import ../contrato/Protocolo.bend as P
import ./Reificacao.bend as R

def texto(s: String) -> String:
  match s:
    case SNil{}:
      "SNil{}"
    case SCon{Chr{codigo}, resto}:
      "SCon{Chr{" ++ U32.show(codigo) ++ "}," ++ texto(resto) ++ "}"

def booleano(b: Bool) -> String:
  match b:
    case True{}:
      "True{}"
    case False{}:
      "False{}"

def valor(v: D.Valor) -> String:
  match v:
    case D.VAusente{}:
      "D.VAusente{}"
    case D.VBool{b}:
      "D.VBool{" ++ booleano(b) ++ "}"
    case D.VInt{alto, baixo}:
      "D.VInt{" ++ U32.show(alto) ++ "," ++ U32.show(baixo) ++ "}"
    case D.VTexto{s}:
      "D.VTexto{" ++ texto(s) ++ "}"
    case D.VListaVazia{}:
      "D.VListaVazia{}"
    case D.VLista{h, t}:
      "D.VLista{" ++ valor(h) ++ "," ++ valor(t) ++ "}"
    case D.VRegistroVazio{}:
      "D.VRegistroVazio{}"
    case D.VRegistro{nome, v, resto}:
      "D.VRegistro{" ++ texto(nome) ++ "," ++ valor(v) ++ "," ++ valor(resto) ++ "}"

def hexadecimal(n: U32, pequeno: Bool) -> Char:
  match pequeno:
    case True{}:
      Chr{(48 + n : U32)}
    case False{}:
      Chr{(87 + n : U32)}

def escapar(+n: U32, aspas: Bool, barra: Bool, controle: Bool) -> String:
  match aspas barra controle:
    case True{} _ _:
      "\\\""
    case False{} True{} _:
      "\\\\"
    case False{} False{} True{}:
      +alto = U32.shrn(n, 4n)
      +baixo = U32.and(n, 15)
      "\\u{" ++ SCon{hexadecimal(alto, U32.is_lt(alto, 10)),
        SCon{hexadecimal(baixo, U32.is_lt(baixo, 10)), SNil{}}} ++ "}"
    case False{} False{} False{}:
      SCon{Chr{n}, SNil{}}

def literal_corpo(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{Chr{+n}, t}:
      escapar(n, U32.is_eq(n, 34), U32.is_eq(n, 92), U32.is_lt(n, 32)) ++ literal_corpo(t)

def literal(s: String) -> String:
  "\"" ++ literal_corpo(s) ++ "\""

def contexto(c: D.Contexto) -> String:
  D.Contexto{id, tipo} = c
  "D.Contexto{" ++ literal(id) ++ "," ++ literal(tipo) ++ "}"

def instancia_conteudo(ctx: D.Contexto, bytes: List<&2, U32>, alto: U32, baixo: U32) -> String:
  "import Base\n" ++
  "import ./Dados.bend as D\n" ++
  "import ./Semantica.bend as S\n" ++
  "import ./Reificacao.bend as Reificacao\n" ++
  "import ./Configuration.bend as C\n\n" ++
  "def config() -> S.Configuracao:\n  C.config()\n\n" ++
  "def contexto() -> D.Contexto:\n  " ++ contexto(ctx) ++ "\n\n" ++
  "def argumentos() -> D.Valor:\n  Reificacao.argumentos(" ++ literal(R.texto(bytes)) ++
    ", " ++ U32.show(alto) ++ ", " ++ U32.show(baixo) ++ ")\n"

def instancia_medida(medida: Maybe<&2, B.Numero64>, ctx: D.Contexto, bytes: List<&2, U32>) -> Maybe<&2, String>:
  match medida:
    case None{}:
      None{}
    case Some{B.Numero64{alto, baixo}}:
      Some{instancia_conteudo(ctx, bytes, alto, baixo)}

def instancia_codificada(codificada: Maybe<&2, List<&2, U32>>, ctx: D.Contexto) -> Maybe<&2, String>:
  match codificada:
    case None{}:
      None{}
    case Some{+bytes}:
      instancia_medida(B.nat64(B.comprimento(bytes)), ctx, bytes)

def instancia(ctx: D.Contexto, argumentos: D.Valor) -> Maybe<&2, String>:
  instancia_codificada(P.codificar(argumentos), ctx)

def vinculos(codigo: String) -> String:
  "import Base\n" ++
  "import ./Dados.bend as D\n" ++
  "import ./Semantica.bend as S\n" ++
  "import ./Requisitos.bend as R\n" ++
  "import ./Interface.bend as F\n" ++
  "import ./Instance.bend as I\n" ++
  "import ./Client.bend as Client\n\n" ++
  "def codigo() -> String:\n  " ++ literal(codigo) ++ "\n\n" ++
  "law certificado:\n  R.Certifica(I.config(), codigo(), Client.programa(), I.contexto(), I.argumentos())\n\n" ++
  "law termina:\n  F.ProgramaTermina(I.config(), Client.programa())\n"

law texto_nao_interpreta_sequencia_de_escape:
  {texto("\\n") == "SCon{Chr{92},SCon{Chr{110},SNil{}}}" : String}
def texto_nao_interpreta_sequencia_de_escape():
  {==}

law inteiro_preserva_ambas_as_palavras:
  {valor(D.VInt{4294967295, 2147483648}) == "D.VInt{4294967295,2147483648}" : String}
def inteiro_preserva_ambas_as_palavras():
  {==}

law literal_nao_permite_injecao_de_fonte:
  {literal("\"\\\n") == "\"\\\"\\\\\\u{0a}\"" : String}
def literal_nao_permite_injecao_de_fonte():
  {==}
