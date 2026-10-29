import Base

# Sequencias de octetos sao listas de U32 acompanhadas de octetos_validos.
# Nenhuma conversao abaixo normaliza Unicode, substitui caracteres ou trunca
# mensagens. A relacao TextoCodificado exige texto valido explicitamente.

def comprimento(bs: List<&2, U32>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+comprimento(t)

def concatenar(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  match a:
    case Nil{}:
      b
    case Con{h, t}:
      Con{h, concatenar(t, b)}

def octetos_validos(bs: List<&2, U32>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{h, t}:
      U32.is_le(h, 255) && octetos_validos(t)

def codigo_valido(+cp: U32) -> Bool:
  U32.is_le(cp, 1114111) && (U32.is_lt(cp, 55296) || U32.is_gt(cp, 57343))

def texto_valido(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{cp}, tail}:
      codigo_valido(cp) && texto_valido(tail)

def be32(+x: U32) -> List<&2, U32>:
  [U32.and(U32.shrn(x, 24n), 255),
   U32.and(U32.shrn(x, 16n), 255),
   U32.and(U32.shrn(x, 8n), 255),
   U32.and(x, 255)]

def be64(alto: U32, baixo: U32) -> List<&2, U32>:
  concatenar(be32(alto), be32(baixo))

def utf8_codigo_emitir(+cp: U32, ascii: Bool, dois: Bool, tres: Bool) -> List<&2, U32>:
  match ascii dois tres:
    case True{} _ _:
      [cp]
    case False{} True{} _:
      [U32.or(192, U32.shrn(cp, 6n)),
       U32.or(128, U32.and(cp, 63))]
    case False{} False{} True{}:
      [U32.or(224, U32.shrn(cp, 12n)),
       U32.or(128, U32.and(U32.shrn(cp, 6n), 63)),
       U32.or(128, U32.and(cp, 63))]
    case False{} False{} False{}:
      [U32.or(240, U32.shrn(cp, 18n)),
       U32.or(128, U32.and(U32.shrn(cp, 12n), 63)),
       U32.or(128, U32.and(U32.shrn(cp, 6n), 63)),
       U32.or(128, U32.and(cp, 63))]

def utf8_codigo(+cp: U32) -> List<&2, U32>:
  utf8_codigo_emitir(cp, U32.is_lt(cp, 128), U32.is_lt(cp, 2048), U32.is_lt(cp, 65536))

def utf8(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{cp}, tail}:
      concatenar(utf8_codigo(cp), utf8(tail))

# Estado do reconhecedor UTF-8. Os valores de minimo proiben codificacoes
# mais longas do que o necessario. codigo_valido exclui surrogates e valores
# maiores do que U+10FFFF. Octetos finais ou iniciais indevidos dao Invalido.
type Decodificador is Data:
  Invalido{}
  Dec{faltam: Nat, acumulado: U32, minimo: U32}

def selecionar_dec(valido: Bool, estado: Decodificador) -> Decodificador:
  match valido:
    case False{}:
      Invalido{}
    case True{}:
      estado

def iniciar_codigo(+b: U32, ascii: Bool, dois: Bool, tres: Bool, quatro: Bool) -> Decodificador:
  match ascii dois tres quatro:
    case True{} _ _ _:
      Dec{0n, 0, 0}
    case False{} True{} _ _:
      Dec{1n, (b - 192 : U32), 128}
    case False{} False{} True{} _:
      Dec{2n, (b - 224 : U32), 2048}
    case False{} False{} False{} True{}:
      Dec{3n, (b - 240 : U32), 65536}
    case False{} False{} False{} False{}:
      Invalido{}

def iniciar(+b: U32) -> Decodificador:
  iniciar_codigo(b, U32.is_lt(b, 128),
    U32.is_ge(b, 194) && U32.is_le(b, 223),
    U32.is_ge(b, 224) && U32.is_le(b, 239),
    U32.is_ge(b, 240) && U32.is_le(b, 244))

def continuar_fim(faltam: Nat, +cp: U32, minimo: U32) -> Decodificador:
  match faltam:
    case 0n:
      selecionar_dec(U32.is_ge(cp, minimo) && codigo_valido(cp), Dec{0n, 0, 0})
    case 1n+p:
      Dec{1n+p, cp, minimo}

def continuar(faltam: Nat, acumulado: U32, minimo: U32, +b: U32) -> Decodificador:
  selecionar_dec(U32.is_ge(b, 128) && U32.is_le(b, 191),
    continuar_fim(faltam, (acumulado * 64 + b - 128 : U32), minimo))

def passo(estado: Decodificador, b: U32) -> Decodificador:
  match estado:
    case Invalido{}:
      Invalido{}
    case Dec{0n, acumulado, minimo}:
      iniciar(b)
    case Dec{1n+p, acumulado, minimo}:
      continuar(p, acumulado, minimo, b)

def fim(estado: Decodificador) -> Bool:
  match estado:
    case Invalido{}:
      False{}
    case Dec{0n, acumulado, minimo}:
      True{}
    case Dec{1n+p, acumulado, minimo}:
      False{}

def utf8_reconhecer(bs: List<&2, U32>, estado: Decodificador) -> Bool:
  match bs:
    case Nil{}:
      fim(estado)
    case Con{h, t}:
      utf8_reconhecer(t, passo(estado, h))

def utf8_valido(bs: List<&2, U32>) -> Bool:
  utf8_reconhecer(bs, Dec{0n, 0, 0})

def TextoCodificado(+texto: String, bytes: List<&2, U32>) -> Type:
  {texto_valido(texto) == True{} : Bool} &
  {utf8(texto) == bytes : List<&2, U32>}

def Octetos(bytes: List<&2, U32>) -> Type:
  {octetos_validos(bytes) == True{} : Bool}

def Palavra64(alto: U32, baixo: U32, bytes: List<&2, U32>) -> Type:
  {be64(alto, baixo) == bytes : List<&2, U32>}

# Conversao de comprimentos sem truncamento. A adicao verifica o transporte
# antes de usar aritmetica U32. Depois do maior u64 a resposta e None.
type Numero64 is Data:
  Numero64{alto: U32, baixo: U32}

def incrementar64_casos(+alto: U32, baixo: U32, transporte: Bool, esgotado: Bool) -> Maybe<&2, Numero64>:
  match transporte esgotado:
    case False{} _:
      Some{Numero64{alto, (baixo + 1 : U32)}}
    case True{} False{}:
      Some{Numero64{(alto + 1 : U32), 0}}
    case True{} True{}:
      None{}

def incrementar64(x: Maybe<&2, Numero64>) -> Maybe<&2, Numero64>:
  match x:
    case None{}:
      None{}
    case Some{Numero64{+alto, +baixo}}:
      incrementar64_casos(alto, baixo, U32.is_eq(baixo, 4294967295), U32.is_eq(alto, 4294967295))

def nat64(n: Nat) -> Maybe<&2, Numero64>:
  match n:
    case 0n:
      Some{Numero64{0, 0}}
    case 1n+p:
      incrementar64(nat64(p))

def numero64_bytes(x: Maybe<&2, Numero64>) -> Maybe<&2, List<&2, U32>>:
  match x:
    case None{}:
      None{}
    case Some{Numero64{alto, baixo}}:
      Some{be64(alto, baixo)}

def comprimento64(n: Nat) -> Maybe<&2, List<&2, U32>>:
  numero64_bytes(nat64(n))

def cabe64(x: Maybe<&2, Numero64>) -> Bool:
  match x:
    case None{}:
      False{}
    case Some{numero}:
      True{}

def comprimento_representavel(n: Nat) -> Bool:
  cabe64(nat64(n))
