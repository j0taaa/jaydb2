import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D

# API publica: decodificar(bytes, B.Numero64{alto, baixo}) -> Resultado.
# bytes e o CORPO completo (sem os oito bytes externos de enquadramento).
# O limite publico conta bytes do corpo, inclusive tags e comprimentos.
# Decodificado contem exatamente D.Valor; Entrada recusa sintaxe, Unicode,
# nomes, truncamento e bytes extras; Limite indica corpo ou tamanho minimo
# declarado acima do limite/u64. Igualdade com o limite e permitida.
# A recepcao e o enquadramento ficam no chamador; nao ha orcamento fisico.
# Nenhum contador do cliente vira Nat, alocacao ou combustivel. A maquina
# avanca uma vez por octeto; emitir desempilha estruturalmente. Portanto nao
# existe teto adicional de profundidade, quantidade ou tamanho textual.
type Resultado is Data:
  Decodificado{valor: D.Valor}
  Entrada{}
  Limite{}

def zero64(+n: B.Numero64) -> Bool:
  B.Numero64{a, b} = n
  U32.is_eq(a, 0) && U32.is_eq(b, 0)

def um64(n: B.Numero64) -> Bool:
  B.Numero64{a, b} = n
  U32.is_eq(a, 0) && U32.is_eq(b, 1)

def menor_igual64(a: B.Numero64, b: B.Numero64) -> Bool:
  B.Numero64{+ah, al} = a
  B.Numero64{+bh, bl} = b
  U32.is_lt(ah, bh) || (U32.is_eq(ah, bh) && U32.is_le(al, bl))

def diminuir64_casos(baixo_zero: Bool, alto_zero: Bool, a: U32, b: U32) -> B.Numero64:
  match baixo_zero alto_zero:
    case False{} _:
      B.Numero64{a, (b - 1 : U32)}
    case True{} False{}:
      B.Numero64{(a - 1 : U32), 4294967295}
    case True{} True{}:
      B.Numero64{0, 0}

# Total em zero; as transicoes so decrementam contadores positivos.
def diminuir64(n: B.Numero64) -> B.Numero64:
  B.Numero64{+a, +b} = n
  diminuir64_casos(U32.is_eq(b, 0), U32.is_eq(a, 0), a, b)

def soma64_fim(overflow: Bool, alto: U32, baixo: U32) -> Maybe<&2, B.Numero64>:
  match overflow:
    case True{}:
      None{}
    case False{}:
      Some{B.Numero64{alto, baixo}}

def soma64_transporte(carry: Bool, +alto: U32, baixo: U32, overflow: Bool) -> Maybe<&2, B.Numero64>:
  match carry:
    case False{}:
      soma64_fim(overflow, alto, baixo)
    case True{}:
      soma64_fim(overflow || U32.is_eq(alto, 4294967295), (alto + 1 : U32), baixo)

def somar64(a: B.Numero64, b: B.Numero64) -> Maybe<&2, B.Numero64>:
  B.Numero64{+ah, +al} = a
  B.Numero64{bh, bl} = b
  +baixo = (al + bl : U32)
  +alto = (ah + bh : U32)
  soma64_transporte(U32.is_lt(baixo, al), alto, baixo, U32.is_lt(alto, ah))

def somar_opcionais(a: Maybe<&2, B.Numero64>, b: Maybe<&2, B.Numero64>) -> Maybe<&2, B.Numero64>:
  match a b:
    case Some{x} Some{y}:
      somar64(x, y)
    case _ _:
      None{}

def multiplicar_pequeno(n: Nat, +x: B.Numero64) -> Maybe<&2, B.Numero64>:
  match n:
    case 0n:
      Some{B.Numero64{0, 0}}
    case 1n:
      Some{x}
    case 1n+p:
      somar_opcionais(Some{x}, multiplicar_pequeno(p, x))

def somar_pendencia_casos(vazia: Bool, n: B.Numero64, fator: Nat, resto: Maybe<&2, B.Numero64>) -> Maybe<&2, B.Numero64>:
  match vazia:
    case True{}:
      resto
    case False{}:
      somar_opcionais(multiplicar_pequeno(fator, n), resto)

# Nao multiplica nem soma o contador vazio dos ancestrais ja no ultimo filho.
def somar_pendencia(+n: B.Numero64, fator: Nat, resto: Maybe<&2, B.Numero64>) -> Maybe<&2, B.Numero64>:
  somar_pendencia_casos(zero64(n), n, fator, resto)

type Pilha is Data:
  Raiz{}
  Lista{ultimo: Bool, restantes: B.Numero64, invertidos: List<&2, D.Valor>, pai: Pilha}
  Nome{ultimo: Bool, restantes: B.Numero64, anterior: String, invertidos: List<&2, D.Campo>, pai: Pilha}
  Campo{ultimo: Bool, restantes: B.Numero64, nome: String, invertidos: List<&2, D.Campo>, pai: Pilha}

type Finalidade is Data:
  Inteiro{}
  Texto{}
  NomeTexto{}
  ContaLista{}
  ContaRegistro{}

type Unicode is Data:
  Inicio{}
  Continua{faltam: Nat, codigo: U32, minimo: U32}

type Escalar is Data:
  Caractere{codigo: U32}
  Parcial{estado: Unicode}
  UTFInvalido{}

type Maquina is Data:
  Tag{pilha: Pilha}
  TagNome{pilha: Pilha}
  Palavra{finalidade: Finalidade, faltam: Nat, alto: U32, baixo: U32, pilha: Pilha}
  Conteudo{nome: Bool, ultimo: Bool, restantes: B.Numero64, unicode: Unicode, invertido: String, pilha: Pilha}
  Pronto{valor: D.Valor}
  Invalido{}
  Acima{}

def montar_lista(xs: List<&2, D.Valor>, acc: D.Valor) -> D.Valor:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      montar_lista(t, D.VLista{h, acc})

def montar_registro(xs: List<&2, D.Campo>, acc: D.Valor) -> D.Valor:
  match xs:
    case Nil{}:
      acc
    case Con{D.Campo{n, v}, t}:
      montar_registro(t, D.VRegistro{n, v, acc})

# O ultimo filho pode completar qualquer numero de ancestrais sem ler bytes.
# A recursao desce somente pelo campo pai da pilha original.
def emitir(pilha: Pilha, valor: D.Valor) -> Maquina:
  match pilha:
    case Raiz{}:
      Pronto{valor}
    case Lista{True{}, q, xs, pai}:
      emitir(pai, montar_lista(Con{valor, xs}, D.VListaVazia{}))
    case Lista{False{}, +q, xs, pai}:
      Tag{Lista{um64(q), diminuir64(q), Con{valor, xs}, pai}}
    case Campo{True{}, q, n, xs, pai}:
      emitir(pai, montar_registro(Con{D.Campo{n, valor}, xs}, D.VRegistroVazio{}))
    case Campo{False{}, +q, +n, xs, pai}:
      TagNome{Nome{um64(q), diminuir64(q), n, Con{D.Campo{n, valor}, xs}, pai}}
    case Nome{u, q, n, xs, pai}:
      Invalido{}

# Minimo dos irmaos ainda pendentes; o valor atual ja comecou e nao entra.
# Um par de registro exige no minimo 4/u64/um ASCII/tag: onze octetos.
# Durante o nome do par atual ainda falta pelo menos um octeto de valor.
def minimo_pilha(pilha: Pilha) -> Maybe<&2, B.Numero64>:
  match pilha:
    case Raiz{}:
      Some{B.Numero64{0, 0}}
    case Lista{u, q, xs, pai}:
      somar_pendencia(q, 1n, minimo_pilha(pai))
    case Nome{u, q, n, xs, pai}:
      somar_opcionais(Some{B.Numero64{0, 1}}, somar_pendencia(q, 11n, minimo_pilha(pai)))
    case Campo{u, q, n, xs, pai}:
      somar_pendencia(q, 11n, minimo_pilha(pai))

type Conferencia is Data:
  Cabe{}
  Curto{}
  Grande{}

def conferir_casos(cabe_limite: Bool, cabe_corpo: Bool) -> Conferencia:
  match cabe_limite cabe_corpo:
    case False{} _:
      Grande{}
    case True{} False{}:
      Curto{}
    case True{} True{}:
      Cabe{}

def conferir(minimo: Maybe<&2, B.Numero64>, corpo: B.Numero64, teto: B.Numero64) -> Conferencia:
  match minimo:
    case None{}:
      Grande{}
    case Some{+n}:
      conferir_casos(menor_igual64(n, teto), menor_igual64(n, corpo))

def minimo_campo(f: Finalidade, n: B.Numero64) -> Maybe<&2, B.Numero64>:
  match f:
    case ContaRegistro{}:
      multiplicar_pequeno(11n, n)
    case _:
      Some{n}

def abrir_nome(cabe: Bool, +n: B.Numero64, pilha: Pilha) -> Maquina:
  match cabe:
    case False{}:
      Invalido{}
    case True{}:
      Conteudo{True{}, um64(n), diminuir64(n), Inicio{}, "", pilha}

def abrir_variavel(vazio: Bool, f: Finalidade, +n: B.Numero64, pilha: Pilha) -> Maquina:
  match vazio f:
    case True{} Texto{}:
      emitir(pilha, D.VTexto{""})
    case True{} ContaLista{}:
      emitir(pilha, D.VListaVazia{})
    case True{} ContaRegistro{}:
      emitir(pilha, D.VRegistroVazio{})
    case False{} Texto{}:
      Conteudo{False{}, um64(n), diminuir64(n), Inicio{}, "", pilha}
    case False{} NomeTexto{}:
      abrir_nome(menor_igual64(n, B.Numero64{0, 64}), n, pilha)
    case False{} ContaLista{}:
      Tag{Lista{um64(n), diminuir64(n), Nil{}, pilha}}
    case False{} ContaRegistro{}:
      TagNome{Nome{um64(n), diminuir64(n), "", Nil{}, pilha}}
    case _ _:
      Invalido{}

def abrir_conferido(c: Conferencia, f: Finalidade, +n: B.Numero64, pilha: Pilha) -> Maquina:
  match c:
    case Grande{}:
      Acima{}
    case Curto{}:
      Invalido{}
    case Cabe{}:
      abrir_variavel(zero64(n), f, n, pilha)

def concluir_palavra(f: Finalidade, +alto: U32, +baixo: U32, +pilha: Pilha, corpo: B.Numero64, teto: B.Numero64) -> Maquina:
  match f:
    case Inteiro{}:
      emitir(pilha, D.VInt{alto, baixo})
    case +outra:
      +n = {B.Numero64{alto, baixo} : B.Numero64}
      abrir_conferido(conferir(somar_opcionais(minimo_campo(outra, n), minimo_pilha(pilha)), corpo, teto), outra, n, pilha)

def ler_palavra(faltam: Nat, f: Finalidade, alto: U32, +baixo: U32, b: U32, pilha: Pilha, corpo: B.Numero64, teto: B.Numero64) -> Maquina:
  match faltam:
    case 0n:
      concluir_palavra(f, (alto * 256 + U32.shrn(baixo, 24n) : U32), (baixo * 256 + b : U32), pilha, corpo, teto)
    case 1n+p:
      Palavra{f, p, (alto * 256 + U32.shrn(baixo, 24n) : U32), (baixo * 256 + b : U32), pilha}

def iniciar_utf8(ascii: Bool, dois: Bool, tres: Bool, quatro: Bool, b: U32) -> Escalar:
  match ascii dois tres quatro:
    case True{} _ _ _:
      Caractere{b}
    case False{} True{} _ _:
      Parcial{Continua{1n, (b - 192 : U32), 128}}
    case False{} False{} True{} _:
      Parcial{Continua{2n, (b - 224 : U32), 2048}}
    case False{} False{} False{} True{}:
      Parcial{Continua{3n, (b - 240 : U32), 65536}}
    case _ _ _ _:
      UTFInvalido{}

def escalar_conferido(valido: Bool, cp: U32) -> Escalar:
  match valido:
    case False{}:
      UTFInvalido{}
    case True{}:
      Caractere{cp}

def completar_utf8(faltam: Nat, +cp: U32, minimo: U32) -> Escalar:
  match faltam:
    case 0n:
      escalar_conferido(U32.is_ge(cp, minimo) && B.codigo_valido(cp), cp)
    case 1n+p:
      Parcial{Continua{1n+p, cp, minimo}}

def continuar_utf8(valido: Bool, faltam: Nat, cp: U32, minimo: U32, b: U32) -> Escalar:
  match valido:
    case False{}:
      UTFInvalido{}
    case True{}:
      completar_utf8(faltam, (cp * 64 + b - 128 : U32), minimo)

def passo_utf8(u: Unicode, +b: U32) -> Escalar:
  match u:
    case Inicio{}:
      iniciar_utf8(U32.is_lt(b, 128), U32.is_ge(b, 194) && U32.is_le(b, 223), U32.is_ge(b, 224) && U32.is_le(b, 239), U32.is_ge(b, 240) && U32.is_le(b, 244), b)
    case Continua{1n+p, cp, minimo}:
      continuar_utf8(U32.is_ge(b, 128) && U32.is_le(b, 191), p, cp, minimo, b)
    case Continua{0n, cp, minimo}:
      UTFInvalido{}

def nome_conferido(valido: Bool, u: Bool, q: B.Numero64, nome: String, xs: List<&2, D.Campo>, pai: Pilha) -> Maquina:
  match valido:
    case False{}:
      Invalido{}
    case True{}:
      Tag{Campo{u, q, nome, xs, pai}}

def emitir_nome(pilha: Pilha, +nome: String) -> Maquina:
  match pilha:
    case Nome{u, q, anterior, xs, pai}:
      nome_conferido(D.nome_valido(nome) && String.is_lt(anterior, nome), u, q, nome, xs, pai)
    case _:
      Invalido{}

def emitir_texto(nome: Bool, texto: String, pilha: Pilha) -> Maquina:
  match nome:
    case False{}:
      emitir(pilha, D.VTexto{texto})
    case True{}:
      emitir_nome(pilha, texto)

def guardar_caractere(ultimo: Bool, nome: Bool, +q: B.Numero64, texto: String, pilha: Pilha) -> Maquina:
  match ultimo:
    case True{}:
      emitir_texto(nome, String.reverse(texto), pilha)
    case False{}:
      Conteudo{nome, um64(q), diminuir64(q), Inicio{}, texto, pilha}

def guardar_parcial(ultimo: Bool, nome: Bool, +q: B.Numero64, u: Unicode, texto: String, pilha: Pilha) -> Maquina:
  match ultimo:
    case True{}:
      Invalido{}
    case False{}:
      Conteudo{nome, um64(q), diminuir64(q), u, texto, pilha}

def guardar_escalar(e: Escalar, ultimo: Bool, nome: Bool, q: B.Numero64, texto: String, pilha: Pilha) -> Maquina:
  match e:
    case UTFInvalido{}:
      Invalido{}
    case Caractere{cp}:
      guardar_caractere(ultimo, nome, q, SCon{Chr{cp}, texto}, pilha)
    case Parcial{u}:
      guardar_parcial(ultimo, nome, q, u, texto, pilha)

def ler_tag(tag: Nat, pilha: Pilha) -> Maquina:
  match tag:
    case 0n:
      emitir(pilha, D.VAusente{})
    case 1n:
      emitir(pilha, D.VBool{False{}})
    case 2n:
      emitir(pilha, D.VBool{True{}})
    case 3n:
      Palavra{Inteiro{}, 7n, 0, 0, pilha}
    case 4n:
      Palavra{Texto{}, 7n, 0, 0, pilha}
    case 5n:
      Palavra{ContaLista{}, 7n, 0, 0, pilha}
    case 6n:
      Palavra{ContaRegistro{}, 7n, 0, 0, pilha}
    case _:
      Invalido{}

def ler_tag_nome(correto: Bool, pilha: Pilha) -> Maquina:
  match correto:
    case False{}:
      Invalido{}
    case True{}:
      Palavra{NomeTexto{}, 7n, 0, 0, pilha}

def passo(m: Maquina, b: U32, corpo: B.Numero64, teto: B.Numero64) -> Maquina:
  match m:
    case Tag{pilha}:
      ler_tag(U32.to_nat(b), pilha)
    case TagNome{pilha}:
      ler_tag_nome(U32.is_eq(b, 4), pilha)
    case Palavra{f, n, alto, baixo, pilha}:
      ler_palavra(n, f, alto, baixo, b, pilha, corpo, teto)
    case Conteudo{nome, ultimo, q, u, texto, pilha}:
      guardar_escalar(passo_utf8(u, b), ultimo, nome, q, texto, pilha)
    case Pronto{v}:
      Invalido{}
    case Invalido{}:
      Invalido{}
    case Acima{}:
      Acima{}

def finalizar(m: Maquina) -> Resultado:
  match m:
    case Pronto{v}:
      Decodificado{v}
    case Acima{}:
      Limite{}
    case _:
      Entrada{}

def percorrer(bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64, m: Maquina) -> Resultado:
  match bs:
    case Nil{}:
      finalizar(m)
    case Con{h, t}:
      +resto = diminuir64(corpo)
      +livre = diminuir64(teto)
      percorrer(t, resto, livre, passo(m, h, resto, livre))

def decodificar_octetos(validos: Bool, bs: List<&2, U32>, corpo: B.Numero64, teto: B.Numero64) -> Resultado:
  match validos:
    case False{}:
      Entrada{}
    case True{}:
      percorrer(bs, corpo, teto, Tag{Raiz{}})

def decodificar_tamanho(cabe: Bool, +bs: List<&2, U32>, corpo: B.Numero64, teto: B.Numero64) -> Resultado:
  match cabe:
    case False{}:
      Limite{}
    case True{}:
      decodificar_octetos(B.octetos_validos(bs), bs, corpo, teto)

def decodificar_medida(n: Maybe<&2, B.Numero64>, bs: List<&2, U32>, +teto: B.Numero64) -> Resultado:
  match n:
    case None{}:
      Limite{}
    case Some{+corpo}:
      decodificar_tamanho(menor_igual64(corpo, teto), bs, corpo, teto)

def decodificar(+bytes: List<&2, U32>, limite: B.Numero64) -> Resultado:
  decodificar_medida(B.nat64(B.comprimento(bytes)), bytes, limite)
