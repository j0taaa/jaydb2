# Chamadas primitivas do nucleo, sem tags de publicacao ou conclusao.
import Base
import ./ProtocoloServico.bend as Q
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../contrato/Protocolo.bend as P
import ../src/Codec.bend as C
import ../src/Estado.bend as E
import ./CodecRecusas.bend as R
import ./CodecSomas64.bend as W
import ./Fundamentos.bend as F

# Os campos sao registrados pelo passo real do parser.
type Primitiva is Data:
  Prefixo{quantidade: Nat, original: Primitiva}
  Codificar{valor: D.Valor}
  Decodificar{bytes: List<&2, U32>, teto: B.Numero64}
  Guardar{esquema: D.Esquema, estado: D.Estado}
  Ler{antes: Nat, capacidade: Nat, recebido: Nat, declarado: Nat}

# A abertura de campos variaveis usa a conferencia da funcao real.
def conferencia(f: C.Finalidade, alto: U32, baixo: U32,
  pilha: C.Pilha, corpo: B.Numero64, teto: B.Numero64) -> C.Conferencia:
  C.conferir(C.somar_opcionais(C.minimo_campo(f, B.Numero64{alto, baixo}),
    C.minimo_pilha(pilha)), corpo, teto)

def construir(c: C.Conferencia, +pos: Nat, +n: Nat) -> List<&2, Q.Quadro>:
  match c:
    case C.Cabe{}: [Q.Conferida{pos, n}, Q.Construida{pos, n}]
    case _: Nil{}

# Guardar representa a serializacao/copia do snapshot publicado ou da proposta
# de sucesso ja validada. Nao representa os stores dos estados privados da
# maquina: estes seguem Nucleo/Operou e a fidelidade do compilador oficial.
# A abstracao e a funcao real Estado.decodificar, nao o estado repetido por definicao.
def guardar_abstracao(q: Maybe<&2, D.Estado>, s: D.Estado, bs: List<&2, U32>) -> List<&2, Q.Quadro>:
  match q:
    case None{}: Nil{}
    case Some{a}: [Q.Guardada{s, bs, a}]

def guardar_bytes(q: Maybe<&2, List<&2, U32>>, e: D.Esquema, +s: D.Estado) -> List<&2, Q.Quadro>:
  match q:
    case None{}: Nil{}
    case Some{bs}: guardar_abstracao(E.decodificar(D.estado_valor(s), e), s, bs)

def quantidade(alto: U32, baixo: U32) -> Nat:
  Word.to_nat(64n, W.bits(B.Numero64{alto, baixo}))

def abrir_nome_valido(f: C.Finalidade, +alto: U32, +baixo: U32) -> Bool:
  match f:
    case C.Inteiro{}: False{}
    case C.NomeTexto{}:
      Bool.not(C.zero64(B.Numero64{alto, baixo})) && C.menor_igual64(B.Numero64{alto, baixo}, B.Numero64{0, 64})
    case _: True{}

def abrir_campo(c: C.Conferencia, pronto: Bool, +pos: Nat, +n: Nat) -> List<&2, Q.Quadro>:
  match c pronto:
    case C.Cabe{} True{}: construir(C.Cabe{}, pos, n)
    case C.Cabe{} False{}: [Q.Conferida{pos, n}]
    case _ _: Nil{}

def quadro_campo(+pos: Nat, +f: C.Finalidade, +alto: U32, +baixo: U32, pilha: C.Pilha,
  corpo: B.Numero64, teto: B.Numero64) -> List<&2, Q.Quadro>:
  abrir_campo(conferencia(f, alto, baixo, pilha, corpo, teto), abrir_nome_valido(f, alto, baixo),
    pos, quantidade(alto, baixo))

# Este e o passo real do Codec; apenas registra as aberturas nele realizadas.
def quadro_tag(tag: Nat, pos: Nat) -> List<&2, Q.Quadro>:
  match tag:
    case 0n: construir(C.Cabe{}, pos, 1n)
    case 1n: construir(C.Cabe{}, pos, 1n)
    case 2n: construir(C.Cabe{}, pos, 1n)
    case 3n+k: Nil{}

def quadro_palavra(+f: C.Finalidade, +alto: U32, +baixo: U32, pilha: C.Pilha,
  corpo: B.Numero64, teto: B.Numero64, pos: Nat) -> List<&2, Q.Quadro>:
  match f:
    case C.Inteiro{}: construir(C.Cabe{}, pos, 8n)
    case C.Texto{}: quadro_campo(pos, C.Texto{}, alto, baixo, pilha, corpo, teto)
    case C.NomeTexto{}: quadro_campo(pos, C.NomeTexto{}, alto, baixo, pilha, corpo, teto)
    case C.ContaLista{}: quadro_campo(pos, C.ContaLista{}, alto, baixo, pilha, corpo, teto)
    case C.ContaRegistro{}: quadro_campo(pos, C.ContaRegistro{}, alto, baixo, pilha, corpo, teto)

def quadro_passo(m: C.Maquina, +b: U32, corpo: B.Numero64, teto: B.Numero64, pos: Nat) -> List<&2, Q.Quadro>:
  match m:
    case C.Tag{pilha}: quadro_tag(U32.to_nat(b), pos)
    case C.Palavra{f, 0n, alto, +baixo, pilha}:
      quadro_palavra(f, (alto * 256 + U32.shrn(baixo, 24n) : U32), (baixo * 256 + b : U32), pilha, corpo, teto, pos)
    case C.TagNome{pilha}: Nil{}
    case C.Palavra{f, 1n+n, alto, baixo, pilha}: Nil{}
    case C.Conteudo{nome, ultimo, q, u, texto, pilha}: Nil{}
    case C.Pronto{v}: Nil{}
    case C.Invalido{}: Nil{}
    case C.Acima{}: Nil{}

def quadros_codec(bs: List<&2, U32>, +m: C.Maquina, +corpo: B.Numero64, +teto: B.Numero64, +pos: Nat) -> List<&2, Q.Quadro>:
  match bs:
    case Nil{}: Nil{}
    case Con{+b, t}: Q.concatenar(quadro_passo(m, b, C.diminuir64(corpo), C.diminuir64(teto), pos), quadros_codec(t, C.passo(m, b, C.diminuir64(corpo), C.diminuir64(teto)), C.diminuir64(corpo), C.diminuir64(teto), Succ{pos}))

def decodificacao_admitida(ok: Bool, +bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64) -> List<&2, Q.Quadro>:
  match ok:
    case False{}: Nil{}
    case True{}: Q.concatenar(quadros_codec(bs, C.Tag{C.Raiz{}}, corpo, teto, 0n),
      [Q.Decodificada{bs, R.opcional(C.decodificar(bs, teto))}])

def decodificacao_medida(q: Maybe<&2, B.Numero64>, +bs: List<&2, U32>, +teto: B.Numero64) -> List<&2, Q.Quadro>:
  match q:
    case None{}: Nil{}
    case Some{+corpo}: decodificacao_admitida(C.menor_igual64(corpo, teto) && B.octetos_validos(bs), bs, corpo, teto)

def expandir(q: Primitiva) -> List<&2, Q.Quadro>:
  match q:
    case Prefixo{n, p}: Q.primeiros(n, expandir(p))
    case Codificar{+v}: [Q.Codificada{v, P.codificar(v)}]
    case Decodificar{+bs, teto}: decodificacao_medida(B.nat64(B.comprimento(bs)), bs, teto)
    case Guardar{e, +s}: guardar_bytes(P.codificar(D.estado_valor(s)), e, s)
    case Ler{antes, cap, recebido, declarado}: [Q.Lida{antes, recebido, declarado}]

def expandir_primitivas(xs: List<&2, Primitiva>) -> List<&2, Q.Quadro>:
  match xs:
    case Nil{}: Nil{}
    case Con{h, t}: Q.concatenar(expandir(h), expandir_primitivas(t))

# Impede que o subtraco consiga fazer um store ou concluir a chamada.
def interna(q: Q.Quadro) -> Bool:
  match q:
    case Q.Codificada{v, bs}: True{}
    case Q.Decodificada{bs, v}: True{}
    case Q.Guardada{s, bs, abstr}: True{}
    case Q.Conferida{p, n}: True{}
    case Q.Construida{p, n}: True{}
    case Q.Lida{antes, n, declarado}: True{}
    case _: False{}

def Internas(qs: List<&2, Q.Quadro>) -> Type:
  match qs:
    case Nil{}: Unit
    case Con{h, t}: L.E<{interna(h) == True{} : Bool}, Internas(t)>

law concatenar_internas:
  for xs: List<&2, Q.Quadro>
  for -ys: List<&2, Q.Quadro>
  for a: Internas(xs)
  for b: Internas(ys)
  Internas(Q.concatenar(xs, ys))
def concatenar_internas(xs, ys, a, b):
  match xs a:
    case Nil{} _: b
    case Con{h, t} L.Ambos{cabeca, cauda}:
      L.Ambos{cabeca, concatenar_internas(t, ys, cauda, b)}

law construir_internas:
  for c: C.Conferencia
  for -pos: Nat
  for -n: Nat
  Internas(construir(c, pos, n))
def construir_internas(c, pos, n):
  match c:
    case C.Cabe{}: L.Ambos{{==}, L.Ambos{{==}, Unit{}}}
    case C.Curto{}: Unit{}
    case C.Grande{}: Unit{}

def guardar_abstracao_internas(q: Maybe<&2, D.Estado>, -s: D.Estado, -bs: List<&2, U32>) ->
  Internas(guardar_abstracao(q, s, bs)):
  match q:
    case None{}: Unit{}
    case Some{a}: L.Ambos{{==}, Unit{}}

def guardar_bytes_internas(q: Maybe<&2, List<&2, U32>>, +e: D.Esquema, +s: D.Estado) ->
  Internas(guardar_bytes(q, e, s)):
  match q:
    case None{}: Unit{}
    case Some{bs}: guardar_abstracao_internas(E.decodificar(D.estado_valor(s), e), s, bs)

def abrir_campo_internas(c: C.Conferencia, pronto: Bool, -pos: Nat, -n: Nat) ->
  Internas(abrir_campo(c, pronto, pos, n)):
  match c pronto:
    case C.Cabe{} True{}: construir_internas(C.Cabe{}, pos, n)
    case C.Cabe{} False{}: L.Ambos{{==}, Unit{}}
    case C.Curto{} _: Unit{}
    case C.Grande{} _: Unit{}

def quadro_campo_internas(+pos: Nat, +f: C.Finalidade, +alto: U32, +baixo: U32,
  +pilha: C.Pilha, +corpo: B.Numero64, +teto: B.Numero64) ->
  Internas(quadro_campo(pos, f, alto, baixo, pilha, corpo, teto)):
  abrir_campo_internas(conferencia(f, alto, baixo, pilha, corpo, teto),
    abrir_nome_valido(f, alto, baixo), pos, quantidade(alto, baixo))

def quadro_tag_internas(tag: Nat, -pos: Nat) -> Internas(quadro_tag(tag, pos)):
  match tag:
    case 0n: construir_internas(C.Cabe{}, pos, 1n)
    case 1n: construir_internas(C.Cabe{}, pos, 1n)
    case 2n: construir_internas(C.Cabe{}, pos, 1n)
    case 3n+k: Unit{}

def quadro_palavra_internas(f: C.Finalidade, +alto: U32, +baixo: U32, +pilha: C.Pilha,
  +corpo: B.Numero64, +teto: B.Numero64, +pos: Nat) ->
  Internas(quadro_palavra(f, alto, baixo, pilha, corpo, teto, pos)):
  match f:
    case C.Inteiro{}: construir_internas(C.Cabe{}, pos, 8n)
    case C.Texto{}: quadro_campo_internas(pos, C.Texto{}, alto, baixo, pilha, corpo, teto)
    case C.NomeTexto{}: quadro_campo_internas(pos, C.NomeTexto{}, alto, baixo, pilha, corpo, teto)
    case C.ContaLista{}: quadro_campo_internas(pos, C.ContaLista{}, alto, baixo, pilha, corpo, teto)
    case C.ContaRegistro{}: quadro_campo_internas(pos, C.ContaRegistro{}, alto, baixo, pilha, corpo, teto)

def quadro_passo_internas(m: C.Maquina, +b: U32, +corpo: B.Numero64, +teto: B.Numero64, +pos: Nat) ->
  Internas(quadro_passo(m, b, corpo, teto, pos)):
  match m:
    case C.Tag{pilha}: quadro_tag_internas(U32.to_nat(b), pos)
    case C.Palavra{f, 0n, alto, +baixo, pilha}:
      quadro_palavra_internas(f, (alto * 256 + U32.shrn(baixo, 24n) : U32), (baixo * 256 + b : U32), pilha, corpo, teto, pos)
    case C.TagNome{pilha}: Unit{}
    case C.Palavra{f, 1n+n, alto, baixo, pilha}: Unit{}
    case C.Conteudo{nome, ultimo, q, u, texto, pilha}: Unit{}
    case C.Pronto{v}: Unit{}
    case C.Invalido{}: Unit{}
    case C.Acima{}: Unit{}

def quadros_codec_internas(bs: List<&2, U32>, +m: C.Maquina, +corpo: B.Numero64,
  +teto: B.Numero64, +pos: Nat) -> Internas(quadros_codec(bs, m, corpo, teto, pos)):
  match bs:
    case Nil{}: Unit{}
    case Con{+b, +t}:
      concatenar_internas(quadro_passo(m, b, C.diminuir64(corpo), C.diminuir64(teto), pos),
        quadros_codec(t, C.passo(m, b, C.diminuir64(corpo), C.diminuir64(teto)), C.diminuir64(corpo), C.diminuir64(teto), Succ{pos}),
        quadro_passo_internas(m, b, C.diminuir64(corpo), C.diminuir64(teto), pos),
        quadros_codec_internas(t, C.passo(m, b, C.diminuir64(corpo), C.diminuir64(teto)), C.diminuir64(corpo), C.diminuir64(teto), Succ{pos}))

def decodificacao_admitida_internas(ok: Bool, +bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64) ->
  Internas(decodificacao_admitida(ok, bs, corpo, teto)):
  match ok:
    case False{}: Unit{}
    case True{}: concatenar_internas(quadros_codec(bs, C.Tag{C.Raiz{}}, corpo, teto, 0n),
      [Q.Decodificada{bs, R.opcional(C.decodificar(bs, teto))}],
      quadros_codec_internas(bs, C.Tag{C.Raiz{}}, corpo, teto, 0n), L.Ambos{{==}, Unit{}})

def decodificacao_medida_internas(q: Maybe<&2, B.Numero64>, +bs: List<&2, U32>, +teto: B.Numero64) ->
  Internas(decodificacao_medida(q, bs, teto)):
  match q:
    case None{}: Unit{}
    case Some{+corpo}: decodificacao_admitida_internas(C.menor_igual64(corpo, teto) && B.octetos_validos(bs), bs, corpo, teto)

def primeiros_internos(n: Nat, qs: List<&2, Q.Quadro>, internas: Internas(qs)) -> Internas(Q.primeiros(n, qs)):
  match n qs:
    case 0n _: Unit{}
    case 1n+k Nil{}: Unit{}
    case 1n+k Con{h, t}:
      match internas:
        case L.Ambos{cabeca, cauda}: L.Ambos{cabeca, primeiros_internos(k, t, cauda)}

law expandir_internas:
  for q: Primitiva
  Internas(expandir(q))
def expandir_internas(q):
  match q:
    case Prefixo{n, +p}: primeiros_internos(n, expandir(p), expandir_internas(p))
    case Codificar{v}: L.Ambos{{==}, Unit{}}
    case Decodificar{+bs, +teto}: decodificacao_medida_internas(B.nat64(B.comprimento(bs)), bs, teto)
    case Guardar{e, +s}: guardar_bytes_internas(P.codificar(D.estado_valor(s)), e, s)
    case Ler{antes, cap, recebido, declarado}: L.Ambos{{==}, Unit{}}

law primitivas_so_geram_internas:
  for +xs: List<&2, Primitiva>
  Internas(expandir_primitivas(xs))
def primitivas_so_geram_internas(xs):
  match xs:
    case Nil{}: Unit{}
    case Con{+h, t}:
      concatenar_internas(expandir(h), expandir_primitivas(t), expandir_internas(h), primitivas_so_geram_internas(t))
