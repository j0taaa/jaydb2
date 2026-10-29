# Direcao inversa: oito octetos validos, seus words acumulados e bytes exatos.
import Base
import ../contrato/Bytes.bend as B
import ../src/Codec.bend as C
import ./CodecPercurso.bend as R
import ./CodecPalavrasWord.bend as W
import ./CodecPalavrasBE64.bend as E
import ./Fundamentos.bend as F

def byte_word(x: U32) -> Word(8n):
  W.ajustar(8n, 32n, E.bits(x))

def montar(a: U32, b: U32, c: U32, d: U32) -> U32:
  E.quatro(byte_word(a), byte_word(b), byte_word(c), byte_word(d))

law octeto_valido_reconstituido:
  for +x: U32
  for valido: {U32.is_le(x, 255) == True{} : Bool}
  {x == E.octeto(byte_word(x)) : U32}
def octeto_valido_reconstituido(x, valido):
  match x:
    case U32{w}:
      Equal.cong(Word(32n), U32, z => U32{z}, w,
        W.juntar(8n, 24n, W.ajustar(8n, 32n, w), Word.zero(24n)), W.limite_bits_baixos(8n, 24n, w, valido))

law recodificar_blocos:
  for +a: Word(8n)
  for +b: Word(8n)
  for +c: Word(8n)
  for +d: Word(8n)
  for +e: Word(8n)
  for +f: Word(8n)
  for +g: Word(8n)
  for +h: Word(8n)
  {B.be64(E.quatro(a, b, c, d), E.quatro(e, f, g, h)) ==
    [E.octeto(a), E.octeto(b), E.octeto(c), E.octeto(d), E.octeto(e), E.octeto(f), E.octeto(g), E.octeto(h)] : List<&2, U32>}
def recodificar_blocos(a, b, c, d, e, f, g, h):
  %Equal.sym(List<&2, U32>, B.be32(E.quatro(a, b, c, d)), [E.octeto(a), E.octeto(b), E.octeto(c), E.octeto(d)], E.be32_quatro(a, b, c, d)) :
    {B.concatenar(_, B.be32(E.quatro(e, f, g, h))) == [E.octeto(a), E.octeto(b), E.octeto(c), E.octeto(d), E.octeto(e), E.octeto(f), E.octeto(g), E.octeto(h)] : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.be32(E.quatro(e, f, g, h)), [E.octeto(e), E.octeto(f), E.octeto(g), E.octeto(h)], E.be32_quatro(e, f, g, h)) :
    {B.concatenar([E.octeto(a), E.octeto(b), E.octeto(c), E.octeto(d)], _) == [E.octeto(a), E.octeto(b), E.octeto(c), E.octeto(d), E.octeto(e), E.octeto(f), E.octeto(g), E.octeto(h)] : List<&2, U32>}
  {==}

law recodificar_octetos_separados:
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +e: U32
  for +f: U32
  for +g: U32
  for +h: U32
  for va: {U32.is_le(a, 255) == True{} : Bool}
  for vb: {U32.is_le(b, 255) == True{} : Bool}
  for vc: {U32.is_le(c, 255) == True{} : Bool}
  for vd: {U32.is_le(d, 255) == True{} : Bool}
  for ve: {U32.is_le(e, 255) == True{} : Bool}
  for vf: {U32.is_le(f, 255) == True{} : Bool}
  for vg: {U32.is_le(g, 255) == True{} : Bool}
  for vh: {U32.is_le(h, 255) == True{} : Bool}
  {B.be64(montar(a, b, c, d), montar(e, f, g, h)) == [a, b, c, d, e, f, g, h] : List<&2, U32>}
def recodificar_octetos_separados(a, b, c, d, e, f, g, h, va, vb, vc, vd, ve, vf, vg, vh):
  %Equal.sym(U32, a, E.octeto(byte_word(a)), octeto_valido_reconstituido(a, va)) :
    {B.be64(montar(a, b, c, d), montar(e, f, g, h)) == [_, b, c, d, e, f, g, h] : List<&2, U32>}
  %Equal.sym(U32, b, E.octeto(byte_word(b)), octeto_valido_reconstituido(b, vb)) :
    {B.be64(montar(a, b, c, d), montar(e, f, g, h)) == [E.octeto(byte_word(a)), _, c, d, e, f, g, h] : List<&2, U32>}
  %Equal.sym(U32, c, E.octeto(byte_word(c)), octeto_valido_reconstituido(c, vc)) :
    {B.be64(montar(a, b, c, d), montar(e, f, g, h)) == [E.octeto(byte_word(a)), E.octeto(byte_word(b)), _, d, e, f, g, h] : List<&2, U32>}
  %Equal.sym(U32, d, E.octeto(byte_word(d)), octeto_valido_reconstituido(d, vd)) :
    {B.be64(montar(a, b, c, d), montar(e, f, g, h)) == [E.octeto(byte_word(a)), E.octeto(byte_word(b)), E.octeto(byte_word(c)), _, e, f, g, h] : List<&2, U32>}
  %Equal.sym(U32, e, E.octeto(byte_word(e)), octeto_valido_reconstituido(e, ve)) :
    {B.be64(montar(a, b, c, d), montar(e, f, g, h)) == [E.octeto(byte_word(a)), E.octeto(byte_word(b)), E.octeto(byte_word(c)), E.octeto(byte_word(d)), _, f, g, h] : List<&2, U32>}
  %Equal.sym(U32, f, E.octeto(byte_word(f)), octeto_valido_reconstituido(f, vf)) :
    {B.be64(montar(a, b, c, d), montar(e, f, g, h)) == [E.octeto(byte_word(a)), E.octeto(byte_word(b)), E.octeto(byte_word(c)), E.octeto(byte_word(d)), E.octeto(byte_word(e)), _, g, h] : List<&2, U32>}
  %Equal.sym(U32, g, E.octeto(byte_word(g)), octeto_valido_reconstituido(g, vg)) :
    {B.be64(montar(a, b, c, d), montar(e, f, g, h)) == [E.octeto(byte_word(a)), E.octeto(byte_word(b)), E.octeto(byte_word(c)), E.octeto(byte_word(d)), E.octeto(byte_word(e)), E.octeto(byte_word(f)), _, h] : List<&2, U32>}
  %Equal.sym(U32, h, E.octeto(byte_word(h)), octeto_valido_reconstituido(h, vh)) :
    {B.be64(montar(a, b, c, d), montar(e, f, g, h)) == [E.octeto(byte_word(a)), E.octeto(byte_word(b)), E.octeto(byte_word(c)), E.octeto(byte_word(d)), E.octeto(byte_word(e)), E.octeto(byte_word(f)), E.octeto(byte_word(g)), _] : List<&2, U32>}
  recodificar_blocos(byte_word(a), byte_word(b), byte_word(c), byte_word(d), byte_word(e), byte_word(f), byte_word(g), byte_word(h))

law be64_recodifica_oito_octetos_validos:
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +e: U32
  for +f: U32
  for +g: U32
  for +h: U32
  for +validos: {B.octetos_validos([a, b, c, d, e, f, g, h]) == True{} : Bool}
  {B.be64(montar(a, b, c, d), montar(e, f, g, h)) == [a, b, c, d, e, f, g, h] : List<&2, U32>}
def be64_recodifica_oito_octetos_validos(a, b, c, d, e, f, g, h, validos):
  va = F.e_booleano_esquerda(U32.is_le(a, 255), B.octetos_validos([b, c, d, e, f, g, h]), validos)
  +t1 = F.e_booleano_direita(U32.is_le(a, 255), B.octetos_validos([b, c, d, e, f, g, h]), validos)
  vb = F.e_booleano_esquerda(U32.is_le(b, 255), B.octetos_validos([c, d, e, f, g, h]), t1)
  +t2 = F.e_booleano_direita(U32.is_le(b, 255), B.octetos_validos([c, d, e, f, g, h]), t1)
  vc = F.e_booleano_esquerda(U32.is_le(c, 255), B.octetos_validos([d, e, f, g, h]), t2)
  +t3 = F.e_booleano_direita(U32.is_le(c, 255), B.octetos_validos([d, e, f, g, h]), t2)
  vd = F.e_booleano_esquerda(U32.is_le(d, 255), B.octetos_validos([e, f, g, h]), t3)
  +t4 = F.e_booleano_direita(U32.is_le(d, 255), B.octetos_validos([e, f, g, h]), t3)
  ve = F.e_booleano_esquerda(U32.is_le(e, 255), B.octetos_validos([f, g, h]), t4)
  +t5 = F.e_booleano_direita(U32.is_le(e, 255), B.octetos_validos([f, g, h]), t4)
  vf = F.e_booleano_esquerda(U32.is_le(f, 255), B.octetos_validos([g, h]), t5)
  +t6 = F.e_booleano_direita(U32.is_le(f, 255), B.octetos_validos([g, h]), t5)
  vg = F.e_booleano_esquerda(U32.is_le(g, 255), B.octetos_validos([h]), t6)
  +t7 = F.e_booleano_direita(U32.is_le(g, 255), B.octetos_validos([h]), t6)
  vh = F.e_booleano_esquerda(U32.is_le(h, 255), B.octetos_validos([]), t7)
  recodificar_octetos_separados(a, b, c, d, e, f, g, h, va, vb, vc, vd, ve, vf, vg, vh)

# Aritmetica IDENTICA a src/Codec.ler_palavra, antes de concluir a finalidade.
def acumular_octeto(n: B.Numero64, b: U32) -> B.Numero64:
  B.Numero64{alto, +baixo} = n
  B.Numero64{(alto * 256 + U32.shrn(baixo, 24n) : U32), (baixo * 256 + b : U32)}

def acumular(bs: List<&2, U32>, n: B.Numero64) -> B.Numero64:
  match bs:
    case Nil{}:
      n
    case Con{b, t}:
      acumular(t, acumular_octeto(n, b))

def recodificar(n: B.Numero64) -> List<&2, U32>:
  B.Numero64{alto, baixo} = n
  B.be64(alto, baixo)

def concluir_acumulacao(n: Nat, f: C.Finalidade, words: B.Numero64, pilha: C.Pilha, corpo: B.Numero64, teto: B.Numero64) -> C.Maquina:
  B.Numero64{alto, baixo} = words
  E.seguinte(n, f, alto, baixo, pilha, corpo, teto)

law acumulador_e_transicao_real:
  for n: Nat
  for +f: C.Finalidade
  for +alto: U32
  for +baixo: U32
  for +b: U32
  for +pilha: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  {C.ler_palavra(n, f, alto, baixo, b, pilha, corpo, teto) ==
    concluir_acumulacao(n, f, acumular_octeto(B.Numero64{alto, baixo}, b), pilha, corpo, teto) : C.Maquina}
def acumulador_e_transicao_real(n, f, alto, baixo, b, pilha, corpo, teto):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

law acumular_blocos:
  for +a: Word(8n)
  for +b: Word(8n)
  for +c: Word(8n)
  for +d: Word(8n)
  for +e: Word(8n)
  for +g: Word(8n)
  for +h: Word(8n)
  for +i: Word(8n)
  for +j: Word(8n)
  {acumular_octeto(B.Numero64{E.quatro(a, b, c, d), E.quatro(e, g, h, i)}, E.octeto(j)) ==
    B.Numero64{E.quatro(b, c, d, e), E.quatro(g, h, i, j)} : B.Numero64}
def acumular_blocos(a, b, c, d, e, g, h, i, j):
  %Equal.sym(U32, U32.shrn(E.quatro(e, g, h, i), 24n), E.octeto(e), E.topo_quatro(e, g, h, i)) :
    {B.Numero64{(E.quatro(a, b, c, d) * 256 + _ : U32), (E.quatro(e, g, h, i) * 256 + E.octeto(j) : U32)} ==
      B.Numero64{E.quatro(b, c, d, e), E.quatro(g, h, i, j)} : B.Numero64}
  %Equal.sym(U32, (E.quatro(a, b, c, d) * 256 + E.octeto(e) : U32), E.quatro(b, c, d, e), E.acrescentar_quatro(a, b, c, d, e)) :
    {B.Numero64{_, (E.quatro(e, g, h, i) * 256 + E.octeto(j) : U32)} ==
      B.Numero64{E.quatro(b, c, d, e), E.quatro(g, h, i, j)} : B.Numero64}
  %Equal.sym(U32, (E.quatro(e, g, h, i) * 256 + E.octeto(j) : U32), E.quatro(g, h, i, j), E.acrescentar_quatro(e, g, h, i, j)) :
    {B.Numero64{E.quatro(b, c, d, e), _} == B.Numero64{E.quatro(b, c, d, e), E.quatro(g, h, i, j)} : B.Numero64}
  {==}

law acumular_oito_blocos:
  for +a: Word(8n)
  for +b: Word(8n)
  for +c: Word(8n)
  for +d: Word(8n)
  for +e: Word(8n)
  for +f: Word(8n)
  for +g: Word(8n)
  for +h: Word(8n)
  {acumular([E.octeto(a), E.octeto(b), E.octeto(c), E.octeto(d), E.octeto(e), E.octeto(f), E.octeto(g), E.octeto(h)], B.Numero64{0, 0}) ==
    B.Numero64{E.quatro(a, b, c, d), E.quatro(e, f, g, h)} : B.Numero64}
def acumular_oito_blocos(a, b, c, d, e, f, g, h):
  %Equal.sym(B.Numero64, acumular_octeto(B.Numero64{E.quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), E.quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n))}, E.octeto(a)), B.Numero64{E.quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), E.quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), a)},
    acumular_blocos(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), a)) :
    {acumular([E.octeto(b), E.octeto(c), E.octeto(d), E.octeto(e), E.octeto(f), E.octeto(g), E.octeto(h)], _) == B.Numero64{E.quatro(a, b, c, d), E.quatro(e, f, g, h)} : B.Numero64}
  %Equal.sym(B.Numero64, acumular_octeto(B.Numero64{E.quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), E.quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), a)}, E.octeto(b)), B.Numero64{E.quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), E.quatro(Word.zero(8n), Word.zero(8n), a, b)},
    acumular_blocos(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), a, b)) :
    {acumular([E.octeto(c), E.octeto(d), E.octeto(e), E.octeto(f), E.octeto(g), E.octeto(h)], _) == B.Numero64{E.quatro(a, b, c, d), E.quatro(e, f, g, h)} : B.Numero64}
  %Equal.sym(B.Numero64, acumular_octeto(B.Numero64{E.quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), E.quatro(Word.zero(8n), Word.zero(8n), a, b)}, E.octeto(c)), B.Numero64{E.quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), E.quatro(Word.zero(8n), a, b, c)},
    acumular_blocos(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), a, b, c)) :
    {acumular([E.octeto(d), E.octeto(e), E.octeto(f), E.octeto(g), E.octeto(h)], _) == B.Numero64{E.quatro(a, b, c, d), E.quatro(e, f, g, h)} : B.Numero64}
  %Equal.sym(B.Numero64, acumular_octeto(B.Numero64{E.quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), E.quatro(Word.zero(8n), a, b, c)}, E.octeto(d)), B.Numero64{E.quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), E.quatro(a, b, c, d)},
    acumular_blocos(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), a, b, c, d)) :
    {acumular([E.octeto(e), E.octeto(f), E.octeto(g), E.octeto(h)], _) == B.Numero64{E.quatro(a, b, c, d), E.quatro(e, f, g, h)} : B.Numero64}
  %Equal.sym(B.Numero64, acumular_octeto(B.Numero64{E.quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), E.quatro(a, b, c, d)}, E.octeto(e)), B.Numero64{E.quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), a), E.quatro(b, c, d, e)},
    acumular_blocos(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), a, b, c, d, e)) :
    {acumular([E.octeto(f), E.octeto(g), E.octeto(h)], _) == B.Numero64{E.quatro(a, b, c, d), E.quatro(e, f, g, h)} : B.Numero64}
  %Equal.sym(B.Numero64, acumular_octeto(B.Numero64{E.quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), a), E.quatro(b, c, d, e)}, E.octeto(f)), B.Numero64{E.quatro(Word.zero(8n), Word.zero(8n), a, b), E.quatro(c, d, e, f)},
    acumular_blocos(Word.zero(8n), Word.zero(8n), Word.zero(8n), a, b, c, d, e, f)) :
    {acumular([E.octeto(g), E.octeto(h)], _) == B.Numero64{E.quatro(a, b, c, d), E.quatro(e, f, g, h)} : B.Numero64}
  %Equal.sym(B.Numero64, acumular_octeto(B.Numero64{E.quatro(Word.zero(8n), Word.zero(8n), a, b), E.quatro(c, d, e, f)}, E.octeto(g)), B.Numero64{E.quatro(Word.zero(8n), a, b, c), E.quatro(d, e, f, g)},
    acumular_blocos(Word.zero(8n), Word.zero(8n), a, b, c, d, e, f, g)) :
    {acumular([E.octeto(h)], _) == B.Numero64{E.quatro(a, b, c, d), E.quatro(e, f, g, h)} : B.Numero64}
  %Equal.sym(B.Numero64, acumular_octeto(B.Numero64{E.quatro(Word.zero(8n), a, b, c), E.quatro(d, e, f, g)}, E.octeto(h)), B.Numero64{E.quatro(a, b, c, d), E.quatro(e, f, g, h)},
    acumular_blocos(Word.zero(8n), a, b, c, d, e, f, g, h)) :
    {acumular([], _) == B.Numero64{E.quatro(a, b, c, d), E.quatro(e, f, g, h)} : B.Numero64}
  {==}

def representar_octetos(bs: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      Con{E.octeto(byte_word(b)), representar_octetos(t)}

law octetos_validos_representacao:
  for +bs: List<&2, U32>
  for +validos: {B.octetos_validos(bs) == True{} : Bool}
  {bs == representar_octetos(bs) : List<&2, U32>}
def octetos_validos_representacao(bs, validos):
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      Equal.trans(List<&2, U32>, Con{b, t}, Con{E.octeto(byte_word(b)), t}, Con{E.octeto(byte_word(b)), representar_octetos(t)},
        Equal.cong(U32, List<&2, U32>, x => Con{x, t}, b, E.octeto(byte_word(b)),
          octeto_valido_reconstituido(b, F.e_booleano_esquerda(U32.is_le(b, 255), B.octetos_validos(t), validos))),
        Equal.cong(List<&2, U32>, List<&2, U32>, xs => Con{E.octeto(byte_word(b)), xs}, t, representar_octetos(t),
          octetos_validos_representacao(t, F.e_booleano_direita(U32.is_le(b, 255), B.octetos_validos(t), validos))))

law acumular_oito_octetos_validos:
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +e: U32
  for +f: U32
  for +g: U32
  for +h: U32
  for +validos: {B.octetos_validos([a, b, c, d, e, f, g, h]) == True{} : Bool}
  {acumular([a, b, c, d, e, f, g, h], B.Numero64{0, 0}) == B.Numero64{montar(a, b, c, d), montar(e, f, g, h)} : B.Numero64}
def acumular_oito_octetos_validos(a, b, c, d, e, f, g, h, validos):
  Equal.trans(B.Numero64, acumular([a, b, c, d, e, f, g, h], B.Numero64{0, 0}), acumular(representar_octetos([a, b, c, d, e, f, g, h]), B.Numero64{0, 0}), B.Numero64{montar(a, b, c, d), montar(e, f, g, h)},
    Equal.cong(List<&2, U32>, B.Numero64, ys => acumular(ys, B.Numero64{0, 0}), [a, b, c, d, e, f, g, h], representar_octetos([a, b, c, d, e, f, g, h]), octetos_validos_representacao([a, b, c, d, e, f, g, h], validos)),
    acumular_oito_blocos(byte_word(a), byte_word(b), byte_word(c), byte_word(d), byte_word(e), byte_word(f), byte_word(g), byte_word(h)))

# Aqui os words sao calculados, nao supostos numa premissa de canonicidade.
law be64_inverte_acumulacao_de_oito_octetos_validos:
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +e: U32
  for +f: U32
  for +g: U32
  for +h: U32
  for +validos: {B.octetos_validos([a, b, c, d, e, f, g, h]) == True{} : Bool}
  {recodificar(acumular([a, b, c, d, e, f, g, h], B.Numero64{0, 0})) == [a, b, c, d, e, f, g, h] : List<&2, U32>}
def be64_inverte_acumulacao_de_oito_octetos_validos(a, b, c, d, e, f, g, h, validos):
  Equal.trans(List<&2, U32>, recodificar(acumular([a, b, c, d, e, f, g, h], B.Numero64{0, 0})), recodificar(B.Numero64{montar(a, b, c, d), montar(e, f, g, h)}), [a, b, c, d, e, f, g, h],
    Equal.cong(B.Numero64, List<&2, U32>, n => recodificar(n), acumular([a, b, c, d, e, f, g, h], B.Numero64{0, 0}), B.Numero64{montar(a, b, c, d), montar(e, f, g, h)},
      acumular_oito_octetos_validos(a, b, c, d, e, f, g, h, validos)),
    be64_recodifica_oito_octetos_validos(a, b, c, d, e, f, g, h, validos))

law oito_octetos_validos_concluem_palavra:
  for +finalidade: C.Finalidade
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +e: U32
  for +f: U32
  for +g: U32
  for +h: U32
  for +pilha: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +validos: {B.octetos_validos([a, b, c, d, e, f, g, h]) == True{} : Bool}
  {R.executar([a, b, c, d, e, f, g, h], R.Quadro{corpo, teto, C.Palavra{finalidade, 7n, 0, 0, pilha}}) == R.Quadro{E.diminuir(8n, corpo), E.diminuir(8n, teto), C.concluir_palavra(finalidade, montar(a, b, c, d), montar(e, f, g, h), pilha, E.diminuir(8n, corpo), E.diminuir(8n, teto))} : R.Quadro}
def oito_octetos_validos_concluem_palavra(finalidade, a, b, c, d, e, f, g, h, pilha, corpo, teto, validos):
  Equal.trans(R.Quadro, R.executar([a, b, c, d, e, f, g, h], R.Quadro{corpo, teto, C.Palavra{finalidade, 7n, 0, 0, pilha}}), R.executar(representar_octetos([a, b, c, d, e, f, g, h]), R.Quadro{corpo, teto, C.Palavra{finalidade, 7n, 0, 0, pilha}}), R.Quadro{E.diminuir(8n, corpo), E.diminuir(8n, teto), C.concluir_palavra(finalidade, montar(a, b, c, d), montar(e, f, g, h), pilha, E.diminuir(8n, corpo), E.diminuir(8n, teto))},
    Equal.cong(List<&2, U32>, R.Quadro, ys => R.executar(ys, R.Quadro{corpo, teto, C.Palavra{finalidade, 7n, 0, 0, pilha}}), [a, b, c, d, e, f, g, h], representar_octetos([a, b, c, d, e, f, g, h]), octetos_validos_representacao([a, b, c, d, e, f, g, h], validos)),
    E.oito_octetos_concluem_palavra(finalidade, byte_word(a), byte_word(b), byte_word(c), byte_word(d), byte_word(e), byte_word(f), byte_word(g), byte_word(h), pilha, corpo, teto))

law oito_octetos_validos_concluem_acumulacao_real:
  for +finalidade: C.Finalidade
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +e: U32
  for +f: U32
  for +g: U32
  for +h: U32
  for +pilha: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +validos: {B.octetos_validos([a, b, c, d, e, f, g, h]) == True{} : Bool}
  {R.executar([a, b, c, d, e, f, g, h], R.Quadro{corpo, teto, C.Palavra{finalidade, 7n, 0, 0, pilha}}) == R.Quadro{E.diminuir(8n, corpo), E.diminuir(8n, teto), concluir_acumulacao(0n, finalidade, acumular([a, b, c, d, e, f, g, h], B.Numero64{0, 0}), pilha, E.diminuir(8n, corpo), E.diminuir(8n, teto))} : R.Quadro}
def oito_octetos_validos_concluem_acumulacao_real(finalidade, a, b, c, d, e, f, g, h, pilha, corpo, teto, validos):
  %Equal.sym(B.Numero64, acumular([a, b, c, d, e, f, g, h], B.Numero64{0, 0}), B.Numero64{montar(a, b, c, d), montar(e, f, g, h)},
    acumular_oito_octetos_validos(a, b, c, d, e, f, g, h, validos)) :
    {R.executar([a, b, c, d, e, f, g, h], R.Quadro{corpo, teto, C.Palavra{finalidade, 7n, 0, 0, pilha}}) == R.Quadro{E.diminuir(8n, corpo), E.diminuir(8n, teto), concluir_acumulacao(0n, finalidade, _, pilha, E.diminuir(8n, corpo), E.diminuir(8n, teto))} : R.Quadro}
  oito_octetos_validos_concluem_palavra(finalidade, a, b, c, d, e, f, g, h, pilha, corpo, teto, validos)
