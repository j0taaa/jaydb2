# Inversao geral de BE64 do contrato pelas transicoes reais do Codec.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../src/Codec.bend as C
import ./CodecPalavrasWord.bend as W
import ./CodecPercurso.bend as R

def octeto(w: Word(8n)) -> U32:
  U32{W.juntar(8n, 24n, w, Word.zero(24n))}

# Os argumentos seguem a ordem big endian; Word guarda primeiro o bit baixo.
def quatro(a: Word(8n), b: Word(8n), c: Word(8n), d: Word(8n)) -> U32:
  U32{W.juntar(8n, 24n, d, W.juntar(8n, 16n, c, W.juntar(8n, 8n, b, a)))}

def bits(x: U32) -> Word(32n):
  U32{w} = x
  w

law acrescentar_octeto:
  for +x: U32
  for +b: Word(8n)
  {(x * 256 + octeto(b) : U32) ==
    U32{W.juntar(8n, 24n, b, W.ajustar(24n, 32n, bits(x)))} : U32}
def acrescentar_octeto(x, b):
  match x:
    case U32{w}:
      %Equal.sym(Word(32n), Word.mul(32n, w, bits(256)),
        W.zeros_baixos(8n, 24n, W.ajustar(24n, 32n, w)),
        W.multiplicar_potencia_dois(8n, 24n, 32n, w)) :
        {U32{Word.add(32n, _, W.juntar(8n, 24n, b, Word.zero(24n)))} ==
          U32{W.juntar(8n, 24n, b, W.ajustar(24n, 32n, w))} : U32}
      Equal.cong(Word(32n), U32, z => U32{z},
        Word.add(32n, W.zeros_baixos(8n, 24n, W.ajustar(24n, 32n, w)), W.juntar(8n, 24n, b, Word.zero(24n))),
        W.juntar(8n, 24n, b, W.ajustar(24n, 32n, w)), W.soma_blocos_separados(8n, 24n, b, W.ajustar(24n, 32n, w)))


law mascara_octeto:
  for +x: U32
  {U32.and(x, 255) == octeto(W.ajustar(8n, 32n, bits(x))) : U32}
def mascara_octeto(x):
  match x:
    case U32{w}:
      Equal.cong(Word(32n), U32, z => U32{z},
        Word.and(32n, w, W.juntar(8n, 24n, W.uns(8n), Word.zero(24n))),
        W.juntar(8n, 24n, W.ajustar(8n, 32n, w), Word.zero(24n)), W.mascara_baixa(8n, 24n, w))

law acrescentar_quatro:
  for +a: Word(8n)
  for +b: Word(8n)
  for +c: Word(8n)
  for +d: Word(8n)
  for +e: Word(8n)
  {(quatro(a, b, c, d) * 256 + octeto(e) : U32) == quatro(b, c, d, e) : U32}
def acrescentar_quatro(a, b, c, d, e):
  match a b c d:
    case WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WNil{}}}}}}}}} WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}} WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}} WCon{d0, WCon{d1, WCon{d2, WCon{d3, WCon{d4, WCon{d5, WCon{d6, WCon{d7, WNil{}}}}}}}}}:
      %Equal.sym(U32, (quatro(a, b, c, d) * 256 + octeto(e) : U32),
        U32{W.juntar(8n, 24n, e, W.ajustar(24n, 32n, bits(quatro(a, b, c, d))))},
        acrescentar_octeto(quatro(a, b, c, d), e)) : {_ == quatro(b, c, d, e) : U32}
      {==}

law topo_quatro:
  for +a: Word(8n)
  for b: Word(8n)
  for c: Word(8n)
  for d: Word(8n)
  {U32.shrn(quatro(a, b, c, d), 24n) == octeto(a) : U32}
def topo_quatro(a, b, c, d):
  match a b c d:
    case WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WNil{}}}}}}}}} WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}} WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}} WCon{d0, WCon{d1, WCon{d2, WCon{d3, WCon{d4, WCon{d5, WCon{d6, WCon{d7, WNil{}}}}}}}}}:
      {==}

law be32_quatro:
  for +a: Word(8n)
  for +b: Word(8n)
  for +c: Word(8n)
  for +d: Word(8n)
  {B.be32(quatro(a, b, c, d)) == [octeto(a), octeto(b), octeto(c), octeto(d)] : List<&2, U32>}
def be32_quatro(a, b, c, d):
  match a b c d:
    case WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WNil{}}}}}}}}} WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}} WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}} WCon{d0, WCon{d1, WCon{d2, WCon{d3, WCon{d4, WCon{d5, WCon{d6, WCon{d7, WNil{}}}}}}}}}:
      %Equal.sym(U32, U32.and(U32.shrn(quatro(a, b, c, d), 24n), 255), octeto(W.ajustar(8n, 32n, bits(U32.shrn(quatro(a, b, c, d), 24n)))), mascara_octeto(U32.shrn(quatro(a, b, c, d), 24n))) :
        {[_, U32.and(U32.shrn(quatro(a, b, c, d), 16n), 255), U32.and(U32.shrn(quatro(a, b, c, d), 8n), 255), U32.and(quatro(a, b, c, d), 255)] == [octeto(a), octeto(b), octeto(c), octeto(d)] : List<&2, U32>}
      %Equal.sym(U32, U32.and(U32.shrn(quatro(a, b, c, d), 16n), 255), octeto(W.ajustar(8n, 32n, bits(U32.shrn(quatro(a, b, c, d), 16n)))), mascara_octeto(U32.shrn(quatro(a, b, c, d), 16n))) :
        {[octeto(W.ajustar(8n, 32n, bits(U32.shrn(quatro(a, b, c, d), 24n)))), _, U32.and(U32.shrn(quatro(a, b, c, d), 8n), 255), U32.and(quatro(a, b, c, d), 255)] == [octeto(a), octeto(b), octeto(c), octeto(d)] : List<&2, U32>}
      %Equal.sym(U32, U32.and(U32.shrn(quatro(a, b, c, d), 8n), 255), octeto(W.ajustar(8n, 32n, bits(U32.shrn(quatro(a, b, c, d), 8n)))), mascara_octeto(U32.shrn(quatro(a, b, c, d), 8n))) :
        {[octeto(W.ajustar(8n, 32n, bits(U32.shrn(quatro(a, b, c, d), 24n)))), octeto(W.ajustar(8n, 32n, bits(U32.shrn(quatro(a, b, c, d), 16n)))), _, U32.and(quatro(a, b, c, d), 255)] == [octeto(a), octeto(b), octeto(c), octeto(d)] : List<&2, U32>}
      %Equal.sym(U32, U32.and(quatro(a, b, c, d), 255), octeto(W.ajustar(8n, 32n, bits(quatro(a, b, c, d)))), mascara_octeto(quatro(a, b, c, d))) :
        {[octeto(W.ajustar(8n, 32n, bits(U32.shrn(quatro(a, b, c, d), 24n)))), octeto(W.ajustar(8n, 32n, bits(U32.shrn(quatro(a, b, c, d), 16n)))), octeto(W.ajustar(8n, 32n, bits(U32.shrn(quatro(a, b, c, d), 8n)))), _] == [octeto(a), octeto(b), octeto(c), octeto(d)] : List<&2, U32>}
      {==}

def seguinte(n: Nat, f: C.Finalidade, alto: U32, baixo: U32, pilha: C.Pilha, corpo: B.Numero64, teto: B.Numero64) -> C.Maquina:
  match n:
    case 0n:
      C.concluir_palavra(f, alto, baixo, pilha, corpo, teto)
    case 1n+p:
      C.Palavra{f, p, alto, baixo, pilha}

law ler_palavra_blocos:
  for n: Nat
  for +f: C.Finalidade
  for +a: Word(8n)
  for +b: Word(8n)
  for +c: Word(8n)
  for +d: Word(8n)
  for +e: Word(8n)
  for +g: Word(8n)
  for +h: Word(8n)
  for +i: Word(8n)
  for +j: Word(8n)
  for +pilha: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  {C.ler_palavra(n, f, quatro(a, b, c, d), quatro(e, g, h, i), octeto(j), pilha, corpo, teto) ==
    seguinte(n, f, quatro(b, c, d, e), quatro(g, h, i, j), pilha, corpo, teto) : C.Maquina}
def ler_palavra_blocos(n, f, a, b, c, d, e, g, h, i, j, pilha, corpo, teto):
  match n:
    case 0n:
      %Equal.sym(U32, U32.shrn(quatro(e, g, h, i), 24n), octeto(e), topo_quatro(e, g, h, i)) :
        {C.concluir_palavra(f, (quatro(a, b, c, d) * 256 + _ : U32), (quatro(e, g, h, i) * 256 + octeto(j) : U32), pilha, corpo, teto) == C.concluir_palavra(f, quatro(b, c, d, e), quatro(g, h, i, j), pilha, corpo, teto) : C.Maquina}
      %Equal.sym(U32, (quatro(a, b, c, d) * 256 + octeto(e) : U32), quatro(b, c, d, e), acrescentar_quatro(a, b, c, d, e)) :
        {C.concluir_palavra(f, _, (quatro(e, g, h, i) * 256 + octeto(j) : U32), pilha, corpo, teto) == C.concluir_palavra(f, quatro(b, c, d, e), quatro(g, h, i, j), pilha, corpo, teto) : C.Maquina}
      %Equal.sym(U32, (quatro(e, g, h, i) * 256 + octeto(j) : U32), quatro(g, h, i, j), acrescentar_quatro(e, g, h, i, j)) :
        {C.concluir_palavra(f, quatro(b, c, d, e), _, pilha, corpo, teto) == C.concluir_palavra(f, quatro(b, c, d, e), quatro(g, h, i, j), pilha, corpo, teto) : C.Maquina}
      {==}
    case 1n+p:
      %Equal.sym(U32, U32.shrn(quatro(e, g, h, i), 24n), octeto(e), topo_quatro(e, g, h, i)) :
        {C.Palavra{f, p, (quatro(a, b, c, d) * 256 + _ : U32), (quatro(e, g, h, i) * 256 + octeto(j) : U32), pilha} == C.Palavra{f, p, quatro(b, c, d, e), quatro(g, h, i, j), pilha} : C.Maquina}
      %Equal.sym(U32, (quatro(a, b, c, d) * 256 + octeto(e) : U32), quatro(b, c, d, e), acrescentar_quatro(a, b, c, d, e)) :
        {C.Palavra{f, p, _, (quatro(e, g, h, i) * 256 + octeto(j) : U32), pilha} == C.Palavra{f, p, quatro(b, c, d, e), quatro(g, h, i, j), pilha} : C.Maquina}
      %Equal.sym(U32, (quatro(e, g, h, i) * 256 + octeto(j) : U32), quatro(g, h, i, j), acrescentar_quatro(e, g, h, i, j)) :
        {C.Palavra{f, p, quatro(b, c, d, e), _, pilha} == C.Palavra{f, p, quatro(b, c, d, e), quatro(g, h, i, j), pilha} : C.Maquina}
      {==}

law avancar_palavra_blocos:
  for +n: Nat
  for +f: C.Finalidade
  for +a: Word(8n)
  for +b: Word(8n)
  for +c: Word(8n)
  for +d: Word(8n)
  for +e: Word(8n)
  for +g: Word(8n)
  for +h: Word(8n)
  for +i: Word(8n)
  for +j: Word(8n)
  for +pilha: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  {R.avancar(R.Quadro{corpo, teto, C.Palavra{f, n, quatro(a, b, c, d), quatro(e, g, h, i), pilha}}, octeto(j)) ==
    R.Quadro{C.diminuir64(corpo), C.diminuir64(teto),
      seguinte(n, f, quatro(b, c, d, e), quatro(g, h, i, j), pilha, C.diminuir64(corpo), C.diminuir64(teto))} : R.Quadro}
def avancar_palavra_blocos(n, f, a, b, c, d, e, g, h, i, j, pilha, corpo, teto):
  Equal.cong(C.Maquina, R.Quadro, m => R.Quadro{C.diminuir64(corpo), C.diminuir64(teto), m},
    C.ler_palavra(n, f, quatro(a, b, c, d), quatro(e, g, h, i), octeto(j), pilha, C.diminuir64(corpo), C.diminuir64(teto)),
    seguinte(n, f, quatro(b, c, d, e), quatro(g, h, i, j), pilha, C.diminuir64(corpo), C.diminuir64(teto)),
    ler_palavra_blocos(n, f, a, b, c, d, e, g, h, i, j, pilha, C.diminuir64(corpo), C.diminuir64(teto)))

def diminuir(n: Nat, x: B.Numero64) -> B.Numero64:
  match n:
    case 0n:
      x
    case 1n+p:
      C.diminuir64(diminuir(p, x))

law oito_octetos_concluem_palavra:
  for +f: C.Finalidade
  for +a: Word(8n)
  for +b: Word(8n)
  for +c: Word(8n)
  for +d: Word(8n)
  for +e: Word(8n)
  for +fb: Word(8n)
  for +g: Word(8n)
  for +h: Word(8n)
  for +pilha: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  {R.executar([octeto(a), octeto(b), octeto(c), octeto(d), octeto(e), octeto(fb), octeto(g), octeto(h)],
    R.Quadro{corpo, teto, C.Palavra{f, 7n, 0, 0, pilha}}) ==
    R.Quadro{diminuir(8n, corpo), diminuir(8n, teto),
      C.concluir_palavra(f, quatro(a, b, c, d), quatro(e, fb, g, h), pilha, diminuir(8n, corpo), diminuir(8n, teto))} : R.Quadro}
def oito_octetos_concluem_palavra(f, a, b, c, d, e, fb, g, h, pilha, corpo, teto):
  %Equal.sym(R.Quadro, R.avancar(R.Quadro{diminuir(0n, corpo), diminuir(0n, teto), C.Palavra{f, 7n, quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), pilha}}, octeto(a)), R.Quadro{diminuir(1n, corpo), diminuir(1n, teto), C.Palavra{f, 6n, quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), a), pilha}},
    avancar_palavra_blocos(7n, f, Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), a, pilha, diminuir(0n, corpo), diminuir(0n, teto))) :
    {R.executar([octeto(b), octeto(c), octeto(d), octeto(e), octeto(fb), octeto(g), octeto(h)], _) == R.Quadro{diminuir(8n, corpo), diminuir(8n, teto), C.concluir_palavra(f, quatro(a, b, c, d), quatro(e, fb, g, h), pilha, diminuir(8n, corpo), diminuir(8n, teto))} : R.Quadro}
  %Equal.sym(R.Quadro, R.avancar(R.Quadro{diminuir(1n, corpo), diminuir(1n, teto), C.Palavra{f, 6n, quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), a), pilha}}, octeto(b)), R.Quadro{diminuir(2n, corpo), diminuir(2n, teto), C.Palavra{f, 5n, quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), quatro(Word.zero(8n), Word.zero(8n), a, b), pilha}},
    avancar_palavra_blocos(6n, f, Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), a, b, pilha, diminuir(1n, corpo), diminuir(1n, teto))) :
    {R.executar([octeto(c), octeto(d), octeto(e), octeto(fb), octeto(g), octeto(h)], _) == R.Quadro{diminuir(8n, corpo), diminuir(8n, teto), C.concluir_palavra(f, quatro(a, b, c, d), quatro(e, fb, g, h), pilha, diminuir(8n, corpo), diminuir(8n, teto))} : R.Quadro}
  %Equal.sym(R.Quadro, R.avancar(R.Quadro{diminuir(2n, corpo), diminuir(2n, teto), C.Palavra{f, 5n, quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), quatro(Word.zero(8n), Word.zero(8n), a, b), pilha}}, octeto(c)), R.Quadro{diminuir(3n, corpo), diminuir(3n, teto), C.Palavra{f, 4n, quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), quatro(Word.zero(8n), a, b, c), pilha}},
    avancar_palavra_blocos(5n, f, Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), a, b, c, pilha, diminuir(2n, corpo), diminuir(2n, teto))) :
    {R.executar([octeto(d), octeto(e), octeto(fb), octeto(g), octeto(h)], _) == R.Quadro{diminuir(8n, corpo), diminuir(8n, teto), C.concluir_palavra(f, quatro(a, b, c, d), quatro(e, fb, g, h), pilha, diminuir(8n, corpo), diminuir(8n, teto))} : R.Quadro}
  %Equal.sym(R.Quadro, R.avancar(R.Quadro{diminuir(3n, corpo), diminuir(3n, teto), C.Palavra{f, 4n, quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), quatro(Word.zero(8n), a, b, c), pilha}}, octeto(d)), R.Quadro{diminuir(4n, corpo), diminuir(4n, teto), C.Palavra{f, 3n, quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), quatro(a, b, c, d), pilha}},
    avancar_palavra_blocos(4n, f, Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), a, b, c, d, pilha, diminuir(3n, corpo), diminuir(3n, teto))) :
    {R.executar([octeto(e), octeto(fb), octeto(g), octeto(h)], _) == R.Quadro{diminuir(8n, corpo), diminuir(8n, teto), C.concluir_palavra(f, quatro(a, b, c, d), quatro(e, fb, g, h), pilha, diminuir(8n, corpo), diminuir(8n, teto))} : R.Quadro}
  %Equal.sym(R.Quadro, R.avancar(R.Quadro{diminuir(4n, corpo), diminuir(4n, teto), C.Palavra{f, 3n, quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), quatro(a, b, c, d), pilha}}, octeto(e)), R.Quadro{diminuir(5n, corpo), diminuir(5n, teto), C.Palavra{f, 2n, quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), a), quatro(b, c, d, e), pilha}},
    avancar_palavra_blocos(3n, f, Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), a, b, c, d, e, pilha, diminuir(4n, corpo), diminuir(4n, teto))) :
    {R.executar([octeto(fb), octeto(g), octeto(h)], _) == R.Quadro{diminuir(8n, corpo), diminuir(8n, teto), C.concluir_palavra(f, quatro(a, b, c, d), quatro(e, fb, g, h), pilha, diminuir(8n, corpo), diminuir(8n, teto))} : R.Quadro}
  %Equal.sym(R.Quadro, R.avancar(R.Quadro{diminuir(5n, corpo), diminuir(5n, teto), C.Palavra{f, 2n, quatro(Word.zero(8n), Word.zero(8n), Word.zero(8n), a), quatro(b, c, d, e), pilha}}, octeto(fb)), R.Quadro{diminuir(6n, corpo), diminuir(6n, teto), C.Palavra{f, 1n, quatro(Word.zero(8n), Word.zero(8n), a, b), quatro(c, d, e, fb), pilha}},
    avancar_palavra_blocos(2n, f, Word.zero(8n), Word.zero(8n), Word.zero(8n), a, b, c, d, e, fb, pilha, diminuir(5n, corpo), diminuir(5n, teto))) :
    {R.executar([octeto(g), octeto(h)], _) == R.Quadro{diminuir(8n, corpo), diminuir(8n, teto), C.concluir_palavra(f, quatro(a, b, c, d), quatro(e, fb, g, h), pilha, diminuir(8n, corpo), diminuir(8n, teto))} : R.Quadro}
  %Equal.sym(R.Quadro, R.avancar(R.Quadro{diminuir(6n, corpo), diminuir(6n, teto), C.Palavra{f, 1n, quatro(Word.zero(8n), Word.zero(8n), a, b), quatro(c, d, e, fb), pilha}}, octeto(g)), R.Quadro{diminuir(7n, corpo), diminuir(7n, teto), C.Palavra{f, 0n, quatro(Word.zero(8n), a, b, c), quatro(d, e, fb, g), pilha}},
    avancar_palavra_blocos(1n, f, Word.zero(8n), Word.zero(8n), a, b, c, d, e, fb, g, pilha, diminuir(6n, corpo), diminuir(6n, teto))) :
    {R.executar([octeto(h)], _) == R.Quadro{diminuir(8n, corpo), diminuir(8n, teto), C.concluir_palavra(f, quatro(a, b, c, d), quatro(e, fb, g, h), pilha, diminuir(8n, corpo), diminuir(8n, teto))} : R.Quadro}
  %Equal.sym(R.Quadro, R.avancar(R.Quadro{diminuir(7n, corpo), diminuir(7n, teto), C.Palavra{f, 0n, quatro(Word.zero(8n), a, b, c), quatro(d, e, fb, g), pilha}}, octeto(h)), R.Quadro{diminuir(8n, corpo), diminuir(8n, teto), C.concluir_palavra(f, quatro(a, b, c, d), quatro(e, fb, g, h), pilha, diminuir(8n, corpo), diminuir(8n, teto))},
    avancar_palavra_blocos(0n, f, Word.zero(8n), a, b, c, d, e, fb, g, h, pilha, diminuir(7n, corpo), diminuir(7n, teto))) :
    {R.executar([], _) == R.Quadro{diminuir(8n, corpo), diminuir(8n, teto), C.concluir_palavra(f, quatro(a, b, c, d), quatro(e, fb, g, h), pilha, diminuir(8n, corpo), diminuir(8n, teto))} : R.Quadro}
  {==}

# Teorema principal: qualquer finalidade, quaisquer words e qualquer pilha.
law be64_conclui_palavra:
  for +f: C.Finalidade
  for +alto: U32
  for +baixo: U32
  for +pilha: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  {R.executar(B.be64(alto, baixo), R.Quadro{corpo, teto, C.Palavra{f, 7n, 0, 0, pilha}}) ==
    R.Quadro{diminuir(8n, corpo), diminuir(8n, teto),
      C.concluir_palavra(f, alto, baixo, pilha, diminuir(8n, corpo), diminuir(8n, teto))} : R.Quadro}
def be64_conclui_palavra(f, alto, baixo, pilha, corpo, teto):
  match alto baixo:
    case U32{WCon{h0, WCon{h1, WCon{h2, WCon{h3, WCon{h4, WCon{h5, WCon{h6, WCon{h7, WCon{h8, WCon{h9, WCon{h10, WCon{h11, WCon{h12, WCon{h13, WCon{h14, WCon{h15, WCon{h16, WCon{h17, WCon{h18, WCon{h19, WCon{h20, WCon{h21, WCon{h22, WCon{h23, WCon{h24, WCon{h25, WCon{h26, WCon{h27, WCon{h28, WCon{h29, WCon{h30, WCon{h31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{l0, WCon{l1, WCon{l2, WCon{l3, WCon{l4, WCon{l5, WCon{l6, WCon{l7, WCon{l8, WCon{l9, WCon{l10, WCon{l11, WCon{l12, WCon{l13, WCon{l14, WCon{l15, WCon{l16, WCon{l17, WCon{l18, WCon{l19, WCon{l20, WCon{l21, WCon{l22, WCon{l23, WCon{l24, WCon{l25, WCon{l26, WCon{l27, WCon{l28, WCon{l29, WCon{l30, WCon{l31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %Equal.sym(List<&2, U32>, B.be32(alto), [octeto(WCon{h24, WCon{h25, WCon{h26, WCon{h27, WCon{h28, WCon{h29, WCon{h30, WCon{h31, WNil{}}}}}}}}}), octeto(WCon{h16, WCon{h17, WCon{h18, WCon{h19, WCon{h20, WCon{h21, WCon{h22, WCon{h23, WNil{}}}}}}}}}), octeto(WCon{h8, WCon{h9, WCon{h10, WCon{h11, WCon{h12, WCon{h13, WCon{h14, WCon{h15, WNil{}}}}}}}}}), octeto(WCon{h0, WCon{h1, WCon{h2, WCon{h3, WCon{h4, WCon{h5, WCon{h6, WCon{h7, WNil{}}}}}}}}})], be32_quatro(WCon{h24, WCon{h25, WCon{h26, WCon{h27, WCon{h28, WCon{h29, WCon{h30, WCon{h31, WNil{}}}}}}}}}, WCon{h16, WCon{h17, WCon{h18, WCon{h19, WCon{h20, WCon{h21, WCon{h22, WCon{h23, WNil{}}}}}}}}}, WCon{h8, WCon{h9, WCon{h10, WCon{h11, WCon{h12, WCon{h13, WCon{h14, WCon{h15, WNil{}}}}}}}}}, WCon{h0, WCon{h1, WCon{h2, WCon{h3, WCon{h4, WCon{h5, WCon{h6, WCon{h7, WNil{}}}}}}}}})) :
        {R.executar(B.concatenar(_, B.be32(baixo)), R.Quadro{corpo, teto, C.Palavra{f, 7n, 0, 0, pilha}}) == R.Quadro{diminuir(8n, corpo), diminuir(8n, teto), C.concluir_palavra(f, alto, baixo, pilha, diminuir(8n, corpo), diminuir(8n, teto))} : R.Quadro}
      %Equal.sym(List<&2, U32>, B.be32(baixo), [octeto(WCon{l24, WCon{l25, WCon{l26, WCon{l27, WCon{l28, WCon{l29, WCon{l30, WCon{l31, WNil{}}}}}}}}}), octeto(WCon{l16, WCon{l17, WCon{l18, WCon{l19, WCon{l20, WCon{l21, WCon{l22, WCon{l23, WNil{}}}}}}}}}), octeto(WCon{l8, WCon{l9, WCon{l10, WCon{l11, WCon{l12, WCon{l13, WCon{l14, WCon{l15, WNil{}}}}}}}}}), octeto(WCon{l0, WCon{l1, WCon{l2, WCon{l3, WCon{l4, WCon{l5, WCon{l6, WCon{l7, WNil{}}}}}}}}})], be32_quatro(WCon{l24, WCon{l25, WCon{l26, WCon{l27, WCon{l28, WCon{l29, WCon{l30, WCon{l31, WNil{}}}}}}}}}, WCon{l16, WCon{l17, WCon{l18, WCon{l19, WCon{l20, WCon{l21, WCon{l22, WCon{l23, WNil{}}}}}}}}}, WCon{l8, WCon{l9, WCon{l10, WCon{l11, WCon{l12, WCon{l13, WCon{l14, WCon{l15, WNil{}}}}}}}}}, WCon{l0, WCon{l1, WCon{l2, WCon{l3, WCon{l4, WCon{l5, WCon{l6, WCon{l7, WNil{}}}}}}}}})) :
        {R.executar(B.concatenar([octeto(WCon{h24, WCon{h25, WCon{h26, WCon{h27, WCon{h28, WCon{h29, WCon{h30, WCon{h31, WNil{}}}}}}}}}), octeto(WCon{h16, WCon{h17, WCon{h18, WCon{h19, WCon{h20, WCon{h21, WCon{h22, WCon{h23, WNil{}}}}}}}}}), octeto(WCon{h8, WCon{h9, WCon{h10, WCon{h11, WCon{h12, WCon{h13, WCon{h14, WCon{h15, WNil{}}}}}}}}}), octeto(WCon{h0, WCon{h1, WCon{h2, WCon{h3, WCon{h4, WCon{h5, WCon{h6, WCon{h7, WNil{}}}}}}}}})], _), R.Quadro{corpo, teto, C.Palavra{f, 7n, 0, 0, pilha}}) == R.Quadro{diminuir(8n, corpo), diminuir(8n, teto), C.concluir_palavra(f, alto, baixo, pilha, diminuir(8n, corpo), diminuir(8n, teto))} : R.Quadro}
      oito_octetos_concluem_palavra(f, WCon{h24, WCon{h25, WCon{h26, WCon{h27, WCon{h28, WCon{h29, WCon{h30, WCon{h31, WNil{}}}}}}}}}, WCon{h16, WCon{h17, WCon{h18, WCon{h19, WCon{h20, WCon{h21, WCon{h22, WCon{h23, WNil{}}}}}}}}}, WCon{h8, WCon{h9, WCon{h10, WCon{h11, WCon{h12, WCon{h13, WCon{h14, WCon{h15, WNil{}}}}}}}}}, WCon{h0, WCon{h1, WCon{h2, WCon{h3, WCon{h4, WCon{h5, WCon{h6, WCon{h7, WNil{}}}}}}}}}, WCon{l24, WCon{l25, WCon{l26, WCon{l27, WCon{l28, WCon{l29, WCon{l30, WCon{l31, WNil{}}}}}}}}}, WCon{l16, WCon{l17, WCon{l18, WCon{l19, WCon{l20, WCon{l21, WCon{l22, WCon{l23, WNil{}}}}}}}}}, WCon{l8, WCon{l9, WCon{l10, WCon{l11, WCon{l12, WCon{l13, WCon{l14, WCon{l15, WNil{}}}}}}}}}, WCon{l0, WCon{l1, WCon{l2, WCon{l3, WCon{l4, WCon{l5, WCon{l6, WCon{l7, WNil{}}}}}}}}}, pilha, corpo, teto)

law be64_inteiro_emite:
  for +alto: U32
  for +baixo: U32
  for +pilha: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  {R.executar(B.be64(alto, baixo), R.Quadro{corpo, teto, C.Palavra{C.Inteiro{}, 7n, 0, 0, pilha}}) ==
    R.Quadro{diminuir(8n, corpo), diminuir(8n, teto), C.emitir(pilha, D.VInt{alto, baixo})} : R.Quadro}
def be64_inteiro_emite(alto, baixo, pilha, corpo, teto):
  be64_conclui_palavra(C.Inteiro{}, alto, baixo, pilha, corpo, teto)

law be64_inteiro_oito_passos:
  for +alto: U32
  for +baixo: U32
  for +pilha: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  {R.maquina(R.executar(B.be64(alto, baixo), R.Quadro{corpo, teto, C.Palavra{C.Inteiro{}, 7n, 0, 0, pilha}})) ==
    C.emitir(pilha, D.VInt{alto, baixo}) : C.Maquina}
def be64_inteiro_oito_passos(alto, baixo, pilha, corpo, teto):
  Equal.cong(R.Quadro, C.Maquina, q => R.maquina(q),
    R.executar(B.be64(alto, baixo), R.Quadro{corpo, teto, C.Palavra{C.Inteiro{}, 7n, 0, 0, pilha}}),
    R.Quadro{diminuir(8n, corpo), diminuir(8n, teto), C.emitir(pilha, D.VInt{alto, baixo})},
    be64_inteiro_emite(alto, baixo, pilha, corpo, teto))

law be64_inteiro_preserva_sufixo:
  for +alto: U32
  for +baixo: U32
  for +pilha: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +sufixo: List<&2, U32>
  {R.executar(B.concatenar(B.be64(alto, baixo), sufixo),
    R.Quadro{corpo, teto, C.Palavra{C.Inteiro{}, 7n, 0, 0, pilha}}) ==
    R.executar(sufixo, R.Quadro{diminuir(8n, corpo), diminuir(8n, teto), C.emitir(pilha, D.VInt{alto, baixo})}) : R.Quadro}
def be64_inteiro_preserva_sufixo(alto, baixo, pilha, corpo, teto, sufixo):
  Equal.trans(R.Quadro,
    R.executar(B.concatenar(B.be64(alto, baixo), sufixo), R.Quadro{corpo, teto, C.Palavra{C.Inteiro{}, 7n, 0, 0, pilha}}),
    R.executar(sufixo, R.executar(B.be64(alto, baixo), R.Quadro{corpo, teto, C.Palavra{C.Inteiro{}, 7n, 0, 0, pilha}})),
    R.executar(sufixo, R.Quadro{diminuir(8n, corpo), diminuir(8n, teto), C.emitir(pilha, D.VInt{alto, baixo})}),
    R.execucao_de_concatenacao(B.be64(alto, baixo), sufixo, R.Quadro{corpo, teto, C.Palavra{C.Inteiro{}, 7n, 0, 0, pilha}}),
    Equal.cong(R.Quadro, R.Quadro, q => R.executar(sufixo, q),
      R.executar(B.be64(alto, baixo), R.Quadro{corpo, teto, C.Palavra{C.Inteiro{}, 7n, 0, 0, pilha}}),
      R.Quadro{diminuir(8n, corpo), diminuir(8n, teto), C.emitir(pilha, D.VInt{alto, baixo})},
      be64_inteiro_emite(alto, baixo, pilha, corpo, teto)))
