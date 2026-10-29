# Extracao de uma palavra BE64 da execucao real, para qualquer finalidade
# e pilha. A validade dos octetos vem dos pre-checks de decodificar;
# R.executar, isoladamente, nao verifica U32 <= 255.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecPercurso.bend as R
import ./CodecPalavrasBE64.bend as H
import ./CodecPalavrasInversa.bend as I

def inicio(f: C.Finalidade, pilha: C.Pilha, corpo: B.Numero64, teto: B.Numero64) -> R.Quadro:
  R.Quadro{corpo, teto, C.Palavra{f, 7n, 0, 0, pilha}}

def apos_palavra(f: C.Finalidade, alto: U32, baixo: U32, pilha: C.Pilha,
  +corpo: B.Numero64, +teto: B.Numero64) -> R.Quadro:
  R.Quadro{H.diminuir(8n, corpo), H.diminuir(8n, teto),
    C.concluir_palavra(f, alto, baixo, pilha, H.diminuir(8n, corpo), H.diminuir(8n, teto))}

# O contador faltam guarda o numero de octetos APOS o proximo: faltam=0
# ainda exige um octeto. A forma e obtida da execucao, nao e uma premissa
# do teorema publico de extracao.
def PalavraSuficiente(n: Nat, bs: List<&2, U32>) -> Type:
  match n bs:
    case 0n Nil{}:
      Empty
    case 0n Con{b, t}:
      Unit
    case 1n+p Nil{}:
      Empty
    case 1n+p Con{b, t}:
      PalavraSuficiente(p, t)

law palavra_pronta_exige_prefixo_completo:
  for n: Nat
  for +bs: List<&2, U32>
  for +f: C.Finalidade
  for +alto: U32
  for +baixo: U32
  for +pilha: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for -v: D.Valor
  for pronto: {R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.Palavra{f, n, alto, baixo, pilha}})) == C.Pronto{v} : C.Maquina}
  PalavraSuficiente(n, bs)
def palavra_pronta_exige_prefixo_completo(n, bs, f, alto, baixo, pilha, corpo, teto, v, pronto):
  match n bs:
    case 0n Nil{}:
      R.entrada_nao_decodificada(v,
        Equal.cong(C.Maquina, C.Resultado, m => C.finalizar(m),
          C.Palavra{f, 0n, alto, baixo, pilha}, C.Pronto{v}, pronto))
    case 0n Con{b, t}:
      Unit{}
    case 1n+p Nil{}:
      R.entrada_nao_decodificada(v,
        Equal.cong(C.Maquina, C.Resultado, m => C.finalizar(m),
          C.Palavra{f, 1n+p, alto, baixo, pilha}, C.Pronto{v}, pronto))
    case 1n+p Con{+b, +t}:
      palavra_pronta_exige_prefixo_completo(p, t, f,
        (alto * 256 + U32.shrn(baixo, 24n) : U32), (baixo * 256 + b : U32),
        pilha, C.diminuir64(corpo), C.diminuir64(teto), v, pronto)

# Separa a validade do prefixo ORIGINAL e do sufixo; nenhuma recodificacao
# ou hipotese de canonicidade participa desta etapa.
def juntar_validade_de_octetos(-b: U32, -t: List<&2, U32>, -ys: List<&2, U32>,
  vb: {U32.is_le(b, 255) == True{} : Bool},
  par: L.E<{B.octetos_validos(t) == True{} : Bool}, {B.octetos_validos(ys) == True{} : Bool}>) ->
  L.E<{B.octetos_validos(Con{b, t}) == True{} : Bool}, {B.octetos_validos(ys) == True{} : Bool}>:
  match par:
    case L.Ambos{vt, vy}:
      L.Ambos{F.e_booleano_intro(U32.is_le(b, 255), B.octetos_validos(t), vb, vt), vy}

law separar_octetos_validos:
  for xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +validos: {B.octetos_validos(B.concatenar(xs, ys)) == True{} : Bool}
  L.E<{B.octetos_validos(xs) == True{} : Bool}, {B.octetos_validos(ys) == True{} : Bool}>
def separar_octetos_validos(xs, ys, validos):
  match xs:
    case Nil{}:
      L.Ambos{{==}, validos}
    case Con{+b, +t}:
      juntar_validade_de_octetos(b, t, ys,
        F.e_booleano_esquerda(U32.is_le(b, 255), B.octetos_validos(B.concatenar(t, ys)), validos),
        separar_octetos_validos(t, ys,
          F.e_booleano_direita(U32.is_le(b, 255), B.octetos_validos(B.concatenar(t, ys)), validos)))

# a..h sao os oito U32 da lista recebida. alto/baixo sao calculados por
# acumular, e be64 demonstra posteriormente que recodifica esses mesmos
# octetos. execucao conserva TODO o quadro final, inclusive os contadores.
type PalavraExtraida<-bs: List<&2, U32>, -f: C.Finalidade, -pilha: C.Pilha,
  -corpo: B.Numero64, -teto: B.Numero64, -v: D.Valor> is Type:
  Extraida{a: U32, b: U32, c: U32, d: U32, e: U32, f0: U32, g: U32, h: U32,
    sufixo: List<&2, U32>, alto: U32, baixo: U32,
    fatoracao: {bs == B.concatenar([a, b, c, d, e, f0, g, h], sufixo) : List<&2, U32>},
    octetos: {B.octetos_validos([a, b, c, d, e, f0, g, h]) == True{} : Bool},
    resto_valido: {B.octetos_validos(sufixo) == True{} : Bool},
    numero: {I.acumular([a, b, c, d, e, f0, g, h], B.Numero64{0, 0}) == B.Numero64{alto, baixo} : B.Numero64},
    be64: {B.be64(alto, baixo) == [a, b, c, d, e, f0, g, h] : List<&2, U32>},
    fatoracao_be64: {bs == B.concatenar(B.be64(alto, baixo), sufixo) : List<&2, U32>},
    quadro: {R.executar([a, b, c, d, e, f0, g, h], inicio(f, pilha, corpo, teto)) == apos_palavra(f, alto, baixo, pilha, corpo, teto) : R.Quadro},
    execucao: {R.executar(sufixo, apos_palavra(f, alto, baixo, pilha, corpo, teto)) == R.executar(bs, inicio(f, pilha, corpo, teto)) : R.Quadro},
    pronto: {R.maquina(R.executar(sufixo, apos_palavra(f, alto, baixo, pilha, corpo, teto))) == C.Pronto{v} : C.Maquina}}

def extrair_oito_octetos(+a: U32, +b: U32, +c: U32, +d: U32,
  +e: U32, +f0: U32, +g: U32, +h: U32, +sufixo: List<&2, U32>,
  +f: C.Finalidade, +pilha: C.Pilha, +corpo: B.Numero64, +teto: B.Numero64, -v: D.Valor,
  pronto: {R.maquina(R.executar(B.concatenar([a, b, c, d, e, f0, g, h], sufixo), inicio(f, pilha, corpo, teto))) == C.Pronto{v} : C.Maquina},
  par: L.E<{B.octetos_validos([a, b, c, d, e, f0, g, h]) == True{} : Bool},
    {B.octetos_validos(sufixo) == True{} : Bool}>) ->
  PalavraExtraida<B.concatenar([a, b, c, d, e, f0, g, h], sufixo), f, pilha, corpo, teto, v>:
  match par:
    case L.Ambos{+octetos, resto_valido}:
      +quadro = I.oito_octetos_validos_concluem_palavra(f, a, b, c, d, e, f0, g, h, pilha, corpo, teto, octetos)
      +execucao = Equal.sym(R.Quadro,
        R.executar(B.concatenar([a, b, c, d, e, f0, g, h], sufixo), inicio(f, pilha, corpo, teto)),
        R.executar(sufixo, apos_palavra(f, I.montar(a, b, c, d), I.montar(e, f0, g, h), pilha, corpo, teto)),
        Equal.trans(R.Quadro,
          R.executar(B.concatenar([a, b, c, d, e, f0, g, h], sufixo), inicio(f, pilha, corpo, teto)),
          R.executar(sufixo, R.executar([a, b, c, d, e, f0, g, h], inicio(f, pilha, corpo, teto))),
          R.executar(sufixo, apos_palavra(f, I.montar(a, b, c, d), I.montar(e, f0, g, h), pilha, corpo, teto)),
          R.execucao_de_concatenacao([a, b, c, d, e, f0, g, h], sufixo, inicio(f, pilha, corpo, teto)),
          Equal.cong(R.Quadro, R.Quadro, q => R.executar(sufixo, q),
            R.executar([a, b, c, d, e, f0, g, h], inicio(f, pilha, corpo, teto)),
            apos_palavra(f, I.montar(a, b, c, d), I.montar(e, f0, g, h), pilha, corpo, teto), quadro)))
      +be64 = I.be64_recodifica_oito_octetos_validos(a, b, c, d, e, f0, g, h, octetos)
      Extraida{a, b, c, d, e, f0, g, h, sufixo, I.montar(a, b, c, d), I.montar(e, f0, g, h),
        {==}, octetos, resto_valido,
        I.acumular_oito_octetos_validos(a, b, c, d, e, f0, g, h, octetos), be64,
        Equal.cong(List<&2, U32>, List<&2, U32>, xs => B.concatenar(xs, sufixo),
          [a, b, c, d, e, f0, g, h], B.be64(I.montar(a, b, c, d), I.montar(e, f0, g, h)),
          Equal.sym(List<&2, U32>, B.be64(I.montar(a, b, c, d), I.montar(e, f0, g, h)), [a, b, c, d, e, f0, g, h], be64)),
        quadro, execucao,
        Equal.trans(C.Maquina,
          R.maquina(R.executar(sufixo, apos_palavra(f, I.montar(a, b, c, d), I.montar(e, f0, g, h), pilha, corpo, teto))),
          R.maquina(R.executar(B.concatenar([a, b, c, d, e, f0, g, h], sufixo), inicio(f, pilha, corpo, teto))), C.Pronto{v},
          Equal.cong(R.Quadro, C.Maquina, q => R.maquina(q),
            R.executar(sufixo, apos_palavra(f, I.montar(a, b, c, d), I.montar(e, f0, g, h), pilha, corpo, teto)),
            R.executar(B.concatenar([a, b, c, d, e, f0, g, h], sufixo), inicio(f, pilha, corpo, teto)), execucao), pronto)}

def extrair_palavra_com_formato(+bs: List<&2, U32>, +f: C.Finalidade, +pilha: C.Pilha,
  +corpo: B.Numero64, +teto: B.Numero64, -v: D.Valor,
  validos: {B.octetos_validos(bs) == True{} : Bool},
  pronto: {R.maquina(R.executar(bs, inicio(f, pilha, corpo, teto))) == C.Pronto{v} : C.Maquina},
  formato: PalavraSuficiente(7n, bs)) -> PalavraExtraida<bs, f, pilha, corpo, teto, v>:
  match bs:
    case Nil{}:
      L.ex_falso(PalavraExtraida<bs, f, pilha, corpo, teto, v>, formato)
    case Con{a, Nil{}}:
      L.ex_falso(PalavraExtraida<bs, f, pilha, corpo, teto, v>, formato)
    case Con{a, Con{b, Nil{}}}:
      L.ex_falso(PalavraExtraida<bs, f, pilha, corpo, teto, v>, formato)
    case Con{a, Con{b, Con{c, Nil{}}}}:
      L.ex_falso(PalavraExtraida<bs, f, pilha, corpo, teto, v>, formato)
    case Con{a, Con{b, Con{c, Con{d, Nil{}}}}}:
      L.ex_falso(PalavraExtraida<bs, f, pilha, corpo, teto, v>, formato)
    case Con{a, Con{b, Con{c, Con{d, Con{e, Nil{}}}}}}:
      L.ex_falso(PalavraExtraida<bs, f, pilha, corpo, teto, v>, formato)
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f0, Nil{}}}}}}}:
      L.ex_falso(PalavraExtraida<bs, f, pilha, corpo, teto, v>, formato)
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f0, Con{g, Nil{}}}}}}}}:
      L.ex_falso(PalavraExtraida<bs, f, pilha, corpo, teto, v>, formato)
    case Con{+a, Con{+b, Con{+c, Con{+d, Con{+e, Con{+f0, Con{+g, Con{+h, +sufixo}}}}}}}}:
      extrair_oito_octetos(a, b, c, d, e, f0, g, h, sufixo, f, pilha, corpo, teto, v, pronto,
        separar_octetos_validos([a, b, c, d, e, f0, g, h], sufixo, validos))

# Premissas: octetos validos e chegada REAL a Pronto. Nenhuma forma de bs,
# numero BE64, suficiência de corpo/teto ou canonicidade e pressuposta.
law palavra_aceita_extrai_be64_e_execucao_restante:
  for +bs: List<&2, U32>
  for +f: C.Finalidade
  for +pilha: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for -v: D.Valor
  for validos: {B.octetos_validos(bs) == True{} : Bool}
  for +pronto: {R.maquina(R.executar(bs, inicio(f, pilha, corpo, teto))) == C.Pronto{v} : C.Maquina}
  PalavraExtraida<bs, f, pilha, corpo, teto, v>
def palavra_aceita_extrai_be64_e_execucao_restante(bs, f, pilha, corpo, teto, v, validos, pronto):
  extrair_palavra_com_formato(bs, f, pilha, corpo, teto, v, validos, pronto,
    palavra_pronta_exige_prefixo_completo(7n, bs, f, 0, 0, pilha, corpo, teto, v, pronto))
