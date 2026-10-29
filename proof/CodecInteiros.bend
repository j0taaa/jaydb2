# Roundtrip e canonicidade GERAIS dos inteiros: todos os 2^64 bit patterns.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./Ordens.bend as O
import ./CodecPalavrasWord.bend as W
import ./CodecPalavrasBE64.bend as H
import ./CodecPalavrasInversa.bend as I
import ./CodecUTF8Bits.bend as A
import ./CodecPercurso.bend as R

law cmp_bit_ate_maximo:
  for b: Bool
  for c: Cmp
  for e: {Cmp.is_le(c) == True{} : Bool}
  {Cmp.is_le(Word.cmp.fin(b, True{}, c)) == True{} : Bool}
def cmp_bit_ate_maximo(b, c, e):
  match b c:
    case False{} EQ{}:
      {==}
    case False{} LT{}:
      {==}
    case True{} EQ{}:
      {==}
    case True{} LT{}:
      {==}
    case False{} GT{}:
      F.absurdo_booleano({False{} == True{} : Bool}, e)
    case True{} GT{}:
      F.absurdo_booleano({False{} == True{} : Bool}, e)

law palavra_ate_maximo:
  for +n: Nat
  for +w: Word(n)
  {Cmp.is_le(Word.cmp(n, w, W.uns(n))) == True{} : Bool}
def palavra_ate_maximo(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, +t}:
          cmp_bit_ate_maximo(b, Word.cmp(p, t, W.uns(p)), palavra_ate_maximo(p, t))

law todo_octeto_formado_cabe_em_255:
  for +w: Word(8n)
  {U32.is_le(H.octeto(w), 255) == True{} : Bool}
def todo_octeto_formado_cabe_em_255(w):
  %Equal.sym(Cmp,
    Word.cmp(32n, W.juntar(8n, 24n, w, Word.zero(24n)), W.juntar(8n, 24n, W.uns(8n), Word.zero(24n))),
    O.prioridade(Word.cmp(24n, Word.zero(24n), Word.zero(24n)), Word.cmp(8n, w, W.uns(8n))),
    A.comparar_blocos(8n, 24n, w, W.uns(8n), Word.zero(24n), Word.zero(24n))) :
    {Cmp.is_le(_) == True{} : Bool}
  palavra_ate_maximo(8n, w)

law mascara_de_octeto_e_valida:
  for +x: U32
  {U32.is_le(U32.and(x, 255), 255) == True{} : Bool}
def mascara_de_octeto_e_valida(x):
  %Equal.sym(U32, U32.and(x, 255), H.octeto(W.ajustar(8n, 32n, H.bits(x))), H.mascara_octeto(x)) :
    {U32.is_le(_, 255) == True{} : Bool}
  todo_octeto_formado_cabe_em_255(W.ajustar(8n, 32n, H.bits(x)))

law be32_so_emite_octetos:
  for +x: U32
  {B.octetos_validos(B.be32(x)) == True{} : Bool}
def be32_so_emite_octetos(x):
  F.e_booleano_intro(U32.is_le(U32.and(U32.shrn(x, 24n), 255), 255),
    U32.is_le(U32.and(U32.shrn(x, 16n), 255), 255) && (U32.is_le(U32.and(U32.shrn(x, 8n), 255), 255) && (U32.is_le(U32.and(x, 255), 255) && True{})),
    mascara_de_octeto_e_valida(U32.shrn(x, 24n)),
    F.e_booleano_intro(U32.is_le(U32.and(U32.shrn(x, 16n), 255), 255),
      U32.is_le(U32.and(U32.shrn(x, 8n), 255), 255) && (U32.is_le(U32.and(x, 255), 255) && True{}),
      mascara_de_octeto_e_valida(U32.shrn(x, 16n)),
      F.e_booleano_intro(U32.is_le(U32.and(U32.shrn(x, 8n), 255), 255), U32.is_le(U32.and(x, 255), 255) && True{},
        mascara_de_octeto_e_valida(U32.shrn(x, 8n)),
        F.e_booleano_intro(U32.is_le(U32.and(x, 255), 255), True{}, mascara_de_octeto_e_valida(x), {==}))))

law concatenar_preserva_octetos:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +vx: {B.octetos_validos(xs) == True{} : Bool}
  for vy: {B.octetos_validos(ys) == True{} : Bool}
  {B.octetos_validos(B.concatenar(xs, ys)) == True{} : Bool}
def concatenar_preserva_octetos(xs, ys, vx, vy):
  match xs:
    case Nil{}:
      vy
    case Con{+h, +t}:
      F.e_booleano_intro(U32.is_le(h, 255), B.octetos_validos(B.concatenar(t, ys)),
        F.e_booleano_esquerda(U32.is_le(h, 255), B.octetos_validos(t), vx),
        concatenar_preserva_octetos(t, ys, F.e_booleano_direita(U32.is_le(h, 255), B.octetos_validos(t), vx), vy))

law be64_so_emite_octetos:
  for +alto: U32
  for +baixo: U32
  {B.octetos_validos(B.be64(alto, baixo)) == True{} : Bool}
def be64_so_emite_octetos(alto, baixo):
  concatenar_preserva_octetos(B.be32(alto), B.be32(baixo), be32_so_emite_octetos(alto), be32_so_emite_octetos(baixo))

law percurso_de_inteiro_e_exato:
  for +alto: U32
  for +baixo: U32
  for +corpo: B.Numero64
  for +teto: B.Numero64
  {C.percorrer(B.be64(alto, baixo), corpo, teto, C.Palavra{C.Inteiro{}, 7n, 0, 0, C.Raiz{}}) ==
    C.Decodificado{D.VInt{alto, baixo}} : C.Resultado}
def percurso_de_inteiro_e_exato(alto, baixo, corpo, teto):
  Equal.trans(C.Resultado,
    C.percorrer(B.be64(alto, baixo), corpo, teto, C.Palavra{C.Inteiro{}, 7n, 0, 0, C.Raiz{}}),
    R.finalizar_quadro(R.executar(B.be64(alto, baixo), R.Quadro{corpo, teto, C.Palavra{C.Inteiro{}, 7n, 0, 0, C.Raiz{}}})),
    C.Decodificado{D.VInt{alto, baixo}},
    R.percurso_e_execucao_integral(B.be64(alto, baixo), R.Quadro{corpo, teto, C.Palavra{C.Inteiro{}, 7n, 0, 0, C.Raiz{}}}),
    Equal.cong(R.Quadro, C.Resultado, q => R.finalizar_quadro(q),
      R.executar(B.be64(alto, baixo), R.Quadro{corpo, teto, C.Palavra{C.Inteiro{}, 7n, 0, 0, C.Raiz{}}}),
      R.Quadro{H.diminuir(8n, corpo), H.diminuir(8n, teto), C.Pronto{D.VInt{alto, baixo}}},
      H.be64_inteiro_emite(alto, baixo, C.Raiz{}, corpo, teto)))

law todo_inteiro_canonico_dentro_do_limite_e_aceito:
  for +alto: U32
  for +baixo: U32
  for +teto: B.Numero64
  for cabe: {C.menor_igual64(B.Numero64{0, 9}, teto) == True{} : Bool}
  {C.decodificar(Con{3, B.be64(alto, baixo)}, teto) == C.Decodificado{D.VInt{alto, baixo}} : C.Resultado}
def todo_inteiro_canonico_dentro_do_limite_e_aceito(alto, baixo, teto, cabe):
  %Equal.sym(Bool, C.menor_igual64(B.Numero64{0, 9}, teto), True{}, cabe) :
    {C.decodificar_tamanho(_, Con{3, B.be64(alto, baixo)}, B.Numero64{0, 9}, teto) == C.Decodificado{D.VInt{alto, baixo}} : C.Resultado}
  %Equal.sym(Bool, B.octetos_validos(Con{3, B.be64(alto, baixo)}), True{}, be64_so_emite_octetos(alto, baixo)) :
    {C.decodificar_octetos(_, Con{3, B.be64(alto, baixo)}, B.Numero64{0, 9}, teto) == C.Decodificado{D.VInt{alto, baixo}} : C.Resultado}
  percurso_de_inteiro_e_exato(alto, baixo, B.Numero64{0, 8}, C.diminuir64(teto))

law inteiro_de_oito_octetos_reconstitui_a_codificacao_original:
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +e: U32
  for +f: U32
  for +g: U32
  for +h: U32
  for +validos: {B.octetos_validos([a, b, c, d, e, f, g, h]) == True{} : Bool}
  {P.codificar(D.VInt{I.montar(a, b, c, d), I.montar(e, f, g, h)}) == Some{[3, a, b, c, d, e, f, g, h]} : Maybe<&2, List<&2, U32>>}
def inteiro_de_oito_octetos_reconstitui_a_codificacao_original(a, b, c, d, e, f, g, h, validos):
  Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, bs => Some{Con{3, bs}},
    B.be64(I.montar(a, b, c, d), I.montar(e, f, g, h)), [a, b, c, d, e, f, g, h],
    I.be64_recodifica_oito_octetos_validos(a, b, c, d, e, f, g, h, validos))

law quaisquer_oito_octetos_validos_sao_inteiro_canonico:
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +e: U32
  for +f: U32
  for +g: U32
  for +h: U32
  for +teto: B.Numero64
  for +validos: {B.octetos_validos([a, b, c, d, e, f, g, h]) == True{} : Bool}
  for cabe: {C.menor_igual64(B.Numero64{0, 9}, teto) == True{} : Bool}
  {C.decodificar([3, a, b, c, d, e, f, g, h], teto) == C.Decodificado{D.VInt{I.montar(a, b, c, d), I.montar(e, f, g, h)}} : C.Resultado}
def quaisquer_oito_octetos_validos_sao_inteiro_canonico(a, b, c, d, e, f, g, h, teto, validos, cabe):
  %I.be64_recodifica_oito_octetos_validos(a, b, c, d, e, f, g, h, validos) :
    {C.decodificar(Con{3, _}, teto) == C.Decodificado{D.VInt{I.montar(a, b, c, d), I.montar(e, f, g, h)}} : C.Resultado}
  todo_inteiro_canonico_dentro_do_limite_e_aceito(I.montar(a, b, c, d), I.montar(e, f, g, h), teto, cabe)

def valor_resultado(r: C.Resultado) -> D.Valor:
  match r:
    case C.Decodificado{v}:
      v
    case _:
      D.VAusente{}

# O limite e os octetos tambem sao extraidos da ACEITACAO real, sem
# pedir ao chamador uma testemunha adicional de canonicidade ou validade.
def concluir_inteiro_aceito(+a: U32, +b: U32, +c: U32, +d: U32,
  +e: U32, +f: U32, +g: U32, +h: U32, +teto: B.Numero64, -v: D.Valor,
  aceito: {C.decodificar([3, a, b, c, d, e, f, g, h], teto) == C.Decodificado{v} : C.Resultado},
  entrada: R.EntradaConferida<Some{B.Numero64{0, 9}}, [3, a, b, c, d, e, f, g, h], teto, v>) ->
  P.Codificacao(v, [3, a, b, c, d, e, f, g, h]):
  match entrada:
    case R.Conferida{+corpo, medida, cabe, octetos, percurso}:
      cabe9 = {(%Equal.sym(B.Numero64, B.Numero64{0, 9}, corpo, F.algum_injetivo(B.Numero64, B.Numero64{0, 9}, corpo, medida)) :
        {C.menor_igual64(_, teto) == True{} : Bool}
        cabe) : {C.menor_igual64(B.Numero64{0, 9}, teto) == True{} : Bool}}
      +validos = F.e_booleano_direita(True{}, B.octetos_validos([a, b, c, d, e, f, g, h]), octetos)
      valor = Equal.cong(C.Resultado, D.Valor, r => valor_resultado(r),
        C.Decodificado{D.VInt{I.montar(a, b, c, d), I.montar(e, f, g, h)}}, C.Decodificado{v},
        Equal.trans(C.Resultado,
          C.Decodificado{D.VInt{I.montar(a, b, c, d), I.montar(e, f, g, h)}}, C.decodificar([3, a, b, c, d, e, f, g, h], teto), C.Decodificado{v},
          Equal.sym(C.Resultado, C.decodificar([3, a, b, c, d, e, f, g, h], teto), C.Decodificado{D.VInt{I.montar(a, b, c, d), I.montar(e, f, g, h)}},
            quaisquer_oito_octetos_validos_sao_inteiro_canonico(a, b, c, d, e, f, g, h, teto, validos, cabe9)), aceito))
      %valor : P.Codificacao(_, [3, a, b, c, d, e, f, g, h])
      inteiro_de_oito_octetos_reconstitui_a_codificacao_original(a, b, c, d, e, f, g, h, validos)

law aceitacao_de_inteiro_reconstroi_exatamente_os_bytes:
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +e: U32
  for +f: U32
  for +g: U32
  for +h: U32
  for +teto: B.Numero64
  for -v: D.Valor
  for +aceito: {C.decodificar([3, a, b, c, d, e, f, g, h], teto) == C.Decodificado{v} : C.Resultado}
  P.Codificacao(v, [3, a, b, c, d, e, f, g, h])
def aceitacao_de_inteiro_reconstroi_exatamente_os_bytes(a, b, c, d, e, f, g, h, teto, v, aceito):
  concluir_inteiro_aceito(a, b, c, d, e, f, g, h, teto, v, aceito,
    R.aceitacao_exige_corpo_representavel_octetos_e_limite([3, a, b, c, d, e, f, g, h], teto, v, aceito))

# Comprimento exigido pela propria maquina Palavra, inclusive EOF e extras.
def PalavraInteiraCompleta(n: Nat, bs: List<&2, U32>) -> Type:
  match n bs:
    case 0n Con{b, Nil{}}:
      Unit
    case 0n Nil{}:
      Empty
    case 0n Con{b, Con{c, t}}:
      Empty
    case 1n+p Nil{}:
      Empty
    case 1n+p Con{b, t}:
      PalavraInteiraCompleta(p, t)

law palavra_inteira_aceita_exige_tamanho_exato:
  for n: Nat
  for +bs: List<&2, U32>
  for +alto: U32
  for +baixo: U32
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for -v: D.Valor
  for aceito: {C.percorrer(bs, corpo, teto, C.Palavra{C.Inteiro{}, n, alto, baixo, C.Raiz{}}) == C.Decodificado{v} : C.Resultado}
  PalavraInteiraCompleta(n, bs)
def palavra_inteira_aceita_exige_tamanho_exato(n, bs, alto, baixo, corpo, teto, v, aceito):
  match n bs:
    case 0n Nil{}:
      R.entrada_nao_decodificada(v, aceito)
    case 0n Con{b, Nil{}}:
      Unit{}
    case 0n Con{+b, Con{+c, +t}}:
      R.entrada_nao_decodificada(v,
        Equal.trans(C.Resultado, C.Entrada{},
          C.percorrer(Con{c, t}, C.diminuir64(corpo), C.diminuir64(teto), C.Pronto{D.VInt{(alto * 256 + U32.shrn(baixo, 24n) : U32), (baixo * 256 + b : U32)}}), C.Decodificado{v},
          Equal.sym(C.Resultado,
            C.percorrer(Con{c, t}, C.diminuir64(corpo), C.diminuir64(teto), C.Pronto{D.VInt{(alto * 256 + U32.shrn(baixo, 24n) : U32), (baixo * 256 + b : U32)}}), C.Entrada{},
            R.pronto_recusa_qualquer_octeto_extra(c, t, C.diminuir64(corpo), C.diminuir64(teto), D.VInt{(alto * 256 + U32.shrn(baixo, 24n) : U32), (baixo * 256 + b : U32)})), aceito))
    case 1n+p Nil{}:
      R.entrada_nao_decodificada(v, aceito)
    case 1n+p Con{+b, +t}:
      palavra_inteira_aceita_exige_tamanho_exato(p, t, (alto * 256 + U32.shrn(baixo, 24n) : U32), (baixo * 256 + b : U32), C.diminuir64(corpo), C.diminuir64(teto), v, aceito)

def inteiro_aceito_com_formato(+bs: List<&2, U32>, +teto: B.Numero64, -v: D.Valor,
  aceito: {C.decodificar(Con{3, bs}, teto) == C.Decodificado{v} : C.Resultado},
  formato: PalavraInteiraCompleta(7n, bs)) -> P.Codificacao(v, Con{3, bs}):
  match bs:
    case Nil{}:
      L.ex_falso(P.Codificacao(v, Con{3, Nil{}}), formato)
    case Con{a0, Nil{}}:
      L.ex_falso(P.Codificacao(v, Con{3, Con{a0, Nil{}}}), formato)
    case Con{a0, Con{a1, Nil{}}}:
      L.ex_falso(P.Codificacao(v, Con{3, Con{a0, Con{a1, Nil{}}}}), formato)
    case Con{a0, Con{a1, Con{a2, Nil{}}}}:
      L.ex_falso(P.Codificacao(v, Con{3, Con{a0, Con{a1, Con{a2, Nil{}}}}}), formato)
    case Con{a0, Con{a1, Con{a2, Con{a3, Nil{}}}}}:
      L.ex_falso(P.Codificacao(v, Con{3, Con{a0, Con{a1, Con{a2, Con{a3, Nil{}}}}}}), formato)
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Nil{}}}}}}:
      L.ex_falso(P.Codificacao(v, Con{3, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Nil{}}}}}}}), formato)
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Nil{}}}}}}}:
      L.ex_falso(P.Codificacao(v, Con{3, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Nil{}}}}}}}}), formato)
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Nil{}}}}}}}}:
      L.ex_falso(P.Codificacao(v, Con{3, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Nil{}}}}}}}}}), formato)
    case Con{+a0, Con{+a1, Con{+a2, Con{+a3, Con{+a4, Con{+a5, Con{+a6, Con{+a7, Nil{}}}}}}}}}:
      aceitacao_de_inteiro_reconstroi_exatamente_os_bytes(a0, a1, a2, a3, a4, a5, a6, a7, teto, v, aceito)
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, resto}}}}}}}}}:
      L.ex_falso(P.Codificacao(v, Con{3, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, resto}}}}}}}}}}), formato)

def corpo_inteiro_aceito_e_exato(+bs: List<&2, U32>, +teto: B.Numero64, -v: D.Valor,
  entrada: R.EntradaConferida<B.nat64(B.comprimento(Con{3, bs})), Con{3, bs}, teto, v>) -> PalavraInteiraCompleta(7n, bs):
  match entrada:
    case R.Conferida{corpo, medida, cabe, octetos, percurso}:
      palavra_inteira_aceita_exige_tamanho_exato(7n, bs, 0, 0, C.diminuir64(corpo), C.diminuir64(teto), v, percurso)

law toda_aceitacao_iniciada_por_tag_inteiro_e_canonica:
  for +bs: List<&2, U32>
  for +teto: B.Numero64
  for -v: D.Valor
  for +aceito: {C.decodificar(Con{3, bs}, teto) == C.Decodificado{v} : C.Resultado}
  P.Codificacao(v, Con{3, bs})
def toda_aceitacao_iniciada_por_tag_inteiro_e_canonica(bs, teto, v, aceito):
  inteiro_aceito_com_formato(bs, teto, v, aceito,
    corpo_inteiro_aceito_e_exato(bs, teto, v,
      R.aceitacao_exige_corpo_representavel_octetos_e_limite(Con{3, bs}, teto, v, aceito)))
