# Liga o transdutor UTF-8 ao estado Conteudo REAL e a um comprimento u64
# obtido de nat64. O corpo e o teto nao sao usados como combustivel.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecUTF8.bend as U
import ./CodecContadores.bend as N
import ./CodecPercurso.bend as R

def ParcialPendente(e: C.Escalar) -> Type:
  match e:
    case C.Parcial{C.Inicio{}}:
      Empty
    case C.Parcial{C.Continua{0n, cp, minimo}}:
      Empty
    case C.Parcial{C.Continua{1n+p, cp, minimo}}:
      Unit
    case C.Caractere{cp}:
      Unit
    case C.UTFInvalido{}:
      Unit

def conferido_pendente(ok: Bool, cp: U32) -> ParcialPendente(C.escalar_conferido(ok, cp)):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      Unit{}

law completar_so_deixa_continuacao_pendente:
  for n: Nat
  for +cp: U32
  for +minimo: U32
  ParcialPendente(C.completar_utf8(n, cp, minimo))
def completar_so_deixa_continuacao_pendente(n, cp, minimo):
  match n:
    case 0n:
      conferido_pendente(U32.is_ge(cp, minimo) && B.codigo_valido(cp), cp)
    case 1n+p:
      Unit{}

law continuar_so_deixa_continuacao_pendente:
  for ok: Bool
  for n: Nat
  for cp: U32
  for minimo: U32
  for b: U32
  ParcialPendente(C.continuar_utf8(ok, n, cp, minimo, b))
def continuar_so_deixa_continuacao_pendente(ok, n, cp, minimo, b):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      completar_so_deixa_continuacao_pendente(n, (cp * 64 + b - 128 : U32), minimo)

law iniciar_so_deixa_continuacao_pendente:
  for ascii: Bool
  for dois: Bool
  for tres: Bool
  for quatro: Bool
  for b: U32
  ParcialPendente(C.iniciar_utf8(ascii, dois, tres, quatro, b))
def iniciar_so_deixa_continuacao_pendente(ascii, dois, tres, quatro, b):
  match ascii dois tres quatro:
    case True{} _ _ _:
      Unit{}
    case False{} True{} _ _:
      Unit{}
    case False{} False{} True{} _:
      Unit{}
    case False{} False{} False{} True{}:
      Unit{}
    case False{} False{} False{} False{}:
      Unit{}

law passo_so_deixa_continuacao_pendente:
  for u: C.Unicode
  for +b: U32
  ParcialPendente(C.passo_utf8(u, b))
def passo_so_deixa_continuacao_pendente(u, b):
  match u:
    case C.Inicio{}:
      iniciar_so_deixa_continuacao_pendente(U32.is_lt(b, 128), U32.is_ge(b, 194) && U32.is_le(b, 223), U32.is_ge(b, 224) && U32.is_le(b, 239), U32.is_ge(b, 240) && U32.is_le(b, 244), b)
    case C.Continua{0n, cp, minimo}:
      Unit{}
    case C.Continua{1n+p, cp, minimo}:
      continuar_so_deixa_continuacao_pendente(U32.is_ge(b, 128) && U32.is_le(b, 191), p, cp, minimo, b)

def concluir_texto(nome: Bool, pilha: C.Pilha, t: U.Texto) -> C.Maquina:
  match t:
    case U.TextoInvalido{}:
      C.Invalido{}
    case U.Lendo{C.Inicio{}, invertido}:
      C.emitir_texto(nome, String.reverse(invertido), pilha)
    case U.Lendo{C.Continua{n, cp, minimo}, invertido}:
      C.Invalido{}

law ultimo_escalar_conclui_exatamente_o_texto:
  for +e: C.Escalar
  for nome: Bool
  for q: B.Numero64
  for +invertido: String
  for +pilha: C.Pilha
  for pendente: ParcialPendente(e)
  {C.guardar_escalar(e, True{}, nome, q, invertido, pilha) == concluir_texto(nome, pilha, U.juntar(e, invertido)) : C.Maquina}
def ultimo_escalar_conclui_exatamente_o_texto(e, nome, q, invertido, pilha, pendente):
  match e:
    case C.UTFInvalido{}:
      {==}
    case C.Caractere{cp}:
      {==}
    case C.Parcial{C.Inicio{}}:
      L.ex_falso({C.Invalido{} == C.emitir_texto(nome, String.reverse(invertido), pilha) : C.Maquina}, pendente)
    case C.Parcial{C.Continua{0n, cp, minimo}}:
      {==}
    case C.Parcial{C.Continua{1n+p, cp, minimo}}:
      {==}

law executar_invalido_permanece_invalido:
  for bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  {R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.Invalido{}})) == C.Invalido{} : C.Maquina}
def executar_invalido_permanece_invalido(bs, corpo, teto):
  match bs:
    case Nil{}:
      {==}
    case Con{b, t}:
      executar_invalido_permanece_invalido(t, C.diminuir64(corpo), C.diminuir64(teto))

law texto_invalido_permanece_invalido:
  for bs: List<&2, U32>
  {U.percorrer_texto(bs, U.TextoInvalido{}) == U.TextoInvalido{} : U.Texto}
def texto_invalido_permanece_invalido(bs):
  match bs:
    case Nil{}:
      {==}
    case Con{b, t}:
      texto_invalido_permanece_invalido(t)

# Quantidade positiva; e so uma forma da lista de bytes, nao canonicidade.
def NaoVazio(bs: List<&2, U32>) -> Type:
  match bs:
    case Nil{}:
      Empty
    case Con{h, t}:
      Unit

def processar_conteudo(bs: List<&2, U32>, +q: B.Numero64,
  corpo: B.Numero64, teto: B.Numero64, nome: Bool, u: C.Unicode,
  invertido: String, pilha: C.Pilha) -> C.Maquina:
  R.maquina(R.executar(bs, R.Quadro{corpo, teto,
    C.Conteudo{nome, C.um64(q), C.diminuir64(q), u, invertido, pilha}}))

# O callback e a hipotese de inducao sobre a CAUDA estrutural, e e
# fornecido pelo teorema abaixo. Nao e uma premissa publica de soundness.
def continuar_apos_escalar(+e: C.Escalar, +bs: List<&2, U32>, +q: B.Numero64,
  +corpo: B.Numero64, +teto: B.Numero64, +nome: Bool,
  +invertido: String, +pilha: C.Pilha,
  continuar: @u: C.Unicode -> @texto: String ->
    {processar_conteudo(bs, q, corpo, teto, nome, u, texto, pilha) ==
      concluir_texto(nome, pilha, U.percorrer_texto(bs, U.Lendo{u, texto})) : C.Maquina}) ->
  {R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.guardar_escalar(e, False{}, nome, q, invertido, pilha)})) ==
    concluir_texto(nome, pilha, U.percorrer_texto(bs, U.juntar(e, invertido))) : C.Maquina}:
  match e:
    case C.UTFInvalido{}:
      %Equal.sym(U.Texto, U.percorrer_texto(bs, U.TextoInvalido{}), U.TextoInvalido{}, texto_invalido_permanece_invalido(bs)) :
        {R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.Invalido{}})) == concluir_texto(nome, pilha, _) : C.Maquina}
      executar_invalido_permanece_invalido(bs, corpo, teto)
    case C.Caractere{cp}:
      continuar(C.Inicio{}, SCon{Chr{cp}, invertido})
    case C.Parcial{u}:
      continuar(u, invertido)

law conteudo_contado_consume_exatamente_o_texto:
  for +bs: List<&2, U32>
  for +q: B.Numero64
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +nome: Bool
  for +u: C.Unicode
  for +invertido: String
  for +pilha: C.Pilha
  for positivo: NaoVazio(bs)
  for +medido: {B.nat64(B.comprimento(bs)) == Some{q} : Maybe<&2, B.Numero64>}
  {processar_conteudo(bs, q, corpo, teto, nome, u, invertido, pilha) ==
    concluir_texto(nome, pilha, U.percorrer_texto(bs, U.Lendo{u, invertido})) : C.Maquina}
def conteudo_contado_consume_exatamente_o_texto(bs, q, corpo, teto, nome, u, invertido, pilha, positivo, medido):
  match bs:
    case Nil{}:
      L.ex_falso({processar_conteudo(Nil{}, q, corpo, teto, nome, u, invertido, pilha) == concluir_texto(nome, pilha, U.Lendo{u, invertido}) : C.Maquina}, positivo)
    case Con{+b, Nil{}}:
      %F.algum_injetivo(B.Numero64, B.Numero64{0, 1}, q, medido) :
        {processar_conteudo(Con{b, Nil{}}, _, corpo, teto, nome, u, invertido, pilha) == concluir_texto(nome, pilha, U.juntar(C.passo_utf8(u, b), invertido)) : C.Maquina}
      ultimo_escalar_conclui_exatamente_o_texto(C.passo_utf8(u, b), nome, B.Numero64{0, 0}, invertido, pilha, passo_so_deixa_continuacao_pendente(u, b))
    case Con{+b, Con{+c, +resto}}:
      +t = {Con{c, resto} : List<&2, U32>}
      %Equal.sym(Bool, C.um64(q), False{}, N.um64_reflete_contagem_natural(B.comprimento(Con{b, t}), q, medido)) :
        {R.maquina(R.executar(t, R.Quadro{C.diminuir64(corpo), C.diminuir64(teto), C.guardar_escalar(C.passo_utf8(u, b), _, nome, C.diminuir64(q), invertido, pilha)})) ==
          concluir_texto(nome, pilha, U.percorrer_texto(t, U.juntar(C.passo_utf8(u, b), invertido))) : C.Maquina}
      continuar_apos_escalar(C.passo_utf8(u, b), t, C.diminuir64(q), C.diminuir64(corpo), C.diminuir64(teto), nome, invertido, pilha,
        proximo => texto => conteudo_contado_consume_exatamente_o_texto(t, C.diminuir64(q), C.diminuir64(corpo), C.diminuir64(teto), nome, proximo, texto, pilha, Unit{},
          N.comprimento_da_cauda_e_decremento_do_corpo(b, t, q, medido)))
