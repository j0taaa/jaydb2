# Soundness publica geral das tres tags unitarias, sem supor tamanho nem
# valor de retorno. A recusa de qualquer byte extra e extraida da execucao.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecPercurso.bend as R
import ./CodecMinimos.bend as M
import ./CodecConteudo.bend as G
import ./CodecTamanhos.bend as T
import ./CodecAridades.bend as A

type AtomoUnitario is Data:
  Ausencia{}
  Booleano{valor: Bool}

def octeto(a: AtomoUnitario) -> U32:
  match a:
    case Ausencia{}:
      0
    case Booleano{False{}}:
      1
    case Booleano{True{}}:
      2

def valor(a: AtomoUnitario) -> D.Valor:
  match a:
    case Ausencia{}:
      D.VAusente{}
    case Booleano{b}:
      D.VBool{b}

def valor_resultado(r: C.Resultado) -> D.Valor:
  match r:
    case C.Decodificado{v}:
      v
    case _:
      D.VAusente{}

law pronto_aceito_exige_sufixo_vazio_e_valor_exato:
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +w: D.Valor
  for -v: D.Valor
  for aceito: {C.percorrer(bs, corpo, teto, C.Pronto{w}) == C.Decodificado{v} : C.Resultado}
  L.E<{bs == Nil{} : List<&2, U32>}, {v == w : D.Valor}>
def pronto_aceito_exige_sufixo_vazio_e_valor_exato(bs, corpo, teto, w, v, aceito):
  match bs:
    case Nil{}:
      L.Ambos{{==}, Equal.sym(D.Valor, w, v, Equal.cong(C.Resultado, D.Valor, r => valor_resultado(r), C.Decodificado{w}, C.Decodificado{v}, aceito))}
    case Con{+b, +t}:
      L.ex_falso(L.E<{Con{b, t} == Nil{} : List<&2, U32>}, {v == w : D.Valor}>,
        R.entrada_nao_decodificada(v, Equal.trans(C.Resultado,
          C.Entrada{}, C.percorrer(Con{b, t}, corpo, teto, C.Pronto{w}), C.Decodificado{v},
          Equal.sym(C.Resultado, C.percorrer(Con{b, t}, corpo, teto, C.Pronto{w}), C.Entrada{}, R.pronto_recusa_qualquer_octeto_extra(b, t, corpo, teto, w)), aceito)))

law atomo_unitario_emite_exatamente_o_valor:
  for +a: AtomoUnitario
  for +pilha: C.Pilha
  for corpo: B.Numero64
  for teto: B.Numero64
  {C.passo(C.Tag{pilha}, octeto(a), corpo, teto) == C.emitir(pilha, valor(a)) : C.Maquina}
def atomo_unitario_emite_exatamente_o_valor(a, pilha, corpo, teto):
  match a:
    case Ausencia{}:
      {==}
    case Booleano{False{}}:
      {==}
    case Booleano{True{}}:
      {==}

law atomo_unitario_tem_codificacao_exata:
  for +a: AtomoUnitario
  P.Codificacao(valor(a), [octeto(a)])
def atomo_unitario_tem_codificacao_exata(a):
  match a:
    case Ausencia{}:
      {==}
    case Booleano{False{}}:
      {==}
    case Booleano{True{}}:
      {==}

def atomo_com_percurso(+a: AtomoUnitario, +bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64, -v: D.Valor,
  percurso: {C.percorrer(Con{octeto(a), bs}, corpo, teto, C.Tag{C.Raiz{}}) == C.Decodificado{v} : C.Resultado}) -> P.Codificacao(v, Con{octeto(a), bs}):
  F.com_par(P.Codificacao(v, Con{octeto(a), bs}), {bs == Nil{} : List<&2, U32>}, {v == valor(a) : D.Valor},
    pronto_aceito_exige_sufixo_vazio_e_valor_exato(bs, C.diminuir64(corpo), C.diminuir64(teto), valor(a), v,
      (%atomo_unitario_emite_exatamente_o_valor(a, C.Raiz{}, C.diminuir64(corpo), C.diminuir64(teto)) :
        {C.percorrer(bs, C.diminuir64(corpo), C.diminuir64(teto), _) == C.Decodificado{v} : C.Resultado}
        percurso)),
    fim => igual =>
      (%Equal.sym(List<&2, U32>, bs, Nil{}, fim) : P.Codificacao(v, Con{octeto(a), _})
        %Equal.sym(D.Valor, v, valor(a), igual) : P.Codificacao(_, [octeto(a)])
        atomo_unitario_tem_codificacao_exata(a)))

def atomo_com_entrada(+a: AtomoUnitario, +bs: List<&2, U32>, +teto: B.Numero64, -v: D.Valor,
  entrada: R.EntradaConferida<B.nat64(B.comprimento(Con{octeto(a), bs})), Con{octeto(a), bs}, teto, v>) -> P.Codificacao(v, Con{octeto(a), bs}):
  match entrada:
    case R.Conferida{corpo, medida, cabe, octetos, percurso}:
      atomo_com_percurso(a, bs, corpo, teto, v, percurso)

law toda_aceitacao_de_atomo_unitario_e_canonica:
  for +a: AtomoUnitario
  for +bs: List<&2, U32>
  for +teto: B.Numero64
  for -v: D.Valor
  for aceito: {C.decodificar(Con{octeto(a), bs}, teto) == C.Decodificado{v} : C.Resultado}
  P.Codificacao(v, Con{octeto(a), bs})
def toda_aceitacao_de_atomo_unitario_e_canonica(a, bs, teto, v, aceito):
  atomo_com_entrada(a, bs, teto, v, R.aceitacao_exige_corpo_representavel_octetos_e_limite(Con{octeto(a), bs}, teto, v, aceito))

law entrada_vazia_e_recusada:
  for +teto: B.Numero64
  {C.decodificar(Nil{}, teto) == C.Entrada{} : C.Resultado}
def entrada_vazia_e_recusada(teto):
  %Equal.sym(Bool, C.menor_igual64(B.Numero64{0, 0}, teto), True{}, M.zero64_nao_maior(teto)) :
    {C.decodificar_tamanho(_, Nil{}, B.Numero64{0, 0}, teto) == C.Entrada{} : C.Resultado}
  {==}

law qualquer_aceitacao_exige_ao_menos_uma_tag:
  for +bs: List<&2, U32>
  for +teto: B.Numero64
  for -v: D.Valor
  for aceito: {C.decodificar(bs, teto) == C.Decodificado{v} : C.Resultado}
  G.NaoVazio(bs)
def qualquer_aceitacao_exige_ao_menos_uma_tag(bs, teto, v, aceito):
  match bs:
    case Nil{}:
      R.entrada_nao_decodificada(v,
        Equal.trans(C.Resultado, C.Entrada{}, C.decodificar(Nil{}, teto), C.Decodificado{v},
          Equal.sym(C.Resultado, C.decodificar(Nil{}, teto), C.Entrada{}, entrada_vazia_e_recusada(teto)), aceito))
    case Con{b, t}:
      Unit{}

law qualquer_aceitacao_exige_um_octeto:
  for +bs: List<&2, U32>
  for +teto: B.Numero64
  for -v: D.Valor
  for aceito: {C.decodificar(bs, teto) == C.Decodificado{v} : C.Resultado}
  {Nat.is_le(1n, B.comprimento(bs)) == True{} : Bool}
def qualquer_aceitacao_exige_um_octeto(bs, teto, v, aceito):
  T.bytes_nao_vazios_tem_pelo_menos_um_octeto(bs, qualquer_aceitacao_exige_ao_menos_uma_tag(bs, teto, v, aceito))

# A mesma propriedade vale no inicio de um filho com pilha arbitraria.
law tag_que_termina_pronta_consume_prefixo_positivo:
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +pilha: C.Pilha
  for -v: D.Valor
  for pronto: {R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.Tag{pilha}})) == C.Pronto{v} : C.Maquina}
  G.NaoVazio(bs)
def tag_que_termina_pronta_consume_prefixo_positivo(bs, corpo, teto, pilha, v, pronto):
  match bs:
    case Nil{}:
      A.tag_nao_e_pronto(pilha, v, pronto)
    case Con{b, t}:
      Unit{}

law tags_naturais_acima_de_seis_sao_recusadas:
  for n: Nat
  for bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for pilha: C.Pilha
  {C.percorrer(bs, corpo, teto, C.ler_tag(7n+n, pilha)) == C.Entrada{} : C.Resultado}
def tags_naturais_acima_de_seis_sao_recusadas(n, bs, corpo, teto, pilha):
  R.invalido_absorve_todo_sufixo(bs, corpo, teto)
