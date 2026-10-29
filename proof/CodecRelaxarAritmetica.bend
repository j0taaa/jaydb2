# Retirar uma pilha externa relaxa o guard real do Codec, para todo u64.
# Os minimos podem transbordar; sua representabilidade vem apenas de Cabe.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./CodecAceitacaoPilha.bend as J
import ./CodecMinimosPilha.bend as M
import ./CodecRelaxarAritmeticaWord.bend as W
import ./CodecRelaxarAritmeticaNat.bend as A

def medir_contador(-q: B.Numero64, medida: W.NumeroMedido<q>) -> M.ContadorMedido<q>:
  match medida:
    case W.NumeroMedido{n, medido}:
      M.ContadorMedido{n, medido}

def medir_pilha(+p: C.Pilha) -> M.MedidasPilha(p):
  match p:
    case C.Raiz{}:
      Unit{}
    case C.Lista{u, +q, xs, +pai}:
      L.Ambos{medir_contador(q, W.medir_numero(q)), medir_pilha(pai)}
    case C.Campo{u, +q, nome, xs, +pai}:
      L.Ambos{medir_contador(q, W.medir_numero(q)), medir_pilha(pai)}
    case C.Nome{u, +q, anterior, xs, +pai}:
      L.Ambos{medir_contador(q, W.medir_numero(q)), medir_pilha(pai)}

def minimos_campo_ligados(+f: C.Finalidade, +q: B.Numero64, +p: C.Pilha, +fora: C.Pilha,
  medida: W.NumeroMedido<q>) ->
  A.OrdemNatural<C.somar_opcionais(C.minimo_campo(f, q), C.minimo_pilha(p)),
    C.somar_opcionais(C.minimo_campo(f, q), C.minimo_pilha(J.ligar_pilha(p, fora)))>:
  match medida:
    case W.NumeroMedido{+n, medido}:
      A.somar_a_ordem(C.minimo_campo(f, q), Nat.mul(M.fator_campo(f), n),
        C.minimo_pilha(p), C.minimo_pilha(J.ligar_pilha(p, fora)),
        M.todos_os_minimos_de_campo_medido_sao_exatos(f, n, q, medido),
        A.minimos_ligados_naturais(p, fora, medir_pilha(p), medir_pilha(fora)))

def conferir_ordem_medida(+a: Maybe<&2, B.Numero64>, +b: Maybe<&2, B.Numero64>,
  +corpo: B.Numero64, +teto: B.Numero64, h: A.OrdemNatural<a, b>,
  medida_corpo: W.NumeroMedido<corpo>, medida_teto: W.NumeroMedido<teto>,
  cabe: {C.conferir(b, corpo, teto) == C.Cabe{} : C.Conferencia}) ->
  {C.conferir(a, corpo, teto) == C.Cabe{} : C.Conferencia}:
  match h medida_corpo medida_teto:
    case A.OrdemNatural{+n, +m, ea, eb, le} W.NumeroMedido{+c, mc} W.NumeroMedido{+t, mt}:
      %Equal.sym(Maybe<&2, B.Numero64>, a, B.nat64(n), ea) :
        {C.conferir(_, corpo, teto) == C.Cabe{} : C.Conferencia}
      A.conferir_natural_menor(n, m, c, t, corpo, teto, mc, mt, le,
        (%eb : {C.conferir(_, corpo, teto) == C.Cabe{} : C.Conferencia}
          cabe))

# Interface sem medidas nem hipoteses de representabilidade adicionais.
law conferir_sem_pilha_externa:
  for +f: C.Finalidade
  for +q: B.Numero64
  for +p: C.Pilha
  for +fora: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for cabe: {C.conferir(C.somar_opcionais(C.minimo_campo(f, q), C.minimo_pilha(J.ligar_pilha(p, fora))), corpo, teto) == C.Cabe{} : C.Conferencia}
  {C.conferir(C.somar_opcionais(C.minimo_campo(f, q), C.minimo_pilha(p)), corpo, teto) == C.Cabe{} : C.Conferencia}
def conferir_sem_pilha_externa(f, q, p, fora, corpo, teto, cabe):
  conferir_ordem_medida(C.somar_opcionais(C.minimo_campo(f, q), C.minimo_pilha(p)),
    C.somar_opcionais(C.minimo_campo(f, q), C.minimo_pilha(J.ligar_pilha(p, fora))), corpo, teto,
    minimos_campo_ligados(f, q, p, fora, W.medir_numero(q)),
    W.medir_numero(corpo), W.medir_numero(teto), cabe)
