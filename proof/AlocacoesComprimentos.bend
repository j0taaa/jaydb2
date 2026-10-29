# Inversao dos guards REAIS antes de abrir um campo variavel do Codec.
# Vale para prefixos que ainda podem falhar depois, sem exigir aceitacao final.
# Nao declara fatos do host; a ordem dos fatos reais cabe ao runtime.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecRelaxarAritmetica.bend as A
import ./CodecRelaxarAritmeticaNat.bend as N
import ./CodecRelaxarAritmeticaWord.bend as W
import ./CodecMinimosPilha.bend as M
import ./CodecSomasMinimos.bend as S
import ./CodecLimitesSequencias.bend as Q

def em_construcao(m: C.Maquina) -> Bool:
  match m:
    case C.Invalido{}:
      False{}
    case C.Acima{}:
      False{}
    case _:
      True{}

law abertura_em_construcao_exige_conferencia_real:
  for +c: C.Conferencia
  for +f: C.Finalidade
  for +q: B.Numero64
  for +pilha: C.Pilha
  for abriu: {em_construcao(C.abrir_conferido(c, f, q, pilha)) == True{} : Bool}
  {c == C.Cabe{} : C.Conferencia}
def abertura_em_construcao_exige_conferencia_real(c, f, q, pilha, abriu):
  match c:
    case C.Cabe{}:
      {==}
    case C.Curto{}:
      F.absurdo_booleano({C.Curto{} == C.Cabe{} : C.Conferencia}, abriu)
    case C.Grande{}:
      F.absurdo_booleano({C.Grande{} == C.Cabe{} : C.Conferencia}, abriu)

law parcela_nao_excede_soma:
  for +n: Nat
  for +r: Nat
  {Nat.is_le(n, Nat.add(n, r)) == True{} : Bool}
def parcela_nao_excede_soma(n, r):
  match n:
    case 0n:
      N.zero_nao_maior(r)
    case 1n+p:
      parcela_nao_excede_soma(p, r)

law quantidade_nao_excede_minimo_do_campo:
  for +f: C.Finalidade
  for +n: Nat
  {Nat.is_le(n, S.minimo_campo_natural(f, n)) == True{} : Bool}
def quantidade_nao_excede_minimo_do_campo(f, n):
  match f:
    case C.ContaRegistro{}:
      parcela_nao_excede_soma(n, Nat.mul(10n, n))
    case C.Inteiro{}:
      Q.limite_reflexivo(n)
    case C.Texto{}:
      Q.limite_reflexivo(n)
    case C.NomeTexto{}:
      Q.limite_reflexivo(n)
    case C.ContaLista{}:
      Q.limite_reflexivo(n)

def quantidade_menor_que_reserva(+f: C.Finalidade, +q: B.Numero64, +pilha: C.Pilha,
  quantidade: W.NumeroMedido<q>, reserva: M.MinimoExato<pilha>) ->
  N.OrdemNatural<Some{q}, C.somar_opcionais(C.minimo_campo(f, q), C.minimo_pilha(pilha))>:
  match quantidade reserva:
    case W.NumeroMedido{+n, +medido} M.MinimoExato{+r, exato}:
      N.OrdemNatural{n, Nat.add(S.minimo_campo_natural(f, n), r),
        Equal.sym(Maybe<&2, B.Numero64>, B.nat64(n), Some{q}, medido),
        S.minimo_campo_com_pilha_nat64_exato(f, n, r, q, pilha, medido, exato),
        N.ordem_transitiva(n, S.minimo_campo_natural(f, n), Nat.add(S.minimo_campo_natural(f, n), r),
          quantidade_nao_excede_minimo_do_campo(f, n), parcela_nao_excede_soma(S.minimo_campo_natural(f, n), r))}

# Nenhuma medida Nat ou representabilidade de minimo e uma premissa externa.
# Elas sao obtidas de todos os u64 e frames reais, inclusive no overflow.
law conferencia_composta_limita_a_quantidade_declarada:
  for +f: C.Finalidade
  for +q: B.Numero64
  for +pilha: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for cabe: {C.conferir(C.somar_opcionais(C.minimo_campo(f, q), C.minimo_pilha(pilha)), corpo, teto) == C.Cabe{} : C.Conferencia}
  {C.conferir(Some{q}, corpo, teto) == C.Cabe{} : C.Conferencia}
def conferencia_composta_limita_a_quantidade_declarada(f, q, pilha, corpo, teto, cabe):
  A.conferir_ordem_medida(Some{q}, C.somar_opcionais(C.minimo_campo(f, q), C.minimo_pilha(pilha)), corpo, teto,
    quantidade_menor_que_reserva(f, q, pilha, W.medir_numero(q),
      M.todos_os_minimos_de_pilha_medida_sao_exatos(pilha, A.medir_pilha(pilha))),
    W.medir_numero(corpo), W.medir_numero(teto), cabe)

def inverter_limites(-q: B.Numero64, -corpo: B.Numero64, -teto: B.Numero64,
  limites: L.E<{C.menor_igual64(q, teto) == True{} : Bool}, {C.menor_igual64(q, corpo) == True{} : Bool}>) ->
  L.E<{C.menor_igual64(q, corpo) == True{} : Bool}, {C.menor_igual64(q, teto) == True{} : Bool}>:
  match limites:
    case L.Ambos{lt, lc}:
      L.Ambos{lc, lt}

law conferencia_composta_exige_ambos_limites:
  for +f: C.Finalidade
  for +q: B.Numero64
  for +pilha: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for cabe: {C.conferir(C.somar_opcionais(C.minimo_campo(f, q), C.minimo_pilha(pilha)), corpo, teto) == C.Cabe{} : C.Conferencia}
  L.E<{C.menor_igual64(q, corpo) == True{} : Bool}, {C.menor_igual64(q, teto) == True{} : Bool}>
def conferencia_composta_exige_ambos_limites(f, q, pilha, corpo, teto, cabe):
  inverter_limites(q, corpo, teto,
    N.conferir_casos_exige_limites(C.menor_igual64(q, teto), C.menor_igual64(q, corpo),
      conferencia_composta_limita_a_quantidade_declarada(f, q, pilha, corpo, teto, cabe)))

# Exclui somente o ramo Inteiro, que usa oito bytes fixos, sem aridade u64.
def Variavel(f: C.Finalidade) -> Type:
  match f:
    case C.Inteiro{}:
      Empty
    case _:
      Unit

law concluir_palavra_variavel_em_construcao_foi_conferido:
  for +f: C.Finalidade
  for +alto: U32
  for +baixo: U32
  for +pilha: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for variavel: Variavel(f)
  for abriu: {em_construcao(C.concluir_palavra(f, alto, baixo, pilha, corpo, teto)) == True{} : Bool}
  {C.conferir(C.somar_opcionais(C.minimo_campo(f, B.Numero64{alto, baixo}), C.minimo_pilha(pilha)), corpo, teto) == C.Cabe{} : C.Conferencia}
def concluir_palavra_variavel_em_construcao_foi_conferido(f, alto, baixo, pilha, corpo, teto, variavel, abriu):
  match f:
    case C.Inteiro{}:
      L.ex_falso({C.conferir(C.somar_opcionais(C.minimo_campo(C.Inteiro{}, B.Numero64{alto, baixo}), C.minimo_pilha(pilha)), corpo, teto) == C.Cabe{} : C.Conferencia}, variavel)
    case C.Texto{}:
      abertura_em_construcao_exige_conferencia_real(C.conferir(C.somar_opcionais(C.minimo_campo(C.Texto{}, B.Numero64{alto, baixo}), C.minimo_pilha(pilha)), corpo, teto), C.Texto{}, B.Numero64{alto, baixo}, pilha, abriu)
    case C.NomeTexto{}:
      abertura_em_construcao_exige_conferencia_real(C.conferir(C.somar_opcionais(C.minimo_campo(C.NomeTexto{}, B.Numero64{alto, baixo}), C.minimo_pilha(pilha)), corpo, teto), C.NomeTexto{}, B.Numero64{alto, baixo}, pilha, abriu)
    case C.ContaLista{}:
      abertura_em_construcao_exige_conferencia_real(C.conferir(C.somar_opcionais(C.minimo_campo(C.ContaLista{}, B.Numero64{alto, baixo}), C.minimo_pilha(pilha)), corpo, teto), C.ContaLista{}, B.Numero64{alto, baixo}, pilha, abriu)
    case C.ContaRegistro{}:
      abertura_em_construcao_exige_conferencia_real(C.conferir(C.somar_opcionais(C.minimo_campo(C.ContaRegistro{}, B.Numero64{alto, baixo}), C.minimo_pilha(pilha)), corpo, teto), C.ContaRegistro{}, B.Numero64{alto, baixo}, pilha, abriu)

law abertura_variavel_real_respeita_corpo_e_teto:
  for +f: C.Finalidade
  for +alto: U32
  for +baixo: U32
  for +pilha: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for variavel: Variavel(f)
  for abriu: {em_construcao(C.concluir_palavra(f, alto, baixo, pilha, corpo, teto)) == True{} : Bool}
  L.E<{C.menor_igual64(B.Numero64{alto, baixo}, corpo) == True{} : Bool},
    {C.menor_igual64(B.Numero64{alto, baixo}, teto) == True{} : Bool}>
def abertura_variavel_real_respeita_corpo_e_teto(f, alto, baixo, pilha, corpo, teto, variavel, abriu):
  conferencia_composta_exige_ambos_limites(f, B.Numero64{alto, baixo}, pilha, corpo, teto,
    concluir_palavra_variavel_em_construcao_foi_conferido(f, alto, baixo, pilha, corpo, teto, variavel, abriu))
