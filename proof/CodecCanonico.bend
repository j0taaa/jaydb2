# Ligacao geral entre os acumuladores invertidos do parser e o encoder
# original: ordem exata dos bytes, cardinalidade e propagacao de None.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecEstruturas.bend as E

law concatenacao_associativa:
  for xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +zs: List<&2, U32>
  {B.concatenar(B.concatenar(xs, ys), zs) == B.concatenar(xs, B.concatenar(ys, zs)) : List<&2, U32>}
def concatenacao_associativa(xs, ys, zs):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, resto => Con{h, resto},
        B.concatenar(B.concatenar(t, ys), zs), B.concatenar(t, B.concatenar(ys, zs)), concatenacao_associativa(t, ys, zs))

law concatenacao_opcional_associativa:
  for a: Maybe<&2, List<&2, U32>>
  for b: Maybe<&2, List<&2, U32>>
  for c: Maybe<&2, List<&2, U32>>
  {P.concatenar_opcional(P.concatenar_opcional(a, b), c) ==
    P.concatenar_opcional(a, P.concatenar_opcional(b, c)) : Maybe<&2, List<&2, U32>>}
def concatenacao_opcional_associativa(a, b, c):
  match a b c:
    case Some{xs} Some{ys} Some{zs}:
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, resto => Some{resto},
        B.concatenar(B.concatenar(xs, ys), zs), B.concatenar(xs, B.concatenar(ys, zs)), concatenacao_associativa(xs, ys, zs))
    case None{} _ _:
      {==}
    case Some{xs} None{} _:
      {==}
    case Some{xs} Some{ys} None{}:
      {==}

law soma_sucessor_direito:
  for a: Nat
  for +b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}
def soma_sucessor_direito(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 1n+b), 1n+Nat.add(p, b), soma_sucessor_direito(p, b))

def contar_valores(xs: List<&2, D.Valor>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+contar_valores(t)

def contar_campos(xs: List<&2, D.Campo>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+contar_campos(t)

# Conteudo em ordem de leitura, mesmo quando o buffer esta invertido.
def conteudo_valores(xs: List<&2, D.Valor>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case Con{h, t}:
      P.concatenar_opcional(conteudo_valores(t), P.finalizar(P.codificar_parcial(h)))

def conteudo_campo(campo: D.Campo) -> Maybe<&2, List<&2, U32>>:
  D.Campo{n, v} = campo
  P.concatenar_opcional(P.texto(n), P.finalizar(P.codificar_parcial(v)))

def conteudo_campos(xs: List<&2, D.Campo>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case Con{h, t}:
      P.concatenar_opcional(conteudo_campos(t), conteudo_campo(h))

def lista_bytes(n: Nat, bs: Maybe<&2, List<&2, U32>>) -> P.Parcial:
  match bs:
    case None{}:
      P.Impossivel{}
    case Some{xs}:
      P.Lista{n, xs}

def registro_bytes(n: Nat, bs: Maybe<&2, List<&2, U32>>) -> P.Parcial:
  match bs:
    case None{}:
      P.Impossivel{}
    case Some{xs}:
      P.Registro{n, xs}

law lista_casos_concatena_bytes:
  for h: Maybe<&2, List<&2, U32>>
  for n: Nat
  for bs: Maybe<&2, List<&2, U32>>
  {P.lista_casos(h, lista_bytes(n, bs)) == lista_bytes(1n+n, P.concatenar_opcional(h, bs)) : P.Parcial}
def lista_casos_concatena_bytes(h, n, bs):
  match h bs:
    case None{} None{}:
      {==}
    case None{} Some{xs}:
      {==}
    case Some{xs} None{}:
      {==}
    case Some{xs} Some{ys}:
      {==}

law registro_casos_concatena_bytes:
  for nome: Maybe<&2, List<&2, U32>>
  for valor: Maybe<&2, List<&2, U32>>
  for n: Nat
  for bs: Maybe<&2, List<&2, U32>>
  {P.registro_casos(nome, valor, registro_bytes(n, bs)) ==
    registro_bytes(1n+n, P.concatenar_opcional(P.concatenar_opcional(nome, valor), bs)) : P.Parcial}
def registro_casos_concatena_bytes(nome, valor, n, bs):
  match nome valor bs:
    case Some{xs} Some{ys} Some{zs}:
      Equal.cong(List<&2, U32>, P.Parcial, resto => P.Registro{1n+n, resto},
        B.concatenar(xs, B.concatenar(ys, zs)), B.concatenar(B.concatenar(xs, ys), zs),
        Equal.sym(List<&2, U32>, B.concatenar(B.concatenar(xs, ys), zs), B.concatenar(xs, B.concatenar(ys, zs)), concatenacao_associativa(xs, ys, zs)))
    case None{} None{} _:
      {==}
    case None{} Some{ys} _:
      {==}
    case Some{xs} None{} _:
      {==}
    case Some{xs} Some{ys} None{}:
      {==}

law montagem_lista_preserva_bytes_e_quantidade:
  for +xs: List<&2, D.Valor>
  for +acc: D.Valor
  for +n: Nat
  for +bs: Maybe<&2, List<&2, U32>>
  for parcial: {P.codificar_parcial(acc) == lista_bytes(n, bs) : P.Parcial}
  {P.codificar_parcial(C.montar_lista(xs, acc)) ==
    lista_bytes(Nat.add(contar_valores(xs), n), P.concatenar_opcional(conteudo_valores(xs), bs)) : P.Parcial}
def montagem_lista_preserva_bytes_e_quantidade(xs, acc, n, bs, parcial):
  match xs:
    case Nil{}:
      match bs:
        case None{}:
          parcial
        case Some{bytes}:
          parcial
    case Con{+h, +t}:
      passo = Equal.trans(P.Parcial, P.codificar_parcial(D.VLista{h, acc}),
        P.lista_casos(P.finalizar(P.codificar_parcial(h)), lista_bytes(n, bs)),
        lista_bytes(1n+n, P.concatenar_opcional(P.finalizar(P.codificar_parcial(h)), bs)),
        Equal.cong(P.Parcial, P.Parcial, p => P.lista_casos(P.finalizar(P.codificar_parcial(h)), p),
          P.codificar_parcial(acc), lista_bytes(n, bs), parcial),
        lista_casos_concatena_bytes(P.finalizar(P.codificar_parcial(h)), n, bs))
      %soma_sucessor_direito(contar_valores(t), n) :
        {P.codificar_parcial(C.montar_lista(t, D.VLista{h, acc})) == lista_bytes(_, P.concatenar_opcional(P.concatenar_opcional(conteudo_valores(t), P.finalizar(P.codificar_parcial(h))), bs)) : P.Parcial}
      %Equal.sym(Maybe<&2, List<&2, U32>>,
        P.concatenar_opcional(P.concatenar_opcional(conteudo_valores(t), P.finalizar(P.codificar_parcial(h))), bs),
        P.concatenar_opcional(conteudo_valores(t), P.concatenar_opcional(P.finalizar(P.codificar_parcial(h)), bs)),
        concatenacao_opcional_associativa(conteudo_valores(t), P.finalizar(P.codificar_parcial(h)), bs)) :
        {P.codificar_parcial(C.montar_lista(t, D.VLista{h, acc})) == lista_bytes(Nat.add(contar_valores(t), 1n+n), _) : P.Parcial}
      montagem_lista_preserva_bytes_e_quantidade(t, D.VLista{h, acc}, 1n+n, P.concatenar_opcional(P.finalizar(P.codificar_parcial(h)), bs), passo)

law montagem_registro_preserva_bytes_e_quantidade:
  for +xs: List<&2, D.Campo>
  for +acc: D.Valor
  for +n: Nat
  for +bs: Maybe<&2, List<&2, U32>>
  for parcial: {P.codificar_parcial(acc) == registro_bytes(n, bs) : P.Parcial}
  {P.codificar_parcial(C.montar_registro(xs, acc)) ==
    registro_bytes(Nat.add(contar_campos(xs), n), P.concatenar_opcional(conteudo_campos(xs), bs)) : P.Parcial}
def montagem_registro_preserva_bytes_e_quantidade(xs, acc, n, bs, parcial):
  match xs:
    case Nil{}:
      match bs:
        case None{}:
          parcial
        case Some{bytes}:
          parcial
    case Con{D.Campo{+nome, +v}, +t}:
      passo = Equal.trans(P.Parcial, P.codificar_parcial(D.VRegistro{nome, v, acc}),
        P.registro_casos(P.texto(nome), P.finalizar(P.codificar_parcial(v)), registro_bytes(n, bs)),
        registro_bytes(1n+n, P.concatenar_opcional(conteudo_campo(D.Campo{nome, v}), bs)),
        Equal.cong(P.Parcial, P.Parcial, p => P.registro_casos(P.texto(nome), P.finalizar(P.codificar_parcial(v)), p),
          P.codificar_parcial(acc), registro_bytes(n, bs), parcial),
        registro_casos_concatena_bytes(P.texto(nome), P.finalizar(P.codificar_parcial(v)), n, bs))
      %soma_sucessor_direito(contar_campos(t), n) :
        {P.codificar_parcial(C.montar_registro(t, D.VRegistro{nome, v, acc})) == registro_bytes(_, P.concatenar_opcional(P.concatenar_opcional(conteudo_campos(t), conteudo_campo(D.Campo{nome, v})), bs)) : P.Parcial}
      %Equal.sym(Maybe<&2, List<&2, U32>>,
        P.concatenar_opcional(P.concatenar_opcional(conteudo_campos(t), conteudo_campo(D.Campo{nome, v})), bs),
        P.concatenar_opcional(conteudo_campos(t), P.concatenar_opcional(conteudo_campo(D.Campo{nome, v}), bs)),
        concatenacao_opcional_associativa(conteudo_campos(t), conteudo_campo(D.Campo{nome, v}), bs)) :
        {P.codificar_parcial(C.montar_registro(t, D.VRegistro{nome, v, acc})) == registro_bytes(Nat.add(contar_campos(t), 1n+n), _) : P.Parcial}
      montagem_registro_preserva_bytes_e_quantidade(t, D.VRegistro{nome, v, acc}, 1n+n, P.concatenar_opcional(conteudo_campo(D.Campo{nome, v}), bs), passo)

law valor_valido_libera_codificacao:
  for +v: D.Valor
  for valido: {D.valor_valido(v) == True{} : Bool}
  {P.codificar(v) == P.finalizar(P.codificar_parcial(v)) : Maybe<&2, List<&2, U32>>}
def valor_valido_libera_codificacao(v, valido):
  %Equal.sym(Bool, D.valor_valido(v), True{}, valido) :
    {P.codificar_casos(_, P.finalizar(P.codificar_parcial(v))) == P.finalizar(P.codificar_parcial(v)) : Maybe<&2, List<&2, U32>>}
  {==}

law lista_montada_tem_codificacao_exata:
  for +xs: List<&2, D.Valor>
  for elementos: E.ValoresValidos(xs)
  {P.codificar(C.montar_lista(xs, D.VListaVazia{})) ==
    P.finalizar(lista_bytes(Nat.add(contar_valores(xs), 0n), P.concatenar_opcional(conteudo_valores(xs), Some{Nil{}}))) : Maybe<&2, List<&2, U32>>}
def lista_montada_tem_codificacao_exata(xs, elementos):
  Equal.trans(Maybe<&2, List<&2, U32>>, P.codificar(C.montar_lista(xs, D.VListaVazia{})),
    P.finalizar(P.codificar_parcial(C.montar_lista(xs, D.VListaVazia{}))),
    P.finalizar(lista_bytes(Nat.add(contar_valores(xs), 0n), P.concatenar_opcional(conteudo_valores(xs), Some{Nil{}}))),
    valor_valido_libera_codificacao(C.montar_lista(xs, D.VListaVazia{}), E.montar_lista_preserva_validade(xs, D.VListaVazia{}, elementos, {==}, {==})),
    Equal.cong(P.Parcial, Maybe<&2, List<&2, U32>>, p => P.finalizar(p),
      P.codificar_parcial(C.montar_lista(xs, D.VListaVazia{})),
      lista_bytes(Nat.add(contar_valores(xs), 0n), P.concatenar_opcional(conteudo_valores(xs), Some{Nil{}})),
      montagem_lista_preserva_bytes_e_quantidade(xs, D.VListaVazia{}, 0n, Some{Nil{}}, {==})))

law registro_montado_tem_codificacao_exata:
  for +xs: List<&2, D.Campo>
  for campos: E.CamposInvertidos(xs)
  {P.codificar(C.montar_registro(xs, D.VRegistroVazio{})) ==
    P.finalizar(registro_bytes(Nat.add(contar_campos(xs), 0n), P.concatenar_opcional(conteudo_campos(xs), Some{Nil{}}))) : Maybe<&2, List<&2, U32>>}
def registro_montado_tem_codificacao_exata(xs, campos):
  Equal.trans(Maybe<&2, List<&2, U32>>, P.codificar(C.montar_registro(xs, D.VRegistroVazio{})),
    P.finalizar(P.codificar_parcial(C.montar_registro(xs, D.VRegistroVazio{}))),
    P.finalizar(registro_bytes(Nat.add(contar_campos(xs), 0n), P.concatenar_opcional(conteudo_campos(xs), Some{Nil{}}))),
    valor_valido_libera_codificacao(C.montar_registro(xs, D.VRegistroVazio{}), E.montar_registro_preserva_validade(xs, campos)),
    Equal.cong(P.Parcial, Maybe<&2, List<&2, U32>>, p => P.finalizar(p),
      P.codificar_parcial(C.montar_registro(xs, D.VRegistroVazio{})),
      registro_bytes(Nat.add(contar_campos(xs), 0n), P.concatenar_opcional(conteudo_campos(xs), Some{Nil{}})),
      montagem_registro_preserva_bytes_e_quantidade(xs, D.VRegistroVazio{}, 0n, Some{Nil{}}, {==})))
