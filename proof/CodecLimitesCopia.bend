# Duplicacao construtiva das provas estruturais usadas pela completude.
# So as igualdades sao copiadas diretamente; as conjuncoes sao reconstruidas.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Protocolo.bend as P
import ../contrato/Logica.bend as L
import ./Fundamentos.bend as F
import ./CodecLimitesSequencias.bend as S
import ./CodecLimitesPilha.bend as Q
import ../src/Codec.bend as C

law duplicar_valores_canonicos:
  for +xs: List<&2, S.ValorSegmentado>
  for canonicos: S.ValoresCanonicos(xs)
  L.E<S.ValoresCanonicos(xs), S.ValoresCanonicos(xs)>
def duplicar_valores_canonicos(xs, canonicos):
  match xs:
    case Nil{}:
      L.Ambos{Unit{}, Unit{}}
    case Con{S.ValorSegmentado{+v, +bs}, +t}:
      match canonicos:
        case L.Ambos{cabeca, cauda}:
          +codificado = {cabeca : {P.codificar(v) == Some{bs} : Maybe<&2, List<&2, U32>>}}
          F.com_par(L.E<S.ValoresCanonicos(xs), S.ValoresCanonicos(xs)>, S.ValoresCanonicos(t), S.ValoresCanonicos(t),
            duplicar_valores_canonicos(t, cauda),
            esquerda => direita => L.Ambos{L.Ambos{codificado, esquerda}, L.Ambos{codificado, direita}})

law duplicar_campos_canonicos:
  for +xs: List<&2, S.CampoSegmentado>
  for canonicos: S.CamposCanonicos(xs)
  L.E<S.CamposCanonicos(xs), S.CamposCanonicos(xs)>
def duplicar_campos_canonicos(xs, canonicos):
  match xs:
    case Nil{}:
      L.Ambos{Unit{}, Unit{}}
    case Con{S.CampoSegmentado{+n, +v, +nb, +vb}, +t}:
      match canonicos:
        case L.Ambos{+nome, L.Ambos{+texto, L.Ambos{valor, cauda}}}:
          +codificado = {valor : {P.codificar(v) == Some{vb} : Maybe<&2, List<&2, U32>>}}
          F.com_par(L.E<S.CamposCanonicos(xs), S.CamposCanonicos(xs)>, S.CamposCanonicos(t), S.CamposCanonicos(t),
            duplicar_campos_canonicos(t, cauda),
            esquerda => direita => L.Ambos{
              L.Ambos{nome, L.Ambos{texto, L.Ambos{codificado, esquerda}}},
              L.Ambos{nome, L.Ambos{texto, L.Ambos{codificado, direita}}}})

law duplicar_plano_canonico:
  for +pilha: C.Pilha
  for +plano: Q.Plano
  for canonico: Q.PlanoCanonico(pilha, plano)
  L.E<Q.PlanoCanonico(pilha, plano), Q.PlanoCanonico(pilha, plano)>
def duplicar_plano_canonico(pilha, plano, canonico):
  match pilha plano:
    case C.Raiz{} Q.Fim{}:
      L.Ambos{Unit{}, Unit{}}
    case C.Lista{u, +q, xs, +pai} Q.IrmaosValores{+valores, +acima}:
      match canonico:
        case L.Ambos{+medido, L.Ambos{segmentos, ancestrais}}:
          F.com_par(L.E<Q.PlanoCanonico(pilha, plano), Q.PlanoCanonico(pilha, plano)>,
            S.ValoresCanonicos(valores), S.ValoresCanonicos(valores), duplicar_valores_canonicos(valores, segmentos),
            v1 => v2 => F.com_par(L.E<Q.PlanoCanonico(pilha, plano), Q.PlanoCanonico(pilha, plano)>,
              Q.PlanoCanonico(pai, acima), Q.PlanoCanonico(pai, acima), duplicar_plano_canonico(pai, acima, ancestrais),
              p1 => p2 => L.Ambos{L.Ambos{medido, L.Ambos{v1, p1}}, L.Ambos{medido, L.Ambos{v2, p2}}}))
    case C.Campo{u, +q, n, xs, +pai} Q.IrmaosCampos{+campos, +acima}:
      match canonico:
        case L.Ambos{+medido, L.Ambos{segmentos, ancestrais}}:
          F.com_par(L.E<Q.PlanoCanonico(pilha, plano), Q.PlanoCanonico(pilha, plano)>,
            S.CamposCanonicos(campos), S.CamposCanonicos(campos), duplicar_campos_canonicos(campos, segmentos),
            c1 => c2 => F.com_par(L.E<Q.PlanoCanonico(pilha, plano), Q.PlanoCanonico(pilha, plano)>,
              Q.PlanoCanonico(pai, acima), Q.PlanoCanonico(pai, acima), duplicar_plano_canonico(pai, acima, ancestrais),
              p1 => p2 => L.Ambos{L.Ambos{medido, L.Ambos{c1, p1}}, L.Ambos{medido, L.Ambos{c2, p2}}}))
    case C.Nome{u, +q, n, xs, +pai} Q.ValorAposNome{+v, +bs, +campos, +acima}:
      match canonico:
        case L.Ambos{+medido, L.Ambos{valor, L.Ambos{segmentos, ancestrais}}}:
          +codificado = {valor : {P.codificar(v) == Some{bs} : Maybe<&2, List<&2, U32>>}}
          F.com_par(L.E<Q.PlanoCanonico(pilha, plano), Q.PlanoCanonico(pilha, plano)>,
            S.CamposCanonicos(campos), S.CamposCanonicos(campos), duplicar_campos_canonicos(campos, segmentos),
            c1 => c2 => F.com_par(L.E<Q.PlanoCanonico(pilha, plano), Q.PlanoCanonico(pilha, plano)>,
              Q.PlanoCanonico(pai, acima), Q.PlanoCanonico(pai, acima), duplicar_plano_canonico(pai, acima, ancestrais),
              p1 => p2 => L.Ambos{
                L.Ambos{medido, L.Ambos{codificado, L.Ambos{c1, p1}}},
                L.Ambos{medido, L.Ambos{codificado, L.Ambos{c2, p2}}}}))
    case C.Raiz{} Q.IrmaosValores{valores, acima}:
      L.ex_falso(L.E<Q.PlanoCanonico(pilha, plano), Q.PlanoCanonico(pilha, plano)>, canonico)
    case C.Raiz{} Q.IrmaosCampos{campos, acima}:
      L.ex_falso(L.E<Q.PlanoCanonico(pilha, plano), Q.PlanoCanonico(pilha, plano)>, canonico)
    case C.Raiz{} Q.ValorAposNome{v, bs, campos, acima}:
      L.ex_falso(L.E<Q.PlanoCanonico(pilha, plano), Q.PlanoCanonico(pilha, plano)>, canonico)
    case C.Lista{u, q, xs, pai} Q.Fim{}:
      L.ex_falso(L.E<Q.PlanoCanonico(pilha, plano), Q.PlanoCanonico(pilha, plano)>, canonico)
    case C.Lista{u, q, xs, pai} Q.IrmaosCampos{campos, acima}:
      L.ex_falso(L.E<Q.PlanoCanonico(pilha, plano), Q.PlanoCanonico(pilha, plano)>, canonico)
    case C.Lista{u, q, xs, pai} Q.ValorAposNome{v, bs, campos, acima}:
      L.ex_falso(L.E<Q.PlanoCanonico(pilha, plano), Q.PlanoCanonico(pilha, plano)>, canonico)
    case C.Campo{u, q, n, xs, pai} Q.Fim{}:
      L.ex_falso(L.E<Q.PlanoCanonico(pilha, plano), Q.PlanoCanonico(pilha, plano)>, canonico)
    case C.Campo{u, q, n, xs, pai} Q.IrmaosValores{valores, acima}:
      L.ex_falso(L.E<Q.PlanoCanonico(pilha, plano), Q.PlanoCanonico(pilha, plano)>, canonico)
    case C.Campo{u, q, n, xs, pai} Q.ValorAposNome{v, bs, campos, acima}:
      L.ex_falso(L.E<Q.PlanoCanonico(pilha, plano), Q.PlanoCanonico(pilha, plano)>, canonico)
    case C.Nome{u, q, n, xs, pai} Q.Fim{}:
      L.ex_falso(L.E<Q.PlanoCanonico(pilha, plano), Q.PlanoCanonico(pilha, plano)>, canonico)
    case C.Nome{u, q, n, xs, pai} Q.IrmaosValores{valores, acima}:
      L.ex_falso(L.E<Q.PlanoCanonico(pilha, plano), Q.PlanoCanonico(pilha, plano)>, canonico)
    case C.Nome{u, q, n, xs, pai} Q.IrmaosCampos{campos, acima}:
      L.ex_falso(L.E<Q.PlanoCanonico(pilha, plano), Q.PlanoCanonico(pilha, plano)>, canonico)
