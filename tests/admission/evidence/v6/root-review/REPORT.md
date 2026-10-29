# Revisão matemática independente — admissão V6

Status: revisão concluída com um achado P2 novo de perda de generalidade. Não encontrei aceitação de False nos controles executados. Fontes do candidato não foram editadas. Não houve Git, GH, delegação ou mudança de provider/model.

## Achado novo confirmado

**P2 — A tradução da prova por casos perde a descida quando um parâmetro Bool anterior é casado antes do Nat recursivo.**

Fonte completa mínima desta rodada:

```bend
import Base

def f(~p: Nat, n: Nat) -> Nat:
  match n:
    case Zero{}: p
    case Succ{x}: f(p, x)
def helper(b: Bool,p: Nat,n: Nat) -> {f(p,n) == p : Nat}:
  match b:
    case False{}:
      match n:
        case Zero{}: {==}
        case Succ{x}: helper(b,p,x)
    case True{}:
      match n:
        case Zero{}: {==}
        case Succ{x}: helper(b,p,x)
def main(b: Bool,n: Nat) -> {f(3n,n) == 3n : Nat}:
  helper(b,3n,n)
```

O Bend oficial aceita essa fonte. A API `admitSubmission` com contrato ativo de três tamanhos a recusa como `BENDTT_CHECK`:

```
In AdmissionRepresentation.Function.Client.helper.evaluate:
affine live code, calls that descend
```

Não é uma prova falsa aceita, esgotamento do harness, domínio opaco nem grupo gerado mutuamente recursivo. A rejeição está na função auxiliar gerada para `helper`; a fonte tem recursão estrutural no campo `x` de `Succ`. A reprodução pela API ocorreu três vezes nessa fonte, incluindo captura do payload real, sem alteração do Book pelo harness antes do gate. Uma quarta variante usa `helper(True{},3n,n)` no próprio `Client.theorem(n)` chamado por J nas folhas de `Bindings.certificado`; ela é recusada no mesmo avaliador. Seu payload `actual-certificate-failing.bendtt` (SHA256 `f1b8f0fa5e35a0241b6ae24ab5389d6ee6afbba858150351a64d92f63361e13d`) também foi recusado pelo kernel original. Os arquivos literais de toda a submissão estão em `actual-certificate-failing-source/`. Portanto o caso não depende de um helper sem uso no certificado.

O payload capturado (`counterexample.bendtt`, SHA256 `3494d1da80abd30cba819ac49d4bc752493e197e8af2adb2cc3cada366444326`) foi rejeitado com a mesma mensagem pelo kernel ORIGINAL e pelo derivado. Remover somente os blocos cujo nome começa `AdmissionRepresentation` deixa o payload físico e seus source_links; esse recorte passa em ambos. Esse controle localiza a objeção na representação acrescentada; ele não é uma prova substituta da obrigação completa do candidato.

Controles causais:

| Alteração | Checker oficial | API V6 |
|---|---:|---|
| fonte acima | aceita | recusa matemática no avaliador gerado |
| remover apenas `~` de `f` | aceita | aceita, rota física |
| conservar `~`, remover o `match b` | aceita | aceita, rota estrutural |

O controle de trocar a ordem dos parâmetros sem trocar os matches foi recusado pelo checker oficial (regra de ordem de matches); está preservado como erro do harness, não como evidência sobre o candidato.

A composição relevante reconstrói a representação do parâmetro casado em `structural-bodies.mjs:119–122` e usa esse ambiente ao compor as chamadas recursivas e o eliminador (`:140–143`). A relação anterior do Bool reaparece como pacote reconstruído antes da relação menor de Nat. A atribuição causal é sustentada pelos dois controles; não afirmo aqui uma prova geral sobre a implementação do guard de descida.

A correção deve conservar a checagem original de descida, as raízes físicas e todos os source_links. Aumentar fuel, suprimir o guard ou trocar esse erro por aceite não resolve o contraexemplo.

## Limitação declarada observada, sem novo achado

`lambda_higher_proof.bend` é aceita no primário, mas a rota estrutural falha tecnicamente em `Reflection.function`: “This opaque result needs a closed construction, not an assumed relation”. O parâmetro é uma função que retorna prova. Isso pertence à limitação declarada de reflexão de inputs opacos/de prova; foi registrado separadamente e não contado como recusa de uma proposição falsa.

## Casos próprios e falhas do harness

Os relatórios JSON `probes.json`, `probes-extra.json`, `probes-controls.json` guardam cada fonte, fixture, código/diagnóstico e duração. Há controles positivos de registro dependente contendo prova, indução não reflexiva, função usada como valor, família de tipos, argumento aninhado e extremos definicionalmente iguais. As sete execuções com fontes/controles inválidos do harness foram preservadas nos `.official.log`: nome `Pair` já existente, sintaxe Sigma/let incorreta, prefixo de template aberto no corpo vivo, match em valor computado e ordem inválida de matches. Nenhuma foi atribuída ao candidato.

## Replays dirigidos e confirmações

Executei os dois métodos de `tests/admission/structural-guards.test.mjs`, sem repetir a suíte de 165. Ambos passaram: seis cenários físicos/dependências/aliases/Base (incluindo o corte de identidade com a mesma head de main), e quatro versões Token (positivo, backlink, prova física no lugar da lógica, duplicação). Eles exercitam ambos os kernels e conservam a árvore física adulterada, sem regenerá-la.

Reexecutei também `capture-certificate.mjs` em `certificate-replay/`. O certificado realmente usa `Client.theorem(n)`. O payload positivo SHA256 `9a25da0c672e7a4e0ea9e1efa4a16e3bbfa8d0aa03008a95dcac5444982eccc9` passa original e derivado; C do mesmo Book imprime `Dados.VInt{0, 6}`. Alterar a dependência física `Client:f~0` para Nat2 falha no próprio `Client.f_7e_0.source_link` em ambos. Esse é replay de regressão existente, separado dos casos novos do reviewer.

A seleção de rota é feita no código antes de `checkKernelFile`. Na reprodução nova só foi capturado um payload/final verdict por API; não houve aceite subsequente por outra rota após a rejeição do avaliador. Não encontrei nesse recorte um fallback que escondesse erro de guard/kernel.

## Integridade e escopo

O archive V6 tem SHA256 `0e1681cb261ca6ffe5988b7d6712e7323ad41c405693340dc510213eb76e7956`; os 174 membros foram conferidos no archive. Os 137 arquivos do grupo de commit conferem no checkout; os dois arquivos de verificador instalados são membros sintéticos do archive e não existem nesse caminho no checkout, exatamente como documentado pela entrega. Os 18 originais históricos e as dependências do contrato ativo foram conferidos antes da execução.

A revisão se restringe a tradução/dispatch/obrigações matemáticas do gate V6, selagem e pequenos controles de emissão. Não examinei contabilidade Linux, controller reentrante, publicação do banco inteiro, equivalência geral de backend nem Contrato(a,k). Não foi executada a suíte inteira de 165 casos.


Conferência final: os **201 caminhos registrados antes e depois** permaneceram idênticos, o archive V6 não mudou e os 174 membros continuam autenticados. Conferi também, contra suas autoridades fixadas, os cinco fontes oficiais, kernels/compilador oficial/generic, 14 fontes do contrato ativo e os seis archives históricos V1–V5/review_v5_literal. `integrity-before.json`, `archive-integrity.json` e `integrity-after.json` registram a diferença entre membro sintético e arquivo live.

**Conclusão restrita:** os reparos anteriores e guards exercitados têm evidência local positiva. Há uma nova perda de generalidade demonstrada na rota estrutural e ela deve ser corrigida antes de se considerar essa classe de programas coberta. O achado não demonstra aceite de prova falsa e não equivale a uma auditoria completa do compilador. Generalidade total, MedicaoReal e Contrato(a,k) não foram aprovados.
