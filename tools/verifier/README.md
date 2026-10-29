# Verificador

O kernel oficial BendTT e suas fontes permanecem intactos e fixados por hash. O derivado `bendtt-budget` parametriza o combustível, mantendo as regras e exigindo tanto o checker guardado quanto `Book.check` na aceitação. Todas as normalizações guardadas propagam esgotamento de combustível; esse estado nunca vira erro matemático definitivo.

A geração verifica em Lean 4.34.0 `Claim.sound`, consistência e adequação para todo `FuelBudget`. Os axiomas continuam `propext`, `Classical.choice` e `Quot.sound`, sem sorry ou axiomas adicionais. Fonte, gerador, main adapter, prova e binário constam no lock.

```sh
node tools/verifier/build.mjs
```

É necessário o Lean pelo Elan, no caminho documentado no README raiz. O build normal reproduz o artefato; `--write-lock` altera deliberadamente a identidade e não é instalação comum.

`checkKernelFile` usa o mesmo arquivo imutável em cada tentativa e dobra BigInt quando o kernel retorna exclusivamente o código reservado de exaustão. `checkBook` traduz o Book já checado e verifica o payload final. Safe também aumenta seu próprio combustível quando necessário. Não há máximo de retries nem deadline do banco.

Uma saída diferente do protocolo esperado, sinal ou erro de execução é falha técnica. Uma forma não representada pelo tradutor também é falha técnica; não prova que um certificado matemático inexiste.

O main derivado é síncrono, com stack Linux expansível e alocador configurado sem eager commit desnecessário. Essas opções não alteram os termos nem as regras. O kernel original continua disponível para controles independentes; os mesmos payloads podem ser verificados por ele quando seu combustível fixo comporta o cálculo.

Os testes correntes cobrem retry positivo/negativo, recusa de exportar evidência apagada para código vivo e distinção entre representação não implementada e prova falsa. Os agregados gerais pertencem a `make verify`; logs e binários de rodadas antigas ficam no histórico, fora da suíte atual.
