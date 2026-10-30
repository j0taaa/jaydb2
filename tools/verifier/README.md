# Verificador oficial

O JayDB usa o **Safe e o BendTT originais do Bend 2.0.39**, sem derivação ou alteração de regras, quantidades, combustível, axiomas ou runtime. Seus hashes estão em `tools/admission/toolchain.lock.json`.

`checkBook` pede ao `safe_emit` oficial o payload do Book já checado pelo frontend. `checkKernelFile` executa o BendTT original sobre esse arquivo. Não há kernel alternativo, retry com combustível alterado ou fallback após rejeição.

Uma falha de processo ou representação não implementada pelo Safe é distinta de uma prova recusada pelo kernel. O JayDB não reescreve o certificado nem fornece uma testemunha substituta para obter aceitação.

A instalação apenas copia o kernel oficial já compilado e verifica seu hash:

```sh
python3 tools/bootstrap.py --source /caminho/bend-2.0.39 --kernel /caminho/bendtt
```

O kernel esperado tem SHA-256 `e365eba1741602bb45261aa0eb6bd2c6f5db885d4b9d4cd603a27bc3c5a9ed18`. Não é necessário gerar um novo verificador Lean para usar o banco.

`make verify` confere as provas gerais com os dois modos oficiais. A aprovação desses componentes não demonstra, sozinha, o contrato do executável completo.
