# Validação das provas de entrada no contrato revisado

Execute na raiz do projeto:

```sh
python3 tests/proof/test_proofs.py --record
```

O runner verifica os agregados gerais e de testes, incluindo
`EntradaVerificar.bend`, em `--check-only` e `--verdict` oficiais de Bend
2.0.39, cada modo em um processo próprio. `BENDTT` deve apontar ao kernel
oficial instalado, quando não estiver disponível no caminho padrão do Bend.
O timeout do harness é apenas de desenvolvimento.

Uma rejeição só conta quando o teorema preenchido `falso` diverge entre os
tipos esperado/observado. Erros de importação, parsing, timeout ou nome
indefinido não contam como negativos válidos.

O relatório ativo é `RESULTADOS_RECURSOS_SIMPLES.json`, com identificação da
revisão, hashes das dependências estáveis, manifesto dos 14 módulos ativos,
verificação dos 18 originais sob `history/contrato-v1/` e saídas dos checkers.
`EntradaResultados.json` e `EntradaReproducao.json` são registros históricos
literais anteriores a esta revisão; não são regravados por esse runner. O
runner antigo embutido neste documento está preservado no snapshot integral
`history/antes-da-retirada-dos-recursos-fisicos.tar.gz`.

Para contrato, wrappers puros com o mesmo Codec e certificados/seeds
dos exemplos, execute também `python3 tests/proof/test_revision.py --record`.
Esses checks não alegam uma prova de `Contrato(a,k)` do executável completo.
