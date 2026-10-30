# Provas gerais

`proof/VERIFICAR.bend` agrega as provas da implementação pura. `tests/proof/VERIFICAR.bend` reaplica suas interfaces públicas em leis quantificadas. Nenhum desses agregados constrói, por si, `Contrato(a,k)` para o serviço completo com controlador Rust, auxiliar Node e executáveis Bend.

- `Fundamentos`, `Ordens`, `Autenticacao`: estrutura e identidade autenticada.
- `Maquina`, `Seguranca`, `Preparacao`, `Publicacao`: percurso incremental, leis do administrador e preparação da proposta.
- `Chamada`: existência da preparação real após finalização e composição de execução autenticada/certificada com preparação fiel, conclusão válida e rollback. Usa as funções reais de `Nucleo`; não pressupõe fidelidade nem validade da conclusão.
- `Representacao`, `Transporte`, `RecepcaoLimites`, `Reificacao`: bytes, enquadramento e argumentos efetivos.
- `CodecVerificar`: 692 leis sobre o Codec original. `CodecLei2` demonstra que aceitação reconstitui a codificação original exata, que toda codificação representável dentro do teto é aceita e que o resultado satisfaz `Interface.DecodificacaoCorreta`, incluindo recusas.
- `EntradaVerificar`, `Configuracao`: composição da entrada real, autenticação, erros e configuração.
- `Recursos`, `AlocacoesComprimentos`, `ErrosFixos`: os três tamanhos lógicos e a conferência de comprimento anterior à construção. Não modelam memória física ou prazos.

## Conferência

```sh
make verify
```

O comando confere os hashes dos 18 originais e dos 14 módulos do contrato ativo, verifica os agregados positivos com `--check-only` e `--verdict` separados e executa seis negativos que removem premissas distintas: identidade, bytes, lei administrativa, publicação, comprimento e reificação. O timeout do runner serve apenas para interromper desenvolvimento travado.

Os exemplos fechados antigos e relatórios de rodadas anteriores foram retirados da suíte corrente; suas versões continuam no Git. Provas gerais não foram removidas para reduzir a contagem de linhas.

## Fronteira pendente

O [mapa das oito leis](CONTRATO_SERVICO.md) identifica, para cada obrigação,
as funções executadas, os lemas disponíveis, a lacuna de composição e os
contratos externos necessários. Ele orienta a construção do protocolo de
fases; não substitui sua prova nem redefine as oito leis.

É necessário ligar essas relações puras ao artefato efetivamente emitido e executado, ao runtime, ao host e ao canal. Pins e testes de integração sustentam casos concretos; não substituem essa demonstração. Não são admitidos fatos externos inventados nem premissas que assumam o resultado desejado.
