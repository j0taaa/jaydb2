# Seleção explícita do driver C

Os builders de módulos em `tools/native/build.py` e de recipes, fields,
constructor, loading, lifecycle, recepção e conclusão usam Clang 19 com
`--no-default-config`, inclusive nas passagens de IR, stack usage, assembly e
link. A escolha retira configurações automáticas do driver do perfil desses
builds; não altera a linguagem Bend, as leis ou os orçamentos.

O [controle causal anterior](../../tests/research/entry/CLANG_DEFAULT_CONFIG-2026-10-29.md)
conserva uma cópia literal do ELF do compilador, com uma configuração de
fixture adjacente: o controle carrega a macro e a seleção explícita a ignora.
No compilador instalado não foi encontrada configuração automática; não foi
demonstrada influência por uma requisição do banco.

`tests/service/test_compiler_profile.py` também usa uma cópia literal do
compilador, com builtin headers reais e uma config de fixture que produz erro.
O controle ordinário falha por esse erro. Os builders selecionados compilam
os shims, as duas formas de link da recipe e o C histórico do Codec. A fonte
C é preservada; o teste não prova sua correspondência geral com Bend nem
concede cobertura de memória.

As opções participam dos argumentos/identidades dos shims. Builders que não
registravam argumentos completos acrescentam `compilerDriverFlags` e
`compilerDefaultConfiguration=false`; são descrição do comando, não
testemunhas de `MedicaoReal`. Mudar o builder muda sua identidade: artefatos
antigos continuam nos checkpoints e precisam de instalação explícita do novo
runtime antes de selecioná-lo.

Esse perfil cobre os builders nomeados. Instalação do frontend/verificador e
build do observer têm entradas próprias e não foram alterados por esta
mudança. Headers, sysroot, linker, bibliotecas, ambiente e estabilidade dos
arquivos ainda precisam do fechamento operacional correspondente.
