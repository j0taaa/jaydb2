# Historical contract

[contract-v1/contract](contract-v1/contract/) contains English translations of
the 18 original contract files. The repository-wide English migration changed
names and language in these historical copies; they are not byte-identical to
the original Portuguese files. The byte-identical original versions remain in Git at commit
`f65f1279913b446bfa37ce1fab3a90a1f7682241`, before the English migration.
`tools/check.py` checks the translated archive against
[`contract-original.sha256.json`](../contract-original.sha256.json).

The [active contract](../contract/) has its own manifest. Removed prototypes,
reports, and snapshots remain available in Git history.
