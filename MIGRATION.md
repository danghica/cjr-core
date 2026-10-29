# Migration

Created from checkpoint `e07ccfb365e019f440480d6357d0251187acc8da` of the original CJR repository.
Proofs were not revalidated during migration. Prior proof reports are historical evidence only.
The checked-in Cangjie extraction is preserved; regeneration requires a proof build.

Runtime tests use preserved extracted Cangjie. Extraction-driver and load-path changes have not been checked by Rocq in this migration.

Printer API: `copy_rules`, `no_copy_rules`, and `print_prog_with` make optional native copy lowering explicit. `print_prog` retains the default interface with no collection-specific rewrite.
