# Retained evidence

- `raw-result.json` is the byte-for-byte original run manifest. Its 30 database
  records and ten PostgreSQL whole-server restart checks passed. Its top-level
  status is **failed** because the final repository inventory guard saw two new
  contract modules added by another session.
- `provenance-audit.json` records a separate, reproducible audit. Every original
  production and suite file, pinned tool, and controller hash matched. Complete
  environment identities reconstructed from the measured-start inputs match all
  ten durable snapshot headers, whose checksums also pass. The added modules
  entered none of the measured frozen environments. Final model hashes agree
  across engines. This is stronger evidence than assuming unused modules have
  no effect: the service hashes every contract/source module at freeze time.
- `results.json` is explicitly **derived** analysis input, with successful
  provenance audit metadata and the original inventory-guard status/error kept
  in that metadata. It does not replace or erase the raw manifest.
- `analysis.json` and `summary.csv` recompute statistics from checked samples.
  PNG/SVG figures and `charts.html` present those values. SVG/PNG charts can be
  opened standalone; HTML uses the conversation renderer's theme variables.

The local database files, stopped PostgreSQL cluster and dumps, generated
sources, run snapshot and logs remain in `build/database-comparison-final/`.
Pilot runs and the canceled isolated fallback are excluded from all statistics.

To reproduce the audit with the original local run artifacts and matching
experiment checkout, run `audit.py` as documented in the suite README. An audit
refuses modified/missing original inputs, nonpassing database records, changed
snapshots or mismatched frozen environments. It never overwrites raw results.
