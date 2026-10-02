# Contributing / Building notes

This repository is primarily a finished artifact rather than an actively
solicited collaborative project, but issues and pull requests are welcome.

## Building locally

```bash
lake exe cache get   # first time: prebuilt Mathlib
lake build           # compile the project
```

The production build is required to emit no Lean or linter warnings
(`python3 tools/check_warnings.py`).  The eight Mathlib-only files
`ParkingAudit/*/Challenge.lean` are the sole exception: each contains one documented
statement-level `sorry`, checked against its completed solution by
`leanprover/comparator`.

A few practical notes for working with this development:

- **Never run `lake clean`.**  It wipes the Mathlib oleans and forces a
  multi-hour rebuild from source.  To force a project-only rebuild, remove the
  project build artifacts under `.lake/build/lib/lean/Parking` (and the
  corresponding `.lake/build/ir/Parking`) and re-run `lake build`.

- **Per-file rebuilds.**  Lake invalidates by content hash, not mtime, so
  `touch` does nothing; delete the specific `.olean` under
  `.lake/build/lib/lean/` and rebuild the module.

- **Frozen statements.**  The text between `-- FROZEN-STATEMENT-BEGIN` and
  `-- FROZEN-STATEMENT-END` in `Parking/Frozen/` and `Parking/External/` is
  pinned by the SHA-256 recorded in `ledger/manifest.yaml`.  A change there
  must be registered with `python3 tools/freeze.py` and shows up in
  `python3 tools/check_manifest.py`; proofs after the end marker may be
  changed freely.

- **Model-independent lemmas** belong in the shared library
  `Lattice-Probability`, which this repository imports; its scaling-limit
  toolkit is `LatticeProb/Prob/Scaling/`.  Do not add a local copy of a library
  declaration.

- **The main results** are in `Parking/MainTheorems.lean`; the axiom audit is
  `lake build Parking.Meta.AxiomsAudit`, and the comparator surface is
  `lake build ParkingAudit`.

## Elaboration policy for new files

These rules keep the elaboration of new files cheap and predictable.

- Close arithmetic goals with named monotonicity lemmas and `calc`, not with
  `nlinarith`.  When a nonlinear fact is needed, hoist it into a small `private`
  lemma over abstract real variables, so that the proof of the main goal only
  instantiates it.
- Never call `nlinarith` on a goal that contains `Real.rpow` or `Real.exp`
  terms.  State the needed inequality over abstract real variables, as above,
  and apply it to the `rpow` and `exp` terms, so that they never enter a numeric
  tactic.
- Before `ring` or `field_simp` on an expression built with `set`, run
  `clear_value` on the bound names; otherwise the let-bodies are unfolded inside
  the tactic.
- Keep Lean files under 1500 lines.
- Never run `lake clean` (see the notes above).
