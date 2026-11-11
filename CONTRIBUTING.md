# Contributing and building

This repository is mainly a finished artifact, the formalization of one paper, but issues and
pull requests are welcome.

## Building locally

```bash
lake exe cache get   # first time: prebuilt mathlib
lake build           # compile the project
```

The toolchain is pinned in `lean-toolchain`. The production build is required to emit no Lean
or linter warnings (`python3 tools/check_warnings.py`). The eight mathlib-only files
`ParkingAudit/*/Challenge.lean` are the only files with a `sorry`: each contains one
documented statement-level `sorry`, checked against its completed solution by
`leanprover/comparator`. `lake build Parking` builds the library and
`lake build ParkingAudit` the comparator libraries.

## The main results and the axiom audit

The main results `Parking.subcritical_tail`, `Parking.master`, `Parking.growth`,
`Parking.trichotomy`, `Parking.nearest`, `Parking.nearest_counterexample`, `Parking.near` and
`Parking.oriented_walk` are in `Parking/MainTheorems.lean`. To print their axiom reports:

```bash
lake build Parking.Meta.AxiomsAudit   # the eight main theorems
python3 tools/check_axioms.py         # the axiom closure of every registered statement
```

`Parking/Meta/AxiomsAudit.lean` is not imported by the library root, because a `#print axioms`
command runs again whenever its module is rebuilt. Each report must list exactly `propext`,
`Classical.choice` and `Quot.sound`; the axiom-audit step of the CI workflow fails on any
warning, and `tools/check_axioms.py` fails on `sorryAx`. The checkers in `tools/` need Python 3
and PyYAML (`pip install pyyaml`).

## Conventions for Lean files

- No `sorry`, `admit` or new `axiom` in the library; `python3 tools/check_manifest.py` rejects
  them.
- **Frozen statements.** The text between `-- FROZEN-STATEMENT-BEGIN` and
  `-- FROZEN-STATEMENT-END` in `Parking/Frozen/` and `Parking/External/` is pinned by the
  SHA-256 recorded in `ledger/manifest.yaml`. A change there must be registered with
  `python3 tools/freeze.py` and shows up in `python3 tools/check_manifest.py`; proofs after
  the end marker may be changed freely. Statements refer to the paper by LaTeX label.
- **Model-independent lemmas** belong in the shared library Lattice-Probability, which this
  repository imports; its scaling-limit toolkit is `LatticeProb/Prob/Scaling/`. Do not add a
  local copy of a library declaration. The dependencies under `.lake/packages/` are read-only.
- **Never run `lake clean`.** It wipes the mathlib oleans and forces a multi-hour rebuild from
  source. To force a project-only rebuild, remove the project build artifacts under
  `.lake/build/lib/lean/Parking` (and the corresponding `.lake/build/ir/Parking`) and re-run
  `lake build`.
- **Per-file rebuilds.** Lake invalidates by content hash, not modification time, so `touch`
  does nothing; delete the specific `.olean` under `.lake/build/lib/lean/` and rebuild the
  module.

### Elaboration policy for new files

These rules keep the elaboration of new files cheap and predictable.

- Close arithmetic goals with named monotonicity lemmas and `calc`, not with
  `nlinarith`. When a nonlinear fact is needed, hoist it into a small `private`
  lemma over abstract real variables, so that the proof of the main goal only
  instantiates it.
- Never call `nlinarith` on a goal that contains `Real.rpow` or `Real.exp`
  terms. State the needed inequality over abstract real variables, as above,
  and apply it to the `rpow` and `exp` terms, so that they never enter a numeric
  tactic.
- Before `ring` or `field_simp` on an expression built with `set`, run
  `clear_value` on the bound names; otherwise the let-bodies are unfolded inside
  the tactic.
- Keep Lean files under 1500 lines.

## Comparators

Each pair under `ParkingAudit/<Pair>/` has a `Challenge.lean` that imports mathlib only, a
`Solution.lean`, a `SolutionBasic.lean` and a `comparator.json` that permits exactly
`propext`, `Classical.choice` and `Quot.sound`. Do not add a declaration to a challenge that
the statement does not need, and do not change a challenge without checking it against the
paper's statement. The command that runs a pair is in
[`ParkingAudit/README.md`](ParkingAudit/README.md) and
[`ParkingAudit/COMPARATOR_RUNS.md`](ParkingAudit/COMPARATOR_RUNS.md). A missing pair, a
missing tool or a failed kernel check is a failure.

## Continuous integration

- `build.yml` (**CI**) builds the library, rejects any warning or `sorry` warning, builds the
  axiom audit module, and runs `tools/check_manifest.py`.
- `comparator.yml` (**Comparator audit**) builds `ParkingAudit` and runs the comparator on all
  eight pairs.

Both run on pushes to `main` that change Lean files, `tools/`, `paper/`, `ledger/`,
`formalization.yaml` or the build configuration, and can be started manually.
