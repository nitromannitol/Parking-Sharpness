# Parking-Sharpness -- independent audit of the `SEALED` manifest nodes (BATCH A)

Date: 2026-10-04.  Auditor: BATCH A of the `dimred-worker-PARKING-AUDIT` brief, independent of
the Parking authors (refute-first, read-only).  Paper pinned at `parking.tex` SHA-256
`4aa03aee7c30e24bffc9a4e8220f775b5c71706e694dcd9bcffc865c8135d3a0` (verified).

## Scope and split

The manifest lists 51 nodes in state `SEALED` (49 theorems + 2 proved External definitions).
The dependency order is the DAG whose edges are `import` relations among the SEALED nodes'
files; a Kahn topological sort (leaves first, ties broken by id) was cut in half.  Batch A is
the first 26 nodes (the leaves/foundations); Batch B is the remaining 25.  Every dependency of
a Batch A node that is itself SEALED lies inside Batch A, so the split is a valid topological
prefix.

**Batch A (audited here, 26):** `ext-binomial-local-clt`, `ext-green-gradient`, `ext-green-norms`, `ext-heat-strong-minimum`, `ext-sandpile-growth-proved`, `ext-srw-local-clt`, `ext-stopping`, `ext-u-concentration`, `cor-growth`, `ext-variance-scale`, `ext-critical-scale-lower-tail`, `lem-activity-holes`, `lem-critical-density`, `cor-critical`, `lem-deferred`, `lem-density-compare`, `lem-exposure`, `lem-gamma-sum`, `lem-mean-horizon`, `lem-near-tilt`, `lem-nearest-close-pair`, `lem-nearest-one-point`, `lem-one-particle`, `lem-parallel`, `lem-pathwise-comparison`, `lem-product`.

**Batch B (assigned to the other worker, 25):** `lem-range-lower`, `lem-shift`, `lem-tagged-monotonicity`, `lem-transport`, `lem-w-martingale`, `prop-discrepancy`, `prop-everyone-settles`, `prop-near-divisible`, `prop-nearest-two-hole`, `prop-oriented-scaling`, `prop-resolvent`, `prop-spatial-scaling`, `prop-w-moment`, `thm-comparison`, `thm-four-sparse`, `thm-master`, `thm-near`, `thm-nearest`, `thm-nearest-counterexample`, `thm-oriented`, `thm-oriented-walk`, `thm-subcritical`, `thm-subcritical-tail`, `thm-trichotomy`, `thm-upper`.

## Verdict

**PASS on all 26 Batch A nodes; no FAIL.  Two documented CONCERNs (not defects), listed below.**
Each node has a per-node report at `ledger/audits/parking-<node-id>.md` addressing statement
integrity, proof, non-vacuity/junk and citations.

## PASS/FAIL table

| node | kind | file | Lean export | verdict |
|---|---|---|---|---|
| `ext-binomial-local-clt` | `theorem` | `Parking/External/BinomialLocalCLTProved.lean` | `Parking.External.binomialLocalCLT` | **PASS** |
| `ext-green-gradient` | `definition` | `Parking/External/GreenGradient.lean` | `Parking.External.GreenGradient` | **PASS** |
| `ext-green-norms` | `theorem` | `Parking/External/GreenNormsProved.lean` | `Parking.External.greenNorms` | **PASS** |
| `ext-heat-strong-minimum` | `theorem` | `Parking/External/HeatStrongMinimumProved.lean` | `Parking.External.heatStrongMinimum` | **PASS** |
| `ext-sandpile-growth-proved` | `theorem` | `Parking/External/SandpileGrowthProved.lean` | `Parking.External.sandpileGrowth` | **PASS** |
| `ext-srw-local-clt` | `theorem` | `Parking/External/SRWLocalCLTBridge.lean` | `Parking.External.srwLocalCLT` | **PASS** |
| `ext-stopping` | `definition` | `Parking/External/Stopping.lean` | `Parking.External.Stopping` | **PASS** |
| `ext-u-concentration` | `theorem` | `Parking/External/UConcentrationProved.lean` | `Parking.External.uConcentration` | **PASS** |
| `cor-growth` | `theorem` | `Parking/Frozen/Growth.lean` | `Parking.Frozen.growth` | **PASS** |
| `ext-variance-scale` | `theorem` | `Parking/External/VarianceScale.lean` | `Parking.External.varianceScale` | **PASS** |
| `ext-critical-scale-lower-tail` | `theorem` | `Parking/External/CriticalScaleLowerTailProved.lean` | `Parking.External.criticalScaleLowerTail` | **PASS** |
| `lem-activity-holes` | `theorem` | `Parking/Frozen/ActivityHoles.lean` | `Parking.Frozen.activity_holes` | **PASS** |
| `lem-critical-density` | `theorem` | `Parking/Frozen/CriticalDensity.lean` | `Parking.Frozen.critical_density` | **PASS** |
| `cor-critical` | `theorem` | `Parking/Frozen/CorCritical.lean` | `Parking.Frozen.cor_critical` | **PASS** |
| `lem-deferred` | `theorem` | `Parking/Frozen/Deferred.lean` | `Parking.Frozen.deferred` | **PASS** |
| `lem-density-compare` | `theorem` | `Parking/Frozen/DensityCompare.lean` | `Parking.Frozen.density_compare` | **PASS** |
| `lem-exposure` | `theorem` | `Parking/Frozen/Exposure.lean` | `Parking.Frozen.exposure` | **PASS** |
| `lem-gamma-sum` | `theorem` | `Parking/Frozen/GammaSum.lean` | `Parking.Frozen.gamma_sum` | **PASS** |
| `lem-mean-horizon` | `theorem` | `Parking/Frozen/MeanHorizon.lean` | `Parking.Frozen.mean_horizon` | **PASS** |
| `lem-near-tilt` | `theorem` | `Parking/Frozen/NearTilt.lean` | `Parking.Frozen.near_tilt` | **PASS** |
| `lem-nearest-close-pair` | `theorem` | `Parking/Frozen/NearestClosePair.lean` | `Parking.Frozen.nearest_close_pair` | **PASS** |
| `lem-nearest-one-point` | `theorem` | `Parking/Frozen/NearestOnePoint.lean` | `Parking.Frozen.nearest_one_point` | **PASS** |
| `lem-one-particle` | `theorem` | `Parking/Frozen/OneParticle.lean` | `Parking.Frozen.one_particle` | **PASS** |
| `lem-parallel` | `theorem` | `Parking/Frozen/Parallel.lean` | `Parking.Frozen.parallel` | **PASS** |
| `lem-pathwise-comparison` | `theorem` | `Parking/Frozen/PathwiseComparison.lean` | `Parking.Frozen.pathwise_comparison` | **PASS** |
| `lem-product` | `theorem` | `Parking/Frozen/Product.lean` | `Parking.Frozen.product` | **PASS** |

## Batch B (for the other worker; not audited here)

| node | kind | file | Lean export |
|---|---|---|---|
| `lem-range-lower` | `theorem` | `Parking/Frozen/RangeLower.lean` | `Parking.Frozen.range_lower` |
| `lem-shift` | `theorem` | `Parking/Frozen/Shift.lean` | `Parking.Frozen.shift` |
| `lem-tagged-monotonicity` | `theorem` | `Parking/Frozen/TaggedMonotonicity.lean` | `Parking.Frozen.tagged_monotonicity` |
| `lem-transport` | `theorem` | `Parking/Frozen/Transport.lean` | `Parking.Frozen.transport` |
| `lem-w-martingale` | `theorem` | `Parking/Frozen/WMartingale.lean` | `Parking.Frozen.w_martingale` |
| `prop-discrepancy` | `theorem` | `Parking/Frozen/Discrepancy.lean` | `Parking.Frozen.discrepancy` |
| `prop-everyone-settles` | `theorem` | `Parking/Frozen/EveryoneSettles.lean` | `Parking.Frozen.everyone_settles` |
| `prop-near-divisible` | `theorem` | `Parking/Frozen/NearDivisible.lean` | `Parking.Frozen.near_divisible` |
| `prop-nearest-two-hole` | `theorem` | `Parking/Frozen/NearestTwoHole.lean` | `Parking.Frozen.nearest_two_hole` |
| `prop-oriented-scaling` | `theorem` | `Parking/Frozen/OrientedScaling.lean` | `Parking.Frozen.oriented_scaling` |
| `prop-resolvent` | `theorem` | `Parking/Frozen/Resolvent.lean` | `Parking.Frozen.resolvent` |
| `prop-spatial-scaling` | `theorem` | `Parking/Frozen/SpatialScaling.lean` | `Parking.Frozen.spatial_scaling` |
| `prop-w-moment` | `theorem` | `Parking/Frozen/WMoment.lean` | `Parking.Frozen.w_moment` |
| `thm-comparison` | `theorem` | `Parking/Frozen/Comparison.lean` | `Parking.Frozen.comparison` |
| `thm-four-sparse` | `theorem` | `Parking/Frozen/FourSparse.lean` | `Parking.Frozen.four_sparse` |
| `thm-master` | `theorem` | `Parking/Frozen/Master.lean` | `Parking.Frozen.master` |
| `thm-near` | `theorem` | `Parking/Frozen/Near.lean` | `Parking.Frozen.near` |
| `thm-nearest` | `theorem` | `Parking/Frozen/Nearest.lean` | `Parking.Frozen.nearest` |
| `thm-nearest-counterexample` | `theorem` | `Parking/Frozen/NearestCounterexample.lean` | `Parking.Frozen.nearest_counterexample` |
| `thm-oriented` | `theorem` | `Parking/Frozen/Oriented.lean` | `Parking.Frozen.oriented` |
| `thm-oriented-walk` | `theorem` | `Parking/Frozen/OrientedWalk.lean` | `Parking.Frozen.oriented_walk` |
| `thm-subcritical` | `theorem` | `Parking/Frozen/Subcritical.lean` | `Parking.Frozen.subcritical` |
| `thm-subcritical-tail` | `theorem` | `Parking/Frozen/SubcriticalTail.lean` | `Parking.Frozen.subcritical_tail` |
| `thm-trichotomy` | `theorem` | `Parking/Frozen/Trichotomy.lean` | `Parking.Frozen.trichotomy` |
| `thm-upper` | `theorem` | `Parking/Frozen/Upper.lean` | `Parking.Frozen.upper` |

## Gate commands and observed results

All commands were run from `~/lean/Parking-Sharpness` with `PATH=$HOME/.elan/bin:$PATH`.
`lake build Parking` was run first because the checkout's `Parking` oleans (and several
`Parking/Support` oleans) were stale/absent; it completed successfully (10371 jobs), after
which the whole gate suite passed.

```
$ lake build Parking
Build completed successfully (10371 jobs).

$ sha256sum paper/parking.tex
4aa03aee7c30e24bffc9a4e8220f775b5c71706e694dcd9bcffc865c8135d3a0  paper/parking.tex
   (matches the manifest `source_pin.sha256`)

$ python3 tools/check_manifest.py
check_manifest: OK (62 nodes, 0 unsealed; closure 0 checked, 62 skipped; 658 Parking
declarations indexed)                                                [exit 0]

$ python3 tools/check_axioms.py
check_axioms: 62 clean, 0 depend on sorryAx, 0 unresolved              [exit 0]

$ python3 tools/check_warnings.py
check_warnings: OK (0 registered sorry warnings)                     [exit 0]

$ python3 tools/check_constants.py
check_constants: OK (62 statements; every existential constant is bound before every paper
parameter, so it is a genuine constant)                             [exit 0]

$ python3 tools/check_coverage.py
check_coverage: OK -- 45 statements in the paper, 45 formalized       [exit 0]

$ python3 tools/check_clauses.py
check_clauses: OK (48 statements, each read against the paper and its correspondence
recorded; 17 where the count heuristic says the paper asserts more, all explained) [exit 0]

$ python3 tools/check_exponents.py
check_exponents: OK (62 statements; every paper exponent appears in its Lean statement or
is explained above)                                                  [exit 0]

$ python3 tools/paper_anchors.py
paper_anchors: OK (48 anchors resolved, 14 nodes carry no paper label)  [exit 0]

$ python3 tools/sync_docs.py
sync_docs: OK (62 nodes; README.md and CORRESPONDENCE.md agree with the manifest) [exit 0]

$ python3 tools/assumptions.py --check
assumptions: OK (ASSUMPTIONS.md is current)                          [exit 0]

$ python3 tools/certificate.py --check
certificate: OK (CERTIFICATE.md matches the checked state)          [exit 0]
```

The stock `check_axioms.py` classifies closures only by the presence of `sorryAx`, so a
targeted probe was run to print the closures of the Batch A exports *and* of the two companion
proof theorems behind the two `definition` nodes (`Parking.External.greenGradient`,
`Parking.External.stopping`), which the stock probe would otherwise not resolve to a proof:

```
'Parking.External.greenGradient'      depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.External.stopping'           depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.External.binomialLocalCLT'   depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.External.greenNorms'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.External.sandpileGrowth'     depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.External.criticalScaleLowerTail' depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.External.srwLocalCLT'        depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.External.uConcentration'     depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.External.heatStrongMinimum'  depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.External.varianceScale'      depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.Frozen.growth'               depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.Frozen.critical_density'     depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.Frozen.cor_critical'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.Frozen.deferred'             depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.Frozen.density_compare'      depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.Frozen.exposure'             depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.Frozen.gamma_sum'            depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.Frozen.mean_horizon'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.Frozen.near_tilt'            depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.Frozen.nearest_close_pair'   depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.Frozen.nearest_one_point'    depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.Frozen.one_particle'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.Frozen.parallel'             depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.Frozen.pathwise_comparison'  depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.Frozen.product'              depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.Frozen.activity_holes'       depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every Batch A closure is exactly the three classical axioms; no `sorryAx`, `axiom`, `admit`, or
other axiom appears.

## Method per node

1. **Statement integrity.** The cited `parking.tex` lines were extracted from the pinned
   paper and read against the bytes between the `FROZEN-STATEMENT-BEGIN`/`END` markers: all
   hypotheses, quantifier order, domains, exponents and constants were compared by hand (the
   `check_exponents.py` / `check_constants.py` / `check_clauses.py` readings were consulted as a
   cross-check, not as the authority).  Quantifier order was checked in particular: every
   existential constant the paper says depends only on `d` (or only on `d` and the law) is bound
   before `n`, `t`, `r`, `p`, `δ`, `L`, etc.
2. **Proof.** `lake build Parking` completed; the targeted `#print axioms` probe above reports
   the closure of every Batch A export and of the two companion proofs.  The frozen bytes hash
   and the declaration name are re-checked by `check_manifest.py`.
3. **Non-vacuity / junk.** Every hypothesis block was checked for satisfiability, and every
   conclusion for a junk value (`0`, `sInf ∅`, non-summable `tsum`, `Set.ncard` on an infinite
   set, `True`).  The statements use `IsLUB` for the supremum in `ext-stopping`, `Summable`/
   `Integrable` guards around `tsum`/integrals, `iSup` of nonnegative terms in `wStar`/`gamma`/
   `greenMax`, and positive existential constants; no junk value was found.  Explicit satisfying
   witnesses are noted per node where short.
4. **Citations.** Each `Parking.External.*` hypothesis was traced to a genuine cited input:
   a paper citation (BP, BPRS, Lawler-Limic, Nirenberg, Raic, Donsker-Varadhan) or a named
   input of the sibling sandpile formalization -- never a step of `parking.tex` itself.

## CONCERNs (documented, not defects; no action requested)

1. **`ext-green-gradient` states only the first half of the display.**  The paper's
   `eq:green-gradient` asserts `|g_m(y)-g_m(z)| <= C(1+|y|)^{1-d}` *and, hence,*
   `Γ_m(y) <= C(1+|y|)^{2-2d}`.  The frozen Prop transcribes only the first relation.  This
   weakening does not weaken any dependent theorem: the sole dependent node, `lem-gamma-sum`,
   carries that gradient bound as its hypothesis and derives the `Γ` bound.  Recorded in
   `tools/check_clauses.py`.
2. **Two `definition` nodes are SEALED by a companion theorem, not by the export itself.**
   For `ext-stopping` and `ext-green-gradient` the manifest `export` is the `Prop`; the stock
   `check_axioms.py` therefore prints the (axiom-free) closure of the *definition*, not of the
   proof.  The targeted probe closes this gap: `Parking.External.stopping` and
   `Parking.External.greenGradient` both have closure `[propext, Classical.choice, Quot.sound]`,
   so the `SEALED` claim is genuine.  (The same pattern applies to the Batch B definitions if
   any are SEALED; `check_axioms.py` should be read with this in mind.)

## Confirmed defects reported to the author

None.  No Batch A node FAILs statement integrity, proof, non-vacuity or citations.

## Reproduce

```
cd ~/lean/Parking-Sharpness
export PATH="$HOME/.elan/bin:$PATH"
lake build Parking
python3 tools/check_manifest.py && python3 tools/check_axioms.py \
  && python3 tools/check_warnings.py && python3 tools/check_constants.py \
  && python3 tools/check_coverage.py && python3 tools/check_clauses.py \
  && python3 tools/check_exponents.py && python3 tools/paper_anchors.py \
  && python3 tools/sync_docs.py && python3 tools/assumptions.py --check \
  && python3 tools/certificate.py --check
```

*This consolidated report and the 26 per-node reports were produced by an independent auditor
(BATCH A).  No Lean file was edited and no manifest state was changed.*
