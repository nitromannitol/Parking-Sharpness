# Audit -- promotion `SEALED -> PROVED` for the two External Props `ext-stopping` and `ext-green-gradient`

Scope: `Parking/External/Stopping.lean` and `Parking/External/GreenGradient.lean`, their frozen
`Prop` blocks, the cited displays in `paper/parking.tex`, the shared-library providers, and the
axiom closure. Read-only; no manifest or Lean edit. `git` was not run; `lake build` was not run.

## Manifest facts

| id | version | kind | state | export | file | frozen SHA-256 |
|---|---|---|---|---|---|---|
| `ext-stopping` | 2 | definition | SEALED | `Parking.External.Stopping` | `Parking/External/Stopping.lean` | `6ba333d5...b7cd731` |
| `ext-green-gradient` | 2 | definition | SEALED | `Parking.External.GreenGradient` | `Parking/External/GreenGradient.lean` | `41340ef1...f700028f` |

Both frozen hashes recomputed from the bytes between the `-- FROZEN-STATEMENT-BEGIN/END` markers
(the `tools/freeze.py` recipe) match the manifest exactly, so the audit is against the frozen
statements.

## `ext-stopping`

**Paper display.** `parking.tex:876-884`, label `lem:stopping`, quoted from BPRS Theorem 3.2,
multiplied by `2d`:

> `u_n(x) = sup_{sigma <= n} E_x sum_{j=0}^{sigma-1} eta(X_j)` (eq. `eq:stopping`, lines 878-880),
> the supremum over stopping times for the natural filtration of `X`, bounded by `n` and
> including `sigma = 0`; the stopping rule may depend on `eta`.

**Frozen Prop** (`Stopping.lean:33-35`):

```
def Parking.External.Stopping : Prop :=
  forall (d : Nat), 1 <= d -> forall (eta : Site d -> R) (n : Nat) (x : Site d),
    IsLUB (LatticeProb.Graph.Zd.zdStopValues eta n x) (Parking.u eta n x)
```

**Transcription.** Faithful. `Parking.u` (`Parking/Basic.lean:82`) is exactly the paper's
normalized odometer `u_0 = 0`, `u_{n+1} = max 0 (eta + walkOp u_n)`; `LatticeProb`'s `zdStopValues`
is the set of integrals of `sceneryPartialSum eta (tau X) X` against `siteWalkLaw d x` over
`IsWalkStopping` times with `tau X <= n`, the constant `tau = 0` allowed and `eta` fixed before
`tau`. The equation's supremum is written as `IsLUB`, which is the faithful strengthening that
excludes an unattained/unbounded junk value. `d >= 1` is the only added side condition.

**Provider and shared library.** `Parking.External.stopping` (`Stopping.lean:51-55`) proves the
`Prop`; it rewrites `Parking.u` to the library odometer via the local `Parking.u_eq_zdOdometer`
(`Stopping.lean:39-49`, proved by induction, no `sorry`) and then applies the shared-library
theorem:

```
Stopping.lean:55   exact LatticeProb.Graph.Zd.parkingStopping' d hd eta n x
.lake/packages/lattice-probability/LatticeProb/Graph/ZdRepresentation.lean:168
  theorem parkingStopping' (d : Nat) (hd : 1 <= d) (eta : Site d -> R) (n : Nat) (x : Site d) :
    IsLUB (zdStopValues eta n x) (zdOdometer eta n x)
```

`parkingStopping'` in turn is `parkingStopping` with `Graph.walkAverageIsIntegral` discharged, and
`parkingStopping` is `Graph.randomWalkRepresentation`. No local axiom or `sorry` is involved.

**Closure.** Targeted probe in the pinned dependency (transient file outside the tree, same
`#print axioms` mechanism as the gate):

```
'Parking.External.Stopping' depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.External.stopping' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`. `python3 tools/check_axioms.py` prints `clean ext-stopping` and the run ends
`62 clean, 0 depend on sorryAx, 0 unresolved` (exit 0).

**Verdict: promotable to PROVED.** No refutation found.

## `ext-green-gradient`

**Paper display.** `parking.tex:1029-1034`, label `eq:green-gradient`:

> "For every `m >= 1`, every `y`, and every neighbor `z` of `y`,
> `|g_m(y) - g_m(z)| <= C (1 + |y|)^{1-d}`, hence `Gamma_m(y) <= C (1+|y|)^{2-2d}`."

The following prose (lines 1035-... ) derives this "For `d >= 2`" from the first-difference local
central limit estimate and the Gaussian bound of Lawler-Limic Section 2.3; for `d = 1` it says the
gradient is computed exactly in the proof of `lem:gamma-sum`. The norm is the graph distance from
the origin (`parking.tex:594-595`, the notation subsection).

**Frozen Prop** (`GreenGradient.lean:33-38`):

```
def Parking.External.GreenGradient (d : Nat) : Prop :=
  exists C : R, 0 < C /\ forall m : Nat, 1 <= m -> forall y z : Site d,
    z in LatticeProb.nbrFinset y ->
      |Parking.green d m y - Parking.green d m z|
        <= C * (1 + (Parking.graphNorm y : R)) ^ (1 - (d : R))
```

**Transcription.** `Parking.green d m` is the truncated Green function
`sum_{j<m} P^j(0,.)` (`Parking/Support/Walk.lean:83`), `Parking.graphNorm` is the library
`LatticeProb.graphNorm` (`Parking/Basic.lean:34`), the `l^1`/graph distance from the origin. The
`exists C > 0` sits outside `m, y, z`, so `C` depends only on `d`, as in the paper. The
transcription is faithful to the **first** relation of the display; the "hence"
`Gamma_m` relation is deliberately not carried in the node (recorded in `tools/check_clauses.py`
and `CORRESPONDENCE.md`), and the only consumer, `lem-gamma-sum`, derives the `Gamma` bound from
this gradient bound itself (`Parking/Support/GammaSum.lean`). This is a weakening, not a
mis-statement.

**Provider and shared library.** `Parking.External.greenGradient (d) (hd : 2 <= d)`
(`GreenGradient.lean:42-48`) proves the `Prop` for `d >= 2`; it bridges `Parking.green` to the
library's `srwGreen` via the local `Parking.green_eq_srwGreen` (`Parking/Support/GreenBridge.lean`,
proved, no `sorry`) and applies

```
GreenGradient.lean:44   obtain <C, hC, hgrad> := LatticeProb.exists_srwGreen_gradient d hd
.lake/packages/lattice-probability/LatticeProb/Walk/SRWGreenGrad.lean:477
  theorem exists_srwGreen_gradient (d : Nat) (hd : 2 <= d) :
    exists C : R, 0 < C /\ forall (m : Nat) (y z : Site d), z in nbrFinset y ->
      |srwGreen d m y - srwGreen d m z| <= C * (1 + (graphNorm y : R)) ^ (1 - (d : R))
```

The library theorem has no `m >= 1` restriction, so the provider proves the `Prop` with the
horizon hypothesis dropped; this is why `GreenGradient.lean:45-46` (`intro m _ y z hz`) ignores it.
No local axiom or `sorry` is involved.

**Closure.** Targeted probe:

```
'Parking.External.GreenGradient' depends on axioms: [propext, Classical.choice, Quot.sound]
'Parking.External.greenGradient' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`. `python3 tools/check_axioms.py` prints `clean ext-green-gradient` and the same
`62 clean, 0 depend on sorryAx, 0 unresolved` (exit 0).

**Refutation-first caveats (do not block promotion, but must be recorded).**

1. The `Prop` is a family over `d : Nat`, but the companion only discharges it for `2 <= d`.
   For `d = 0` it is vacuous (`nbrFinset` is empty) and for `d = 1` it is true but proved by a
   separate exact computation (`Parking/Support/SpatGreenShiftLowDim.lean`, `green_one_sub'`),
   not by this companion. This matches the paper, which derives the display for `d >= 2` and
   handles `d = 1` elsewhere, and it matches every consumer: `Parking.Frozen.gamma_sum` carries
   the hypothesis as `hgrad : 2 <= d -> Parking.External.GreenGradient d`, and
   `Parking/Support/GreenIncrement.lean:83` calls the companion with `hge : 2 <= d`. So the node is
   proved exactly in its range of use.
2. The manifest `export` of both nodes is the `def ... : Prop`, so the generic
   `tools/check_axioms.py` gate prints `#print axioms` on the *definition*, not on the companion
   theorem. For `kind: definition` external nodes the gate alone does not certify the proof; the
   companion `Parking.External.stopping` / `Parking.External.greenGradient` was probed separately
   here and is clean.

**Verdict: promotable to PROVED**, with caveat 1 (scope `d >= 2`) and caveat 2 (gate methodology)
recorded in the node's audit trail.

## Gate output

```
$ python3 tools/check_axioms.py          # exit 0
  clean   ext-stopping
  ...
  clean   ext-green-gradient
  ...
62 clean, 0 depend on sorryAx, 0 unresolved
```

Both `Parking/External/Stopping.lean` and `Parking/External/GreenGradient.lean` contain no
`sorry`, no `axiom`, and no `sorryAx` in the closures of either the export definitions or the
companion theorems.

## Summary

| node | paper display | transcription | companion proof | closure | verdict |
|---|---|---|---|---|---|
| `ext-stopping` | `parking.tex:876-884` | faithful (`IsLUB` form) | `Parking.External.stopping` via `LatticeProb.Graph.Zd.parkingStopping'` | `[propext, Classical.choice, Quot.sound]` | promote |
| `ext-green-gradient` | `parking.tex:1029-1034` | faithful to the first (gradient) relation; scope `d >= 2` | `Parking.External.greenGradient` via `LatticeProb.exists_srwGreen_gradient` | `[propext, Classical.choice, Quot.sound]` | promote, scope `d >= 2` |
