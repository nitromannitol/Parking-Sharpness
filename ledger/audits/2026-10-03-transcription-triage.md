# Hand triage of the Parking audit flags (2026-10-03)

`~/fleet/runs/parking-sharpness-audit/` (DeepSeek-V4.1-flash, all lenses returned; reader
fallible) reported **no proof-level defect**. Two items were left for the owner; both are triaged
here against the frozen Lean and the paper. No frozen statement is edited.

## `lem-exposure` — both flags are false positives

The auditor read the two differences as defects. Both dissolve on the definitions:

1. **"Lean uses `U_k(y) ≤ j` where the paper says `j > U_k(y)`."** This is the indexing shift, not an
   off-by-one. The paper numbers instructions from one; this formalization from zero
   (`Parking/Support/Filtration.lean:1-15`): `ρ_{j+1}(y)` is `ω.2.1 (y, j)` and `{U_k(y) ≥ j+1}` is
   `j + 1 ≤ U ω k y`. With the paper's `j' = j + 1`, the paper's condition `j' > U_k(y)` is
   `j + 1 > U_k(y)`, i.e. `U_k(y) ≤ j = q.2` — exactly the Lean's `U ω' k q.1 ≤ q.2`.

2. **"a.s. measurable instead of measurable."** The frozen conclusion is
   `∃ g, Measurable[expFiltration d k] g ∧ U (k+1) x =ᵐ[law d ν] g`: `U (k+1) x` agrees almost surely
   with a `G_k`-measurable function. This is the standard measure-theoretic form and is what every
   downstream use consumes; `U` is a deterministic function of the data and the ambient
   σ-algebra, so no content is lost. Benign reformulation.

## The four External-Prop fidelity items

The remaining flags are fidelity questions about the carried `Parking.External.*` propositions.
Those are EXTERNALS-to-zero work (proving/refining the cited `Prop`s), not transcription defects in
the parked theorems.

## Consequence

There is no transcription defect in the 51 `SEALED` nodes. `lem-exposure` is faithful, and the only
open obligation is the External debt. The 51 nodes may be promoted `SEALED -> PROVED` on this
audit record.
