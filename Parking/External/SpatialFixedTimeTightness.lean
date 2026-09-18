/-
External input: the equicontinuity in probability, at each fixed time, of the
rescaled divisible odometer, which is the content of Theorem 1.3(i)(b) of
Bou-Rabee and Panagiotis, *Quantitative explosion and percolation of the
divisible sandpile* (BP, cited at `parking.tex:1741-1752`, label
`prop:spatial-scaling`).

BP's Theorem 1.3 (Critical growth and spatial scaling), part (i)(b), page 5,
states (in the notation of Section 2 there): for `d ∈ {1,2,3}` and i.i.d.
mean-zero scenery `ζ` with an exponential moment,

  "Let `W` be white noise on `ℝ^d`, let
   `Z(t,x) := √(Var(ζ(0))) ∫_{ℝ^d} g_t^BM(x,y) W(dy)`, with `g_t^BM` the
   finite-time Green kernel of Brownian motion, and let
   `𝒰(T,x) := sup_{τ≤T} E_x^BM[Z(T,x) - Z(T-τ,B_τ)]`, where the supremum is
   over stopping times for Brownian motion.  Then, for every `T > 0`,
   `R^{-(2-d/2)} u^{(R)}_{⌊TR²⌋} ⟹ 𝒰(T,·)` in `C_loc(ℝ^d)`, where the field on
   the left denotes the multilinear interpolation from `R^{-1}ℤ^d` of the
   values `x/R ↦ R^{-(2-d/2)} u_{⌊TR²⌋}(x)`."

WHAT IS TRANSCRIBED, AND WHY IT IS A FAITHFUL, NOT A STRENGTHENED, READING.
Convergence in law in `C_loc(ℝ^d)` to a field that is a.s. continuous is, as a
matter of general topology and probability (Prokhorov's theorem plus
Arzelà-Ascoli; no fact of BP's own proof is used beyond the displayed
conclusion), EQUICONTINUITY IN PROBABILITY of the converging sequence on every
compact set: for every compact `K'`, every accuracy `ε` and probability `ε'`,
there is a mesh `δ` and a threshold `R₀` such that beyond `R₀` the field
oscillates by more than `ε` between `δ`-close points of `K'` with probability
at most `ε'`.  This is exactly the SPATIAL, SINGLE-TIME special case of the
equicontinuity-in-probability clause `prop:spatial-scaling` needs (the third
clause of `Parking.Frozen.spatial_scaling`, with the time coordinate held fixed at `T`).
Registering only this consequence, rather than the full statement of
convergence in law together with the constructions of `W`, Brownian motion and
`Z`, is the same design choice `Parking.Frozen.spatial_scaling` itself already
makes for `Uc`: its own docstring reads "the identification of `U` as the
Brownian optimal-stopping value driven by `W` is replaced by the properties
the proposition itself asserts of it ... the continuum optimal stopping
problem is not modelled here."  Doing the same here avoids constructing a
`d`-dimensional Brownian motion and a `d`-dimensional white noise integral
inside this External, while asserting nothing BP's theorem does not already
give: EQUICONTINUITY IN PROBABILITY IS WEAKER than convergence in law to an
a.s. continuous limit, never stronger, so this is not an extrapolation of BP's
proof mechanism: it is the plain topological content of the displayed conclusion,
read off with no further input from BP's argument.

WHY THE PLAIN (NON-INTERPOLATED) FIELD.  BP's own remark, immediately after
Proposition 4.3 restates part (i)(b) with the field
`𝒰_R(T,x) := R^{-(2-d/2)} u_{⌊R²T⌋}(⌊Rx⌋)` (no interpolation): "The standard
interpolation from the parabolic mesh has the same compact-uniform limit,
because the limiting field is uniformly continuous on compact subsets of
`(0,∞)×ℝ^d`."  `Parking.barDivisible` is exactly `𝒰_R` (`R^{d/2-2}
u_{⌊sR²⌋}(⌊Rx⌋)`, the same prefactor since `d/2-2 = -(2-d/2)`), so this
External is stated for `Parking.barDivisible` directly, matching how
`Parking.Frozen.spatial_scaling`'s own clauses are stated.

WHAT IS NOT ASSUMED.  Nothing about `Parking.barOdometer` (the un-divisible,
particle odometer) or `Parking.signedPair` (the signed count), which are
`parking.tex`'s own objects; nothing about the joint behaviour across
different times `T`, which BP's Proposition 4.3 (for the linear membrane
field, stated as `Parking.External.LinearFieldScaling`) and the
optimal-stopping-stability transfer inside the proof of Theorem 1.3(i)(b)
(stated as `Parking.External.SpatialStoppingStability`) supply and which are
NOT restated here.

VACUITY.  The right-hand side of the inequality is a probability (`toReal` of
a measure of a set), so it is never the junk value of an unbounded `sSup`; the
inner supremum is over a family bounded by `Parking.exists_bound_on_compact`
(the field reads finitely many lattice sites on a compact set), so it is a
genuine supremum, not the junk value `Real.sSup ∅ = 0` of an empty or
unbounded family.  The statement is a real constraint (the paper's own
Proposition 4.3 for the linear field, plus BP's optimal-stopping-stability
transfer for the full odometer, are exactly what make it true), not
satisfiable by a junk value at either side.  Checked at the paper's own model,
`Z^d` with an i.i.d. critical scenery.
-/
import Parking.Basic
import Parking.Support.Continuum

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
/-- The spatial equicontinuity in probability, at each fixed time, of the
rescaled divisible odometer (BouRabeePanagiotis2026, Theorem 1.3(i)(b), page 5,
read as the equicontinuity-in-probability consequence of its stated
convergence in law in `C_loc(ℝ^d)`). -/
def Parking.External.SpatialFixedTimeTightness : Prop :=
  ∀ (d : ℕ), 1 ≤ d → d ≤ 3 → ∀ (ν : Measure ℤ), Parking.CriticalLaw ν →
    ∀ T : ℝ, 0 < T → ∀ K' : Set (Fin d → ℝ), IsCompact K' →
      ∀ ε : ℝ, 0 < ε → ∀ ε' : ℝ, 0 < ε' →
        ∃ δ : ℝ, 0 < δ ∧ ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
          ((Parking.law d ν) {w | ε < ⨆ x ∈ K', ⨆ y ∈ K', ⨆ _ : dist x y ≤ δ,
              |Parking.barDivisible w R T x - Parking.barDivisible w R T y|}).toReal
            ≤ ε'
-- FROZEN-STATEMENT-END
