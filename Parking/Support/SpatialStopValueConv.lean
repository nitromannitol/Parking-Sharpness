/-
**The single-point, single-cutoff scalar value convergence**, for the STOPPING-VALUE summand
of BP's Lemma 2.5 decomposition (`Parking.u_eq_potential_add_stoppingSup`,
`Parking/Support/Terminal.lean`).  `Parking.External.SpatialStoppingStability` is applied at
horizon `n := ⌊R²⌋₊` and time `T := s` (NOT `n := ⌊sR²⌋₊`), so that `Parking.spatialScaledSite n`
rescales by `√n ≈ R`, matching `Parking.barDivisible`'s own `/R` rescaling exactly, and no
Brownian self-similarity step is needed (`T = s` directly, not `T = 1`).

**What this module proves.** For a FIXED bounded continuous cutoff field
`G : E := BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ`, read as the reward
`Parking.spatialStopReward x s G t y := -G (s - t, x + y)`
(elapsed time `t`, offset `y`, matching `Parking.contUc`'s own reward convention, "the first
argument is the elapsed time" per `Parking.spatialContPayoffs`'s docstring), the DISCRETE
optimal-stopping value built from `G` at scale `R` (`Parking.spatialStopValueCutoff`) converges,
as `R → ∞`, to the CONTINUUM Brownian optimal-stopping value at the same reward
(`Parking.spatialContStopValue`).  Combined with `Parking.External.LinearFieldScaling`'s own
weak-convergence clause (the hypothesis `hlim` below) through `Parking.Support.
ExtendedMappingReal.tendsto_integral_comp_real_of_lipschitz`, this gives the weak convergence of
the RANDOM cutoff discrete stopping value (built from the realized field `w.1`, via `Parking.
linHatInterp`) to the random cutoff continuum stopping value (built from `LinearFieldScaling`'s
witness `Z`), for every bounded continuous test function of the resulting REAL number.

**Relation to the full stopping-value summand.**  The scalar core proved here is one ingredient
of the full argument.  The others are: (a) relating `spatialStopValueCutoff` back to
`Parking.barDivisible`'s own literal second summand, which needs the exact-grid
reparametrization AND the floor-rounding gap between `⌊⌊R²⌋₊·s⌋₊` and `⌊sR²⌋₊`; (b) the
cutoff-to-true gap (both the discrete field's own cutoff error, via the walk's exit tail,
`Parking.measureReal_sup_walkPath_graphNorm_le`, and the continuum field's,
`Parking.Support.ContSpatialCutoff`); (c) the convergence of the potential summand `V` to
`Z(s,x)` (`Parking.tendsto_measure_linHatInterp_sub_barPotential_zero`,
`Parking/Support/LinGridGap.lean`); (d) the joint/multi-point and scenery-retained forms.

The floor-rounding gap in (a) is handled below (`Parking.natFloor_sq_mul_sub_spatialStopHorizon_le`,
consuming `Parking.Generic.FloorGap.natFloor_sq_mul_sub_natFloor_horizon_le`): the two horizons
differ by at most `⌊s⌋₊ + 1` steps, uniformly in `R`.  Turning this `O(1)`-step count into a
VANISHING bound on `|stoppingSup F ⌊sR²⌋₊ z0 - stoppingSup F ⌊⌊R²⌋₊·s⌋₊ z0|` for the reward `F` in
question needs more than boundedness of `F` (a bounded reward only gives the crude,
non-vanishing bound `2‖F‖`): it needs a MODULUS OF CONTINUITY on how the reward, read at
`SpatialStoppingStability`'s own elapsed-time convention, varies over `O(1)/⌊R²⌋₊ → 0` of elapsed
time, which is available here since the reward is built from a COMPACTLY-SUPPORTED cutoff (hence
uniformly continuous by Heine-Cantor).  This "exact-grid reparametrization" proper is not carried
out in this module.  None of (b)-(d) is needed for the theorem proved here, which is exactly the
single-point, single-cutoff scalar value convergence.

`Parking.External.SpatialStoppingStability` and `Parking.External.LinearFieldScaling` are
taken here as explicit hypotheses.  This module does not touch `Parking.Frozen.spatial_scaling`,
which carries them only at the final assembly.
-/
import Parking.Support.SpatWalkCLT
import Parking.Support.ValueLipschitz
import Parking.Support.ContValueLipschitz
import Parking.Support.LinearFieldMeasurable
import Parking.Support.LinHatMeasurable
import Parking.Support.ExtendedMappingReal
import Parking.Generic.LipschitzLimit
import Parking.Generic.FloorGap
import Parking.External.SpatialStoppingStability

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Parking

variable {d : ℕ}

/-- Abbreviation for the space of bounded continuous space-time rewards, reducible so that
instance arguments stated for it transfer transparently. -/
abbrev SpatBCF (d : ℕ) : Type := BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ

/-! ### The reward, and the discrete/continuum stopping-value functionals of a generic
cutoff field -/

/-- **The stopping-value reward built from a generic bounded continuous cutoff field `G`.**
`t` is the ELAPSED time (matching `Parking.spatialContPayoffs`'s own convention); the reward
reads `G` at REMAINING time `s - t`, offset by the fixed point `x`, matching `Parking.contUc`'s
own reward `k y ↦ -Z ω' (s - k) (x + y)`. -/
def spatialStopReward (x : Fin d → ℝ) (s : ℝ)
    (G : BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ) (t : ℝ) (y : Fin d → ℝ) : ℝ :=
  -G (s - t, x + y)

theorem abs_spatialStopReward_le (x : Fin d → ℝ) (s : ℝ)
    (G : BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ) (t : ℝ) (y : Fin d → ℝ) :
    |spatialStopReward x s G t y| ≤ ‖G‖ := by
  unfold spatialStopReward
  rw [abs_neg]
  exact G.norm_coe_le_norm _

theorem continuous_spatialStopReward (x : Fin d → ℝ) (s : ℝ)
    (G : BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ) :
    Continuous (fun p : ℝ × (Fin d → ℝ) => spatialStopReward x s G p.1 p.2) := by
  unfold spatialStopReward
  exact (G.continuous.comp
    ((continuous_const.sub continuous_fst).prodMk (continuous_const.add continuous_snd))).neg

/-- **The discrete stopping-value functional** of a generic cutoff field `G`, at scale `R`:
the simple-random-walk optimal-stopping value at `Parking.spatialStopReward x s G`, read at
elapsed step `k` and rescaled site `k/n`, `spatialScaledSite n`, `n := ⌊R²⌋₊`, over the
horizon `⌊n·s⌋₊`. -/
def spatialStopValueCutoff (x : Fin d → ℝ) (s : ℝ) (R : ℝ)
    (G : BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ) : ℝ :=
  Parking.stoppingSup d
    (fun k z => spatialStopReward x s G ((k : ℝ) / (⌊R ^ 2⌋₊ : ℝ))
      (Parking.spatialScaledSite ⌊R ^ 2⌋₊ z))
    ⌊(⌊R ^ 2⌋₊ : ℝ) * s⌋₊ (0 : Site d)

/-- **The continuum stopping-value functional** of a generic cutoff field `G`: the Brownian
optimal-stopping value at the same reward. -/
def spatialContStopValue {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d)) (PB : Measure ΩB) (x : Fin d → ℝ) (s : ℝ)
    (G : BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ) : ℝ :=
  Parking.spatialContValue (Parking.ofBrownianSpace B) PB (spatialStopReward x s G) s

/-! ### The discrete functional is `1`-Lipschitz, uniformly in `R` -/

theorem abs_spatialStopValueCutoff_sub_le (hd1 : 1 ≤ d) (x : Fin d → ℝ) (s : ℝ) (R : ℝ)
    (G1 G2 : BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ) :
    |spatialStopValueCutoff x s R G1 - spatialStopValueCutoff x s R G2| ≤ dist G1 G2 := by
  unfold spatialStopValueCutoff
  set n := ⌊R ^ 2⌋₊ with hn
  set horizon := ⌊(n : ℝ) * s⌋₊ with hhorizon
  refine Parking.abs_stoppingSup_sub_le hd1 _ _ horizon (0 : Site d)
    (M := max ‖G1‖ ‖G2‖) (fun k z => ?_) (fun k z => ?_) (fun k z => ?_)
  · exact (abs_spatialStopReward_le x s G1 _ _).trans (le_max_left _ _)
  · exact (abs_spatialStopReward_le x s G2 _ _).trans (le_max_right _ _)
  · set p : ℝ × (Fin d → ℝ) :=
      (s - (k : ℝ) / (n : ℝ), x + Parking.spatialScaledSite n z) with hp
    have h1 : spatialStopReward x s G1 ((k : ℝ) / (n : ℝ)) (Parking.spatialScaledSite n z)
        - spatialStopReward x s G2 ((k : ℝ) / (n : ℝ)) (Parking.spatialScaledSite n z)
        = -(G1 p - G2 p) := by
      unfold spatialStopReward
      rw [hp]; ring
    rw [h1, abs_neg]
    calc |G1 p - G2 p| = dist (G1 p) (G2 p) := (Real.dist_eq _ _).symm
      _ ≤ dist G1 G2 := G1.dist_coe_le_dist p

theorem lipschitzWith_spatialStopValueCutoff (hd1 : 1 ≤ d) (x : Fin d → ℝ) (s : ℝ) (R : ℝ) :
    LipschitzWith 1 (spatialStopValueCutoff (d := d) x s R) := by
  refine LipschitzWith.of_dist_le_mul fun G1 G2 => ?_
  rw [NNReal.coe_one, one_mul, Real.dist_eq]
  exact abs_spatialStopValueCutoff_sub_le hd1 x s R G1 G2

theorem measurable_spatialStopValueCutoff (hd1 : 1 ≤ d) (x : Fin d → ℝ) (s : ℝ) (R : ℝ)
    [MeasurableSpace (BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ)]
    [BorelSpace (BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ)] :
    Measurable (spatialStopValueCutoff (d := d) x s R) :=
  (lipschitzWith_spatialStopValueCutoff hd1 x s R).continuous.measurable

/-! ### `⌊R²⌋₊ → ∞` as `R → ∞` -/

theorem tendsto_nat_floor_sq_atTop : Tendsto (fun R : ℝ => ⌊R ^ 2⌋₊) atTop atTop :=
  tendsto_nat_floor_atTop.comp (tendsto_pow_atTop two_ne_zero)

/-! ### The pointwise limit, via `Parking.External.SpatialStoppingStability` -/

theorem tendsto_spatialStopValueCutoff (hd1 : 1 ≤ d) (hd3 : d ≤ 3)
    (hStopping : Parking.External.SpatialStoppingStability)
    (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d)) (hB : LatticeProb.IsBrownianSpace d 0 B PB)
    (x : Fin d → ℝ) (s : ℝ) (hs : 0 < s)
    (G : BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ) :
    Tendsto (fun R : ℝ => spatialStopValueCutoff x s R G) atTop
      (𝓝 (spatialContStopValue B PB x s G)) := by
  set Glim : ℝ → (Fin d → ℝ) → ℝ := spatialStopReward x s G with hGlim
  have hGlimCont : Continuous (fun p : ℝ × (Fin d → ℝ) => Glim p.1 p.2) :=
    continuous_spatialStopReward x s G
  have hGlimBdd : ∀ s' (y : Fin d → ℝ), |Glim s' y| ≤ ‖G‖ := fun s' y =>
    abs_spatialStopReward_le x s G s' y
  have hWalk := Parking.hWalk_of_isBrownianSpace d hd1 hd3 ΩB PB B hB s hs
  have hkey := hStopping d hd1 hd3 ΩB PB B hB s hs hWalk ‖G‖ (norm_nonneg G) Glim hGlimCont
    hGlimBdd (fun _ : ℕ => Glim) (fun _ s' y => hGlimBdd s' y)
    (fun ε hε => ⟨0, fun n _ s' _ y => by simpa using hε.le⟩)
  have hnat : Tendsto (fun n : ℕ =>
      Parking.stoppingSup d (fun k z => Glim ((k : ℝ) / (n : ℝ))
          (Parking.spatialScaledSite n z)) ⌊(n : ℝ) * s⌋₊ (0 : Site d))
      atTop (𝓝 (Parking.spatialContValue (Parking.ofBrownianSpace B) PB Glim s)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hkey (ε / 2) (by linarith)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hN n hn) (by linarith)
  have hcomp := hnat.comp tendsto_nat_floor_sq_atTop
  have heq : (fun R : ℝ => spatialStopValueCutoff x s R G)
      = (fun R : ℝ => Parking.stoppingSup d (fun k z => Glim ((k : ℝ) / (⌊R ^ 2⌋₊ : ℝ))
          (Parking.spatialScaledSite ⌊R ^ 2⌋₊ z)) ⌊(⌊R ^ 2⌋₊ : ℝ) * s⌋₊ (0 : Site d)) := rfl
  rw [heq]
  exact hcomp

/-! ### The continuum functional is measurable (as the limit of uniformly `1`-Lipschitz
functions, no cross-integrability hypothesis needed) -/

theorem measurable_spatialContStopValue (hd1 : 1 ≤ d) (hd3 : d ≤ 3)
    (hStopping : Parking.External.SpatialStoppingStability)
    (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d)) (hB : LatticeProb.IsBrownianSpace d 0 B PB)
    (x : Fin d → ℝ) (s : ℝ) (hs : 0 < s)
    [MeasurableSpace (BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ)]
    [BorelSpace (BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ)] :
    Measurable (spatialContStopValue (d := d) B PB x s) :=
  Parking.Generic.LipschitzLimit.measurable_of_tendsto _ _
    (abs_spatialStopValueCutoff_sub_le hd1 x s)
    (tendsto_spatialStopValueCutoff hd1 hd3 hStopping ΩB PB B hB x s hs)

/-! ### The random cutoff value converges in law: the SINGLE-point, single-cutoff scalar
value convergence itself -/

/-- **The single-point, single-cutoff scalar value convergence**: the discrete stopping-value
functional, read at the REALIZED cutoff interpolated field `Parking.linHatInterp (w.1) R`,
converges in law, as `R → ∞`, to the continuum stopping-value functional read at
`Parking.External.LinearFieldScaling`'s witness field `Z`, for every bounded continuous test
function of the resulting real number.  `hFieldConv` is `LinearFieldScaling`'s own field-alone
weak-convergence clause (its 7th conjunct), consumed here already destructured, matching
`Parking.measurable_cutoffBC_linearField`'s own pattern. -/
theorem tendsto_integral_spatialStopValueCutoff (hd1 : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℤ) (hν : Parking.CriticalLaw ν)
    (hStopping : Parking.External.SpatialStoppingStability)
    (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d)) (hB : LatticeProb.IsBrownianSpace d 0 B PB)
    (x : Fin d → ℝ) (s : ℝ) (hs : 0 < s)
    (χ : ℝ × (Fin d → ℝ) → ℝ) (hχ : Parking.IsSpaceTimeTest χ)
    [MeasurableSpace (SpatBCF d)]
    [BorelSpace (SpatBCF d)]
    (Ω' : Type) [MeasurableSpace Ω'] (Q' : Measure Ω') [IsProbabilityMeasure Q']
    (Z : Ω' → ℝ → (Fin d → ℝ) → ℝ)
    (hZcont : ∀ ω', Continuous fun p : ℝ × (Fin d → ℝ) => Z ω' p.1 p.2)
    (hZmeas : ∀ r x, Measurable fun ω' => Z ω' r x)
    (hFieldConv :
      ∀ F : BoundedContinuousFunction (BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ) ℝ,
        Tendsto (fun R : ℝ =>
            ∫ w : Parking.Data d,
              F (Parking.cutoffBC χ (Parking.linHatInterp (fun y => (w.1 y : ℝ)) R)
                  hχ.1.continuous hχ.2.1
                  (Parking.continuous_linHatInterp (fun y => (w.1 y : ℝ)) R))
              ∂(Parking.law d ν))
          atTop
          (𝓝 (∫ ω', F (Parking.cutoffBC χ (fun p => Z ω' p.1 p.2) hχ.1.continuous hχ.2.1
                  (hZcont ω')) ∂Q')))
    (Gt : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun R : ℝ =>
        ∫ w : Parking.Data d, Gt (spatialStopValueCutoff x s R
            (Parking.cutoffBC χ (Parking.linHatInterp (fun y => (w.1 y : ℝ)) R)
                hχ.1.continuous hχ.2.1 (Parking.continuous_linHatInterp _ R)))
          ∂(Parking.law d ν))
      atTop
      (𝓝 (∫ ω' : Ω', Gt (spatialContStopValue B PB x s
            (Parking.cutoffBC χ (fun p => Z ω' p.1 p.2) hχ.1.continuous hχ.2.1 (hZcont ω')))
          ∂Q')) := by
  set cutoffDisc : ℝ → Parking.Data d → SpatBCF d := fun R w =>
    Parking.cutoffBC χ (Parking.linHatInterp (fun y => (w.1 y : ℝ)) R) hχ.1.continuous hχ.2.1
      (Parking.continuous_linHatInterp (fun y => (w.1 y : ℝ)) R) with hcutoffDisc
  set cutoffCont : Ω' → SpatBCF d := fun ω' =>
    Parking.cutoffBC χ (fun p => Z ω' p.1 p.2) hχ.1.continuous hχ.2.1 (hZcont ω')
    with hcutoffCont
  haveI hνprob : IsProbabilityMeasure ν := hν.prob
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by unfold LatticeProb.iidLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.stackLaw d) := LatticeProb.stackLaw_isProbability hd1
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  haveI hlawprob : IsProbabilityMeasure (Parking.law d ν) := by
    unfold Parking.law; infer_instance
  set νR : ℝ → Measure (SpatBCF d) := fun R => (Parking.law d ν).map (cutoffDisc R) with hνR
  set νlim : Measure (SpatBCF d) := Q'.map cutoffCont with hνlim
  have hmeasR : ∀ R, Measurable (cutoffDisc R) := fun R =>
    Parking.measurable_cutoffBC_linHatInterp d hd1 R χ hχ.1.continuous hχ.2.1
  have hmeasZ : Measurable cutoffCont :=
    Parking.measurable_cutoffBC_linearField Z hZcont hZmeas χ hχ.1.continuous hχ.2.1
  haveI hpmR : ∀ R, IsProbabilityMeasure (νR R) := fun R =>
    Measure.isProbabilityMeasure_map (hmeasR R).aemeasurable
  haveI hpmlim : IsProbabilityMeasure νlim :=
    Measure.isProbabilityMeasure_map hmeasZ.aemeasurable
  have hlim : ∀ G : BoundedContinuousFunction (SpatBCF d) ℝ,
      Tendsto (fun R : ℝ => ∫ y, G y ∂(νR R)) atTop (𝓝 (∫ y, G y ∂νlim)) := by
    intro G
    have h1 : ∀ R, (∫ y, G y ∂(νR R)) = ∫ w, G (cutoffDisc R w) ∂(Parking.law d ν) := fun R =>
      integral_map (hmeasR R).aemeasurable G.continuous.measurable.aestronglyMeasurable
    have h2 : (∫ y, G y ∂νlim) = ∫ ω', G (cutoffCont ω') ∂Q' :=
      integral_map hmeasZ.aemeasurable G.continuous.measurable.aestronglyMeasurable
    rw [Filter.tendsto_congr h1, h2]
    exact hFieldConv G
  have hfR : ∀ R, Measurable (spatialStopValueCutoff x s R : SpatBCF d → ℝ) := fun R =>
    measurable_spatialStopValueCutoff hd1 x s R
  have hf : Measurable (spatialContStopValue B PB x s : SpatBCF d → ℝ) :=
    measurable_spatialContStopValue hd1 hd3 hStopping ΩB PB B hB x s hs
  have hLip : ∀ (R : ℝ) (y x' : SpatBCF d),
      |spatialStopValueCutoff x s R y - spatialStopValueCutoff x s R x'| ≤ dist y x' :=
    fun R y x' => abs_spatialStopValueCutoff_sub_le hd1 x s R y x'
  have hpt : ∀ G : SpatBCF d, Tendsto (fun R => spatialStopValueCutoff x s R G) atTop
      (𝓝 (spatialContStopValue B PB x s G)) := fun G =>
    tendsto_spatialStopValueCutoff hd1 hd3 hStopping ΩB PB B hB x s hs G
  have hmain := Parking.tendsto_integral_comp_real_of_lipschitz νlim νR hlim
    (spatialContStopValue B PB x s) (spatialStopValueCutoff x s) hfR hf hLip hpt Gt
  have heqR : ∀ R : ℝ, (∫ y, Gt (spatialStopValueCutoff x s R y) ∂(νR R))
      = ∫ w, Gt (spatialStopValueCutoff x s R (cutoffDisc R w)) ∂(Parking.law d ν) := fun R =>
    integral_map (hmeasR R).aemeasurable
      (Gt.continuous.measurable.comp (hfR R)).aestronglyMeasurable
  have heqZ : (∫ y, Gt (spatialContStopValue B PB x s y) ∂νlim)
      = ∫ ω', Gt (spatialContStopValue B PB x s (cutoffCont ω')) ∂Q' :=
    integral_map hmeasZ.aemeasurable
      (Gt.continuous.measurable.comp hf).aestronglyMeasurable
  rw [heqZ] at hmain
  exact (Filter.tendsto_congr heqR).mp hmain

/-! ### The floor-rounding gap between the two horizons -/

/-- **The floor-rounding gap between `Parking.spatialStopValueCutoff`'s own horizon
`⌊⌊R²⌋₊·s⌋₊` and `Parking.barDivisible`'s horizon `⌊sR²⌋₊`, an `O(1)`-step bound.**  Consumes
`Parking.Generic.FloorGap.natFloor_sq_mul_sub_natFloor_horizon_le`, stated here in the exact
vocabulary of this file's own horizon term (the second component of `Parking.
spatialStopValueCutoff`'s definition). -/
theorem natFloor_sq_mul_sub_spatialStopHorizon_le (s R : ℝ) (hs : 0 < s) :
    ⌊s * R ^ 2⌋₊ - ⌊(⌊R ^ 2⌋₊ : ℝ) * s⌋₊ ≤ ⌊s⌋₊ + 1 :=
  Parking.Generic.FloorGap.natFloor_sq_mul_sub_natFloor_horizon_le s R hs

end Parking

end
