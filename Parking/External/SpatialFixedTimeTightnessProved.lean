import Parking.External.SpatialFixedTimeTightness
import Parking.Support.SandpileLawBridge
import Sandpile.Support.MainExplInterpolationTightness
import Sandpile.External.LocalCLTProved

/-!
# Spatial tightness of the parking odometer

The sandpile interpolation modulus transfers to the lattice-sampled parking
field through the centered mass law and the mesh-point estimate.
-/

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open Sandpile.Continuum

namespace Parking.External

/-- The fixed-time spatial modulus of the rescaled divisible odometer. -/
theorem spatialFixedTimeTightness : SpatialFixedTimeTightness := by
  intro d hd hd3 ν hν T hT K hK ε hε ε' hε'
  have := hν.prob
  let μ : Measure ℝ := ν.map (fun k : ℤ => (k : ℝ))
  have hm := Parking.criticalLaw_moments ν hν
  have : IsProbabilityMeasure μ := hm.1
  let A : Set (Space d) := (WithLp.toLp 2) '' K
  have hA : IsCompact A := hK.image (PiLp.continuous_toLp 2 _)
  obtain ⟨ρ, hρ, hAρ⟩ := hA.isBounded.subset_closedBall_lt 0 (0 : Space d)
  let K' : Set (Space d) := closedBall 0 (ρ + Real.sqrt d)
  have hK' : IsCompact K' := isCompact_closedBall 0 _
  obtain ⟨θ, hθ, hexp⟩ := hm.2.2.2.2.1
  obtain ⟨a, ha, hmod⟩ := Sandpile.exists_interpolation_modulus
    Sandpile.External.localCLT d hd hd3 μ hm.2.1 hm.2.2.1 hm.2.2.2.1
    θ hθ hexp T hT K' hK' ε' ε hε' hε
  obtain ⟨b, hb, hcont⟩ := Metric.uniformContinuous_iff.mp
    (PiLp.uniformContinuous_toLp 2 (fun _ : Fin d => ℝ)) (a / 3) (by positivity)
  refine ⟨b / 2, by positivity, max 1 (6 * Real.sqrt d / a + 1), ?_⟩
  intro R hR
  have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hmesh : Real.sqrt d / R < a / 6 := by
    have hR' := (le_max_right (1 : ℝ) (6 * Real.sqrt d / a + 1)).trans hR
    have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
    have : 6 * Real.sqrt d / a < R := by linarith
    apply (div_lt_iff₀ hRp).2
    have := (div_lt_iff₀ ha).1 this
    nlinarith
  let M : Data d → Site d → ℝ := fun w y => 1 + 2 * (d : ℝ) * (w.1 y : ℝ)
  have hM : Measurable M := by
    apply Measurable.of_eval
    intro y
    exact measurable_const.add (measurable_const.mul
      (measurable_intCastReal.comp ((measurable_pi_apply y).comp measurable_fst)))
  let F : (Site d → ℝ) → Space d → ℝ := fun σ z =>
    Sandpile.Continuum.multilinearInterp R
      (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y) z
  let E : Set (Site d → ℝ) := {σ | ∃ z ∈ K', ∃ z' ∈ K',
    dist z z' < a ∧ ε < |F σ z - F σ z'|}
  have hpoint : ∀ x ∈ K, Sandpile.Support.meshPoint R (WithLp.toLp 2 x) ∈ K' := by
    intro x hx
    have hxρ : ‖(WithLp.toLp 2 x : Space d)‖ ≤ ρ := by
      simpa only [mem_closedBall, dist_zero_right] using hAρ (show _ ∈ A from ⟨x, hx, rfl⟩)
    have hs := Sandpile.Support.norm_meshPoint_sub_le hRp (WithLp.toLp 2 x)
    have hs' : Real.sqrt d / R ≤ Real.sqrt d := div_le_self (Real.sqrt_nonneg _) hR1
    have ht := norm_add_le (Sandpile.Support.meshPoint R (WithLp.toLp 2 x) -
      (WithLp.toLp 2 x : Space d)) (WithLp.toLp 2 x)
    rw [sub_add_cancel] at ht
    simpa only [K', mem_closedBall, dist_zero_right] using (show
      ‖Sandpile.Support.meshPoint R (WithLp.toLp 2 x)‖ ≤ ρ + Real.sqrt d by linarith)
  have hdist : ∀ x y : Fin d → ℝ, dist x y ≤ b / 2 →
      dist (Sandpile.Support.meshPoint R (WithLp.toLp 2 x))
        (Sandpile.Support.meshPoint R (WithLp.toLp 2 y)) < a := by
    intro x y hxy
    have hxy' := hcont (show dist x y < b by linarith)
    have hx : dist (Sandpile.Support.meshPoint R (WithLp.toLp 2 x))
        (WithLp.toLp 2 x : Space d) ≤ Real.sqrt d / R := by
      simpa only [dist_eq_norm] using
        Sandpile.Support.norm_meshPoint_sub_le hRp (WithLp.toLp 2 x)
    have hy : dist (WithLp.toLp 2 y : Space d)
        (Sandpile.Support.meshPoint R (WithLp.toLp 2 y)) ≤ Real.sqrt d / R := by
      simpa only [dist_eq_norm, norm_sub_rev] using
        Sandpile.Support.norm_meshPoint_sub_le hRp (WithLp.toLp 2 y)
    have ht1 := dist_triangle (Sandpile.Support.meshPoint R (WithLp.toLp 2 x))
      (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    have ht2 := dist_triangle (Sandpile.Support.meshPoint R (WithLp.toLp 2 x))
      (WithLp.toLp 2 y) (Sandpile.Support.meshPoint R (WithLp.toLp 2 y))
    linarith
  have hsub : {w : Data d | ε < ⨆ x ∈ K, ⨆ y ∈ K, ⨆ _ : dist x y ≤ b / 2,
      |barDivisible w R T x - barDivisible w R T y|} ⊆ M ⁻¹' E := by
    intro w hw
    have hex : ∃ x ∈ K, ∃ y ∈ K, dist x y ≤ b / 2 ∧
        ε < |barDivisible w R T x - barDivisible w R T y| := by
      by_contra hn
      have hall : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ b / 2 →
          |barDivisible w R T x - barDivisible w R T y| ≤ ε := by
        push Not at hn
        exact hn
      have hsup : (⨆ x ∈ K, ⨆ y ∈ K, ⨆ _ : dist x y ≤ b / 2,
          |barDivisible w R T x - barDivisible w R T y|) ≤ ε :=
        Real.iSup_le (fun x => Real.iSup_le (fun hx => Real.iSup_le (fun y =>
          Real.iSup_le (fun hy => Real.iSup_le (fun hxy => hall x hx y hy hxy) hε.le)
            hε.le) hε.le) hε.le) hε.le
      exact not_lt_of_ge hsup hw
    obtain ⟨x, hx, y, hy, hxy, hlarge⟩ := hex
    refine ⟨_, hpoint x hx, _, hpoint y hy, hdist x y hxy, ?_⟩
    have hfield (z : Fin d → ℝ) :
        F (M w) (Sandpile.Support.meshPoint R (WithLp.toLp 2 z)) = barDivisible w R T z := by
      simpa only [F, M, Sandpile.Support.meshPoint] using
        (Parking.barDivisible_eq_sandpile_interp d hd w R T hRp z).symm
    rw [hfield x, hfield y]
    exact hlarge
  have hbound : law d ν {w | ε < ⨆ x ∈ K, ⨆ y ∈ K, ⨆ _ : dist x y ≤ b / 2,
      |barDivisible w R T x - barDivisible w R T y|} ≤ ENNReal.ofReal ε' := by
    calc
      _ ≤ law d ν (M ⁻¹' E) := measure_mono hsub
      _ ≤ (law d ν).map M E := Measure.le_map_apply hM.aemeasurable E
      _ = Sandpile.centeredMassLaw d μ E := by rw [Parking.law_map_mass d hd ν]
      _ ≤ ENNReal.ofReal ε' := hmod R hR1
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  simpa [ENNReal.toReal_ofReal hε'.le] using this

end Parking.External
