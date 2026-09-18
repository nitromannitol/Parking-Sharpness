/-
The real-parameter (filter) form of the scalar triangular-array characteristic-function CLT,
`Parking.Support.SpatCLT.tendsto_charFun_weighted_scenery_sum`, needed because
`prop:spatial-scaling`'s clauses (`parking.tex:1679-1737`) are all stated as `R → ∞` limits over
a REAL parameter `R : ℝ`, not a sequence indexed by `ℕ`.  Nothing in the ℕ-indexed proof uses any
property of `ℕ` beyond being an index set for a filter: every step is `Filter.Tendsto`,
`Filter.Eventually`/`filter_upwards`, and `ge_of_tendsto'` (which needs only `[l.NeBot]` on the
ambient filter, for any filter on any type).  This module transcribes that proof verbatim with
the index type generalized from `(ℕ, Filter.atTop)` to an arbitrary `(ι, l)` with `[l.NeBot]`,
so it applies directly with `ι := ℝ`, `l := Filter.atTop` to the scenery pairing's own rescaling
parameter `R`.
-/
import Parking.Support.SpatCLT

open MeasureTheory LatticeProb ProbabilityTheory Filter Complex
open scoped Topology RealInnerProductSpace InnerProductSpace

noncomputable section
namespace Parking

/-- **The characteristic function of a triangular family of finitely-supported weighted i.i.d.
sums over `Site d`, indexed by an arbitrary filter, converges to the Gaussian one**, provided
the weights' squares sum to a limit `V` and are uniformly negligible.  The real-parameter form of
`Parking.Support.SpatCLT.tendsto_charFun_weighted_scenery_sum`, identical proof, generalized from
`(ℕ, atTop)` to any `(ι, l)` with `[l.NeBot]`. -/
theorem tendsto_charFun_weighted_scenery_sum_filter {ι : Type*} {l : Filter ι} [l.NeBot] {d : ℕ} (ν : Measure ℤ) (hν : CriticalLaw ν)
    (S : ι → Finset (Site d)) (c : ι → Site d → ℝ) (t : ℝ) {V : ℝ}
    (hV : Tendsto (fun i => ∑ w ∈ S i, (c i w) ^ 2) l (𝓝 V))
    (M : ι → ℝ) (hM : Tendsto M l (𝓝 0)) (hMd : ∀ i, ∀ w ∈ S i, |c i w| ≤ M i) :
    Tendsto (fun i : ι => charFun ((iidLaw d (realLaw ν)).map
        (fun η : Site d → ℝ => ∑ w ∈ S i, c i w * η w)) t) l
      (𝓝 (Complex.exp (-((∫ x : ℝ, x ^ 2 ∂(realLaw ν) : ℝ) : ℂ) * (V : ℂ) * (t : ℂ) ^ 2 / 2))) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  set σ2 : ℝ := ∫ x : ℝ, x ^ 2 ∂(realLaw ν) with hσ2
  have hσ2nonneg : 0 ≤ σ2 := by rw [hσ2]; exact integral_nonneg fun x => sq_nonneg x
  have hprodeq : ∀ i : ι, charFun ((iidLaw d (realLaw ν)).map
      (fun η : Site d → ℝ => ∑ w ∈ S i, c i w * η w)) t
      = ∏ w ∈ S i, charFun (realLaw ν) (t * c i w) :=
    fun i => charFun_map_weighted_sum_eq_prod ν hν (S i) (c i) t
  have hVnonneg : 0 ≤ V :=
    ge_of_tendsto' hV (fun i => Finset.sum_nonneg fun w _ => sq_nonneg (c i w))
  have hnegligible : ∀ δ' : ℝ, 0 < δ' → ∀ᶠ i : ι in l, ∀ w ∈ S i, |t * c i w| < δ' := by
    intro δ' hδ'pos
    rcases eq_or_ne t 0 with ht0 | ht0
    · filter_upwards [] with i w _
      simp [ht0, hδ'pos]
    · have hδt : (0 : ℝ) < δ' / |t| := by positivity
      filter_upwards [hM.eventually (eventually_lt_nhds hδt)] with i hn w hw
      have h1 : |t * c i w| ≤ |t| * M i := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hMd i w hw) (abs_nonneg t)
      have h2 : |t| * M i < |t| * (δ' / |t|) :=
        mul_lt_mul_of_pos_left hn (abs_pos.mpr ht0)
      have h3 : |t| * (δ' / |t|) = δ' := by field_simp
      linarith
  have hLsum : Tendsto (fun i : ι => ∑ w ∈ S i, Complex.log (charFun (realLaw ν) (t * c i w)))
      l (𝓝 (-(σ2 : ℂ) * (V : ℂ) * (t : ℂ) ^ 2 / 2)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set B : ℝ := t ^ 2 * (V + 1) + 1 with hB
    have hBpos : 0 < B := by
      rw [hB]; nlinarith [sq_nonneg t, hVnonneg]
    set ε' : ℝ := ε / (2 * B) with hε'
    have hε'pos : 0 < ε' := by rw [hε']; positivity
    obtain ⟨δ, hδpos, hδ⟩ := exists_spatLog_charFun_realLaw ν hν ε' hε'pos
    have hMev : ∀ᶠ i : ι in l, ∀ w ∈ S i, |t * c i w| < δ := hnegligible δ hδpos
    set D : ℝ := σ2 * t ^ 2 / 2 with hD
    have hDnonneg : 0 ≤ D := by rw [hD]; nlinarith [hσ2nonneg, sq_nonneg t]
    have hDp1pos : 0 < D + 1 := by linarith
    set C : ℝ := min (ε / 2 / (D + 1)) 1 with hC
    have hCpos : 0 < C := by
      rw [hC]; exact lt_min (div_pos (by linarith) hDp1pos) (by norm_num)
    have hCleD1 : C ≤ ε / 2 / (D + 1) := by rw [hC]; exact min_le_left _ _
    have hCle1 : C ≤ 1 := by rw [hC]; exact min_le_right _ _
    have hVclose : ∀ᶠ i : ι in l, |∑ w ∈ S i, (c i w) ^ 2 - V| < C := by
      have h := Metric.tendsto_nhds.mp hV C hCpos
      filter_upwards [h] with i hn
      rwa [Real.dist_eq] at hn
    filter_upwards [hMev, hVclose] with i hn hCn
    have hVn : ∑ w ∈ S i, (c i w) ^ 2 ≤ V + 1 := by
      have := (abs_lt.mp hCn).2
      linarith
    have herrbound : ∀ w ∈ S i,
        ‖Complex.log (charFun (realLaw ν) (t * c i w)) +
            (σ2 : ℂ) * ((t * c i w : ℝ) : ℂ) ^ 2 / 2‖
          ≤ ε' * (t * c i w) ^ 2 :=
      fun w hw => (hδ (t * c i w) (hn w hw)).2
    have hsumerr : ‖∑ w ∈ S i, (Complex.log (charFun (realLaw ν) (t * c i w)) +
          (σ2 : ℂ) * ((t * c i w : ℝ) : ℂ) ^ 2 / 2)‖ ≤ ε' * t ^ 2 * ∑ w ∈ S i, (c i w) ^ 2 := by
      calc ‖∑ w ∈ S i, (Complex.log (charFun (realLaw ν) (t * c i w)) +
              (σ2 : ℂ) * ((t * c i w : ℝ) : ℂ) ^ 2 / 2)‖
          ≤ ∑ w ∈ S i, ‖Complex.log (charFun (realLaw ν) (t * c i w)) +
              (σ2 : ℂ) * ((t * c i w : ℝ) : ℂ) ^ 2 / 2‖ := norm_sum_le _ _
        _ ≤ ∑ w ∈ S i, ε' * (t * c i w) ^ 2 := Finset.sum_le_sum herrbound
        _ = ε' * t ^ 2 * ∑ w ∈ S i, (c i w) ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun w _ => ?_
            ring
    have hsumdecomp : (∑ w ∈ S i, Complex.log (charFun (realLaw ν) (t * c i w)))
        + (σ2 : ℂ) * (t : ℂ) ^ 2 / 2 * (∑ w ∈ S i, ((c i w : ℂ)) ^ 2)
        = ∑ w ∈ S i, (Complex.log (charFun (realLaw ν) (t * c i w)) +
            (σ2 : ℂ) * ((t * c i w : ℝ) : ℂ) ^ 2 / 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun w _ => ?_
      push_cast
      ring
    have hsumcast : (∑ w ∈ S i, ((c i w : ℂ)) ^ 2) = ((∑ w ∈ S i, (c i w) ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [Complex.dist_eq]
    have hfinalbound : ‖(∑ w ∈ S i, Complex.log (charFun (realLaw ν) (t * c i w))) -
        (-(σ2 : ℂ) * (V : ℂ) * (t : ℂ) ^ 2 / 2)‖
        ≤ ε' * t ^ 2 * ∑ w ∈ S i, (c i w) ^ 2 +
          σ2 * t ^ 2 / 2 * |∑ w ∈ S i, (c i w) ^ 2 - V| := by
      have hrewrite : (∑ w ∈ S i, Complex.log (charFun (realLaw ν) (t * c i w))) -
          (-(σ2 : ℂ) * (V : ℂ) * (t : ℂ) ^ 2 / 2)
          = (∑ w ∈ S i, (Complex.log (charFun (realLaw ν) (t * c i w)) +
              (σ2 : ℂ) * ((t * c i w : ℝ) : ℂ) ^ 2 / 2)) -
            (σ2 : ℂ) * (t : ℂ) ^ 2 / 2 * (((∑ w ∈ S i, (c i w) ^ 2 : ℝ) : ℂ) - (V : ℂ)) := by
        rw [← hsumdecomp, ← hsumcast]
        ring
      rw [hrewrite]
      refine (norm_sub_le _ _).trans ?_
      refine add_le_add hsumerr ?_
      have hcast2 : ((σ2 : ℂ) * (t : ℂ) ^ 2 / 2 *
          (((∑ w ∈ S i, (c i w) ^ 2 : ℝ) : ℂ) - (V : ℂ)))
          = (((σ2 * t ^ 2 / 2 * (∑ w ∈ S i, (c i w) ^ 2 - V) : ℝ)) : ℂ) := by
        push_cast; ring
      rw [hcast2, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      have hnn : (0:ℝ) ≤ σ2 * t ^ 2 / 2 := by nlinarith [hσ2nonneg, sq_nonneg t]
      rw [abs_of_nonneg hnn]
    refine lt_of_le_of_lt hfinalbound ?_
    have h1 : ε' * t ^ 2 * ∑ w ∈ S i, (c i w) ^ 2 ≤ ε' * B := by
      have hε'nn : 0 ≤ ε' := hε'pos.le
      have ht2nn : 0 ≤ t ^ 2 := sq_nonneg t
      calc ε' * t ^ 2 * ∑ w ∈ S i, (c i w) ^ 2 ≤ ε' * t ^ 2 * (V + 1) := by
            apply mul_le_mul_of_nonneg_left hVn (by positivity)
        _ ≤ ε' * B := by rw [hB]; nlinarith
    have h2 : σ2 * t ^ 2 / 2 * |∑ w ∈ S i, (c i w) ^ 2 - V| < ε / 2 := by
      rw [← hD]
      calc D * |∑ w ∈ S i, (c i w) ^ 2 - V| ≤ D * C :=
            mul_le_mul_of_nonneg_left hCn.le hDnonneg
        _ ≤ D * (ε / 2 / (D + 1)) := mul_le_mul_of_nonneg_left hCleD1 hDnonneg
        _ < ε / 2 := by
            rw [mul_div_assoc', div_lt_iff₀ hDp1pos]
            nlinarith [hε]
    have h3 : ε' * B = ε / 2 := by
      rw [hε']; field_simp
    linarith [h1, h2, h3.le]
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := exists_spatLog_charFun_realLaw ν hν 1 one_pos
  have hne_ev : ∀ᶠ i : ι in l, ∀ w ∈ S i, charFun (realLaw ν) (t * c i w) ≠ 0 := by
    filter_upwards [hnegligible δ₁ hδ₁pos] with i hn w hw
    exact (hδ₁ (t * c i w) (hn w hw)).1
  have hprodexp : (fun i : ι => ∏ w ∈ S i, charFun (realLaw ν) (t * c i w)) =ᶠ[l]
      (fun i : ι => Complex.exp (∑ w ∈ S i, Complex.log (charFun (realLaw ν) (t * c i w)))) := by
    filter_upwards [hne_ev] with i hn
    rw [Complex.exp_sum]
    exact Finset.prod_congr rfl fun w hw => (Complex.exp_log (hn w hw)).symm
  have hexpconv : Tendsto (fun i : ι => Complex.exp
      (∑ w ∈ S i, Complex.log (charFun (realLaw ν) (t * c i w)))) l
      (𝓝 (Complex.exp (-(σ2 : ℂ) * (V : ℂ) * (t : ℂ) ^ 2 / 2))) :=
    (Complex.continuous_exp.tendsto _).comp hLsum
  have hprodconv : Tendsto (fun i : ι => ∏ w ∈ S i, charFun (realLaw ν) (t * c i w)) l
      (𝓝 (Complex.exp (-(σ2 : ℂ) * (V : ℂ) * (t : ℂ) ^ 2 / 2))) :=
    hexpconv.congr' hprodexp.symm
  exact hprodconv.congr' (Filter.Eventually.of_forall fun i => (hprodeq i).symm)


end Parking
end
