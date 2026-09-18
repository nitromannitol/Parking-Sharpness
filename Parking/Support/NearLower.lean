/-
Step 2 of `prop:near-divisible` (`parking.tex:2861-2879`), up to the optimization
over the horizon.

The paper writes "the comparison eq:near-convex, positive homogeneity, and
Theorem thm:BP give `E u_m(0;ξ_δ) ≥ c φ(m)` for all large `m`, uniformly in `δ`",
and then "an optimizer for `u_m(0;ξ_δ)` is a competitor for the `η_δ` problem,
and hence `u^δ_∞(0) ≥ u_m(0;ξ_δ) - δm`".

Here the two steps are separated.  The competitor statement is `Parking.u_xi_le`,
proved from the perturbation bound of the odometer rather than from the stopping
representation: the two sceneries differ by the constant `δ` at every site, so
their odometers differ by at most `δm` at the horizon `m`.  The comparison is
`Parking.exists_twoPoint_comparison` of `Parking/Support/TwoPointOrder.lean` fed
into the coordinatewise convex comparison `Parking.integral_u_iid_le`; positive
homogeneity is not needed, because `thm:BP` is stated for an arbitrary mean zero
law with a positive finite variance and an exponential moment, and the symmetric
two point law at `±a₀` is such a law.

`Parking.lowerRate` is the rate of the lower half of `thm:BP`: `m^{(4-d)/4}` below
dimension four, `log m` in dimension four and `(log m)^{2/d}` above it.
-/
import Parking.Support.TwoPointOrder
import Parking.Support.CriticalLawReal
import Parking.Support.CriticalChain

open MeasureTheory ProbabilityTheory LatticeProb

noncomputable section
namespace Parking
variable {d : ℕ}

theorem shiftLaw_zero (ν : Measure ℤ) : shiftLaw 0 ν = realLaw ν := by
  rw [shiftLaw, realLaw]
  simp

/-- The recentred odometer exceeds the odometer by at most `δ m`. -/
theorem u_xi_le (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 ≤ δ) (η : Site d → ℤ) (m : ℕ) (x : Site d) :
    u (Parking.xi δ η) m x ≤ u (Parking.xi 0 η) m x + δ * m := by
  have hdiff : ∀ y : Site d, |Parking.xi δ η y - Parking.xi 0 η y| ≤ δ := by
    intro y
    have he : Parking.xi δ η y - Parking.xi 0 η y = δ := by simp [Parking.xi]
    rw [he, abs_of_nonneg hδ]
  have h := abs_u_sub_le hd hδ hdiff m x
  have h3 := (abs_le.mp h).2
  linarith

/-- The recentred mean odometer exceeds the mean odometer by at most `δ m`. -/
theorem integral_u_shift_le_meanu (hd : 1 ≤ d) {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ}
    (hfam : NearFamily δ₀ ν θ M K) {δ : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) δ₀) (m : ℕ) :
    (∫ ζ, u ζ m 0 ∂(LatticeProb.iidLaw d (shiftLaw δ (ν δ)))) - δ * m
      ≤ meanu (law d (ν δ)) m := by
  obtain ⟨hδ₀, hθ, hprob, hmeanν, -, hexp, -⟩ := hfam
  haveI hpν : IsProbabilityMeasure (ν δ) := hprob δ hδ
  have hintexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) (ν δ) := (hexp δ hδ).1
  have hintid : Integrable (fun k : ℤ => ((k : ℝ))) (ν δ) :=
    integrable_intCast_of_exp hθ (ν δ) hintexp
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d (ν δ)) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hxim : ∀ e : ℝ, Measurable (fun η : Site d → ℤ => Parking.xi e η) := fun e =>
    measurable_pi_lambda _ fun y =>
      (measurable_intCastReal.comp (measurable_pi_apply y)).add_const e
  have hmap : ∀ e : ℝ, ∫ ζ, u ζ m 0 ∂(LatticeProb.iidLaw d (shiftLaw e (ν δ)))
      = ∫ η, u (Parking.xi e η) m 0 ∂(LatticeProb.iidLaw d (ν δ)) := by
    intro e
    rw [← law_map_xi (d := d) e (ν δ)]
    exact integral_map (hxim e).aemeasurable (measurable_u_eval m 0).aestronglyMeasurable
  have hIδ : Integrable (fun η : Site d → ℤ => u (Parking.xi δ η) m 0)
      (LatticeProb.iidLaw d (ν δ)) := by
    have hbase : Integrable (fun ζ : Site d → ℝ => u ζ m 0)
        (LatticeProb.iidLaw d (shiftLaw δ (ν δ))) :=
      integrable_u_iid hd _ (integrable_id_shiftLaw δ (ν δ) hintid) m 0
    rw [← law_map_xi (d := d) δ (ν δ)] at hbase
    exact (integrable_map_measure (measurable_u_eval m 0).aestronglyMeasurable
      (hxim δ).aemeasurable).mp hbase
  have hI0 : Integrable (fun η : Site d → ℤ => u (Parking.xi 0 η) m 0)
      (LatticeProb.iidLaw d (ν δ)) := by
    have hbase : Integrable (fun ζ : Site d → ℝ => u ζ m 0)
        (LatticeProb.iidLaw d (shiftLaw 0 (ν δ))) :=
      integrable_u_iid hd _ (integrable_id_shiftLaw 0 (ν δ) hintid) m 0
    rw [← law_map_xi (d := d) 0 (ν δ)] at hbase
    exact (integrable_map_measure (measurable_u_eval m 0).aestronglyMeasurable
      (hxim 0).aemeasurable).mp hbase
  have hmeanu : meanu (law d (ν δ)) m
      = ∫ η, u (Parking.xi 0 η) m 0 ∂(LatticeProb.iidLaw d (ν δ)) := by
    rw [meanu_eq_meanSandpileReal hd (ν δ) m, Parking.External.meanSandpileReal,
      ← shiftLaw_zero (ν δ), hmap 0]
  rw [hmeanu, hmap δ]
  have hmono : ∫ η, u (Parking.xi δ η) m 0 ∂(LatticeProb.iidLaw d (ν δ))
      ≤ ∫ η, (u (Parking.xi 0 η) m 0 + δ * m) ∂(LatticeProb.iidLaw d (ν δ)) :=
    integral_mono hIδ (hI0.add (integrable_const _)) (fun η => u_xi_le hd hδ.1 η m 0)
  rw [integral_add hI0 (integrable_const _), integral_const] at hmono
  simp only [probReal_univ, smul_eq_mul, one_mul] at hmono
  linarith

/-- The three lower rates of `thm:BP`. -/
def lowerRate (d : ℕ) (m : ℕ) : ℝ :=
  if d ≤ 3 then (m : ℝ) ^ ((4 - (d:ℝ)) / 4)
  else if d = 4 then Real.log m
  else (Real.log m) ^ ((2:ℝ) / d)

/-- **`thm:BP` at the two point law.**  The mean odometer of the symmetric two point
scenery is at least a constant times the rate of `thm:BP`. -/
theorem exists_meanSandpile_twoPoint_lower (hd : 1 ≤ d)
    (hGrowth : Parking.External.SandpileGrowth) {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 2 ≤ m →
      c * lowerRate d m ≤ Parking.External.meanSandpileReal d (twoPointLaw a₀) m := by
  have hmean : ∫ z, z ∂(twoPointLaw a₀) = 0 := integral_twoPointLaw_id a₀
  have hv0 : 0 < evariance (id : ℝ → ℝ) (twoPointLaw a₀) := evariance_twoPointLaw_pos ha₀
  have hvT : evariance (id : ℝ → ℝ) (twoPointLaw a₀) < ⊤ := evariance_twoPointLaw_lt_top a₀
  have hexp : ∃ θ : ℝ, 0 < θ ∧
      Integrable (fun z : ℝ => Real.exp (θ * |z|)) (twoPointLaw a₀) :=
    ⟨1, one_pos, integrable_twoPointLaw a₀ _⟩
  obtain ⟨h3, h4, h5, -, -⟩ := hGrowth d hd (twoPointLaw a₀) inferInstance hmean hv0 hvT hexp
  by_cases hd3 : d ≤ 3
  · obtain ⟨c, C, hc, hC, h⟩ := h3 hd3
    exact ⟨c, hc, fun m hm => by rw [lowerRate, if_pos hd3]; exact (h m hm).1⟩
  by_cases hd4 : d = 4
  · obtain ⟨c, C, hc, hC, h⟩ := h4 hd4
    exact ⟨c, hc, fun m hm => by
      rw [lowerRate, if_neg hd3, if_pos hd4]; exact (h m hm).1⟩
  · have hd5 : 5 ≤ d := by omega
    obtain ⟨c, C, hc, hC, h⟩ := h5 hd5
    exact ⟨c, hc, fun m hm => by
      rw [lowerRate, if_neg hd3, if_neg hd4]; exact (h m hm).1⟩

/-- **Step 2 of `prop:near-divisible`** (`parking.tex:2861-2879`), before the optimization
over the horizon.  The comparison `eq:near-convex` replaces the recentred scenery by the
symmetric two point scenery, and `thm:BP` bounds the latter from below. -/
theorem exists_meanu_lower (hd : 1 ≤ d) (hGrowth : Parking.External.SandpileGrowth)
    {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ} (hfam : NearFamily δ₀ ν θ M K) :
    ∃ c δ₁ : ℝ, 0 < c ∧ 0 < δ₁ ∧ δ₁ ≤ δ₀ ∧ ∀ δ ∈ Set.Ioc (0:ℝ) δ₁, ∀ m : ℕ, 2 ≤ m →
      c * lowerRate d m - δ * m ≤ meanu (law d (ν δ)) m := by
  have hfam' : NearFamily δ₀ ν θ M K := hfam
  obtain ⟨hδ₀, hθ, hprob, hmeanν, -, hexp, -⟩ := hfam
  obtain ⟨a₀, δ₁, ha₀, hδ₁, hδ₁₀, hcmp⟩ := exists_twoPoint_comparison hfam'
  obtain ⟨c, hc, hlow⟩ := exists_meanSandpile_twoPoint_lower hd hGrowth ha₀
  refine ⟨c, δ₁, hc, hδ₁, hδ₁₀, fun δ hδ m hm => ?_⟩
  have hδicc : δ ∈ Set.Icc (0:ℝ) δ₀ := ⟨hδ.1.le, le_trans hδ.2 hδ₁₀⟩
  haveI hpν : IsProbabilityMeasure (ν δ) := hprob δ hδicc
  have hintexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) (ν δ) := (hexp δ hδicc).1
  have hintid : Integrable (fun k : ℤ => ((k : ℝ))) (ν δ) :=
    integrable_intCast_of_exp hθ (ν δ) hintexp
  have hcompare : Parking.External.meanSandpileReal d (twoPointLaw a₀) m
      ≤ ∫ ζ, u ζ m 0 ∂(LatticeProb.iidLaw d (shiftLaw δ (ν δ))) :=
    integral_u_iid_le hd (integrable_twoPointLaw a₀ _)
      (integrable_id_shiftLaw δ (ν δ) hintid) (hcmp δ hδ) m 0
  have hstep := integral_u_shift_le_meanu hd hfam' hδicc m
  have hbp := hlow m hm
  linarith
