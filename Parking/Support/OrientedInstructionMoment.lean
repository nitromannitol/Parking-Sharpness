/- The moment bound for the directed error regrouped by instruction.

Each instruction is a fresh independent coordinate, read once, with the
cumulative discrepancy `Parking.orientedCumDisc` at the horizon it is alive for.
That horizon is determined by the odometer, hence by the instructions of the
layers strictly below, so it is chosen by the past out of the finitely many
horizons `0, …, n`.  This is exactly the situation of
`Parking.exists_finite_coordinate_moment_bound_sel`, and the quadratic variation
it returns is the odometer weighted by the layer variances at the selected
horizons, which `Parking.orientedGamma_eq_sum` bounds by the weights
`sup_M Gamma_M(y)` of `Parking.orientedSupCharge`.
-/
import Parking.Support.PredictableCoordinate
import Parking.Support.OrientedInstructionSum
import Parking.Support.OrientedSupCharge
import Parking.Support.SortedEnumeration

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
open scoped Classical
variable {d : ℕ}

/-- The alive count as a sum of indicators. -/
theorem orientedAlive_eq_sum (η : Site d → ℤ) (σ : Site d × ℕ → Site d) (n : ℕ) (y : Site d)
    (j : ℕ) :
    orientedAlive η σ n y j
      = ∑ m ∈ range n, if j < orientedOdometer η σ (n - 1 - m) y then 1 else 0 := by
  rw [orientedAlive, card_filter]

/-- **The horizon of an instruction is chosen by the past.**  In the layer-sorted
enumeration of the instructions, the alive count of the instruction at position
`j` is measurable for the coordinate filtration up to `j`. -/
theorem measurable_orientedAlive_coordinateFiltration {K : ℕ}
    (b : Site d × ℕ → Site d) (q : Fin K → Site d × ℕ)
    (hq : Monotone fun j => layerHeight (q j).1) (jj : Fin K) (n : ℕ) :
    Measurable[coordinateFiltration b q jj.val]
      fun z : (Site d → ℤ) × (Site d × ℕ → Site d) =>
        orientedAlive z.1 z.2 n (q jj).1 (q jj).2 := by
  have he : (fun z : (Site d → ℤ) × (Site d × ℕ → Site d) =>
      orientedAlive z.1 z.2 n (q jj).1 (q jj).2)
      = fun z => ∑ m ∈ range n,
          if (q jj).2 < orientedOdometer z.1 z.2 (n - 1 - m) (q jj).1 then 1 else 0 := by
    funext z; exact orientedAlive_eq_sum z.1 z.2 n (q jj).1 (q jj).2
  rw [he]
  refine Finset.measurable_sum _ fun m _ => ?_
  exact (measurable_from_countable' fun k : ℕ => if (q jj).2 < k then (1 : ℕ) else 0).comp
    (measurable_orientedOdometer_coordinateFiltration b q hq jj (n - 1 - m))

/-- The instruction sum of the directed error, with every departure stack
truncated at index `M`. -/
def orientedTruncatedInstr (S : Finset (Site d)) (n M : ℕ)
    (z : (Site d → ℤ) × (Site d × ℕ → Site d)) : ℝ :=
  ∑ y ∈ S, ∑ j ∈ range M, if j < orientedOdometer z.1 z.2 (n - 1) y then
    orientedCumDisc (orientedAlive z.1 z.2 n y j) y (z.2 (y, j)) else 0

/-- The truncated Green variance is below its supremum over horizons. -/
theorem orientedGamma_le_gammaSup (hd : 1 ≤ d) (m : ℕ) (y : Site d) :
    orientedGamma d m y ≤ ⨆ k : ℕ, orientedGamma d k y := by
  rw [orientedGammaSup_eq_tsum_charge hd y, orientedGamma_eq_sum]
  exact (summable_orientedCharge_site hd y).sum_le_tsum _
    (fun l _ => orientedCharge_nonneg l y)

/-- **The moment bound for the truncated instruction sum.**  Each instruction is
one fresh coordinate, read once at the horizon the past selects; the quadratic
variation is the odometer weighted by the layer variances, and the telescoping
identity turns it into the odometer moment at the origin. -/
theorem exists_oriented_instr_moment (hBern : External.Bernstein) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 2 ≤ d → ∀ (ν : Measure ℤ), CriticalLaw ν →
      ∀ (N n M : ℕ) (r : ℝ), 2 ≤ r →
      (∫ z, |orientedTruncatedInstr (boxFinset (0 : Site d) N) n M z| ^ r
        ∂((iidLaw d ν).prod (orientedStackLaw d))) ^ (1 / r) ≤
        C * (Real.sqrt r * (∫ ω : Data d, (U ω (n - 1) 0 : ℝ) ^ (r / 2)
          ∂(orientedLaw d ν)) ^ (1 / r) + r) := by
  obtain ⟨C, hC, hb⟩ := exists_finite_coordinate_moment_bound_sel hBern
  refine ⟨C, hC, fun d hd2 ν hν N n M r hr => ?_⟩
  have hd : 1 ≤ d := by omega
  haveI := hν.prob
  haveI : ∀ c : Site d × ℕ, IsProbabilityMeasure (orientedInstructionLaw c.1) :=
    fun c => orientedInstructionLaw_isProbability hd c.1
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  let T := (boxFinset (0 : Site d) N) ×ˢ range M
  obtain ⟨q, hq, hcov, hsort⟩ := exists_sorted_enumeration T (fun c => layerHeight c.1)
  let bb : Site d × ℕ → Site d := fun _ => 0
  let H : Fin T.card → (Site d → ℤ) × (Site d × ℕ → Site d) → ℝ :=
    fun j z => if (q j).2 < orientedOdometer z.1 z.2 (n - 1) (q j).1 then 1 else 0
  let sel : Fin T.card → (Site d → ℤ) × (Site d × ℕ → Site d) → Fin (n + 1) :=
    fun j z => ⟨min (orientedAlive z.1 z.2 n (q j).1 (q j).2) n,
      Nat.lt_succ_of_le (min_le_right _ _)⟩
  let g : (j : Fin T.card) → Fin (n + 1) → Site d → ℝ :=
    fun j Mi => orientedCumDisc (Mi : ℕ) (q j).1
  have hselalive : ∀ (j : Fin T.card) (z : (Site d → ℤ) × (Site d × ℕ → Site d)),
      ((sel j z : Fin (n + 1)) : ℕ) = orientedAlive z.1 z.2 n (q j).1 (q j).2 :=
    fun j z => min_eq_left (orientedAlive_le z.1 z.2 n (q j).1 (q j).2)
  have hH (j : Fin T.card) : Measurable[coordinateFiltration bb q j.val] (H j) :=
    (measurable_from_countable' fun N' : ℕ => if (q j).2 < N' then (1 : ℝ) else 0).comp
      (measurable_orientedOdometer_coordinateFiltration bb q hsort j (n - 1))
  have hsel (j : Fin T.card) : Measurable[coordinateFiltration bb q j.val] (sel j) :=
    (measurable_from_countable' fun k : ℕ =>
        (⟨min k n, Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (n + 1))).comp
      (measurable_orientedAlive_coordinateFiltration bb q hsort j n)
  have hHb (j : Fin T.card) (z : (Site d → ℤ) × (Site d × ℕ → Site d)) : |H j z| ≤ 1 := by
    dsimp only [H]; split_ifs <;> norm_num
  have h := hb (Site d → ℤ) (Site d × ℕ) (fun _ => Site d) inferInstance inferInstance
    inferInstance T.card (n + 1) (iidLaw d ν) inferInstance
    (fun c => orientedInstructionLaw c.1) inferInstance bb q hq H sel g r 1 hH hsel hHb
    (fun _ _ => Measurable.of_discrete) (fun j Mi x => abs_orientedCumDisc_le hd _ _ x)
    (fun j Mi => integral_orientedCumDisc hd _ _) hr zero_lt_one
  have hsum (z : (Site d → ℤ) × (Site d × ℕ → Site d)) :
      (∑ j : Fin T.card, H j z * g j (sel j z) (z.2 (q j))) = orientedTruncatedInstr (boxFinset (0 : Site d) N) n M z := by
    have he (j : Fin T.card) : H j z * g j (sel j z) (z.2 (q j)) =
        if (q j).2 < orientedOdometer z.1 z.2 (n - 1) (q j).1 then
          orientedCumDisc (orientedAlive z.1 z.2 n (q j).1 (q j).2) (q j).1 (z.2 (q j)) else 0 := by
      dsimp only [H, g]
      rw [hselalive j z]
      split_ifs <;> simp
    simp only [he]
    rw [sum_enumeration T q hq hcov (fun c =>
      if c.2 < orientedOdometer z.1 z.2 (n - 1) c.1 then
        orientedCumDisc (orientedAlive z.1 z.2 n c.1 c.2) c.1 (z.2 c) else 0), sum_product]
    rfl
  have hQV0 : ∀ z, (0 : ℝ) ≤ ∑ j : Fin T.card,
      H j z ^ 2 * ∫ x, g j (sel j z) x ^ 2 ∂(orientedInstructionLaw (q j).1) :=
    fun z => sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (integral_nonneg fun x => sq_nonneg _)
  have hsq (z : (Site d → ℤ) × (Site d × ℕ → Site d)) :
      (∑ j : Fin T.card, H j z ^ 2 * ∫ x, g j (sel j z) x ^ 2 ∂(orientedInstructionLaw (q j).1))
        ≤ orientedSupCharge d N (n - 1) z := by
    have he (j : Fin T.card) :
        H j z ^ 2 * (∫ x, g j (sel j z) x ^ 2 ∂(orientedInstructionLaw (q j).1))
          ≤ (if (q j).2 < orientedOdometer z.1 z.2 (n - 1) (q j).1 then (1 : ℝ) else 0) *
            (⨆ m : ℕ, orientedGamma d m (q j).1) := by
      dsimp only [H, g]
      rw [integral_orientedCumDisc_sq hd]
      split_ifs
      · simpa using orientedGamma_le_gammaSup hd _ (q j).1
      · simp
    refine le_trans (sum_le_sum fun j _ => he j) ?_
    rw [sum_enumeration T q hq hcov (fun c =>
      (if c.2 < orientedOdometer z.1 z.2 (n - 1) c.1 then (1 : ℝ) else 0) *
        (⨆ m : ℕ, orientedGamma d m c.1)), sum_product]
    rw [orientedSupCharge]
    refine sum_le_sum fun y _ => ?_
    dsimp only
    rw [← sum_mul, sum_range_lt_indicator]
    have hm : ((min M (orientedOdometer z.1 z.2 (n - 1) y) : ℕ) : ℝ)
        ≤ ((orientedOdometer z.1 z.2 (n - 1) y : ℕ) : ℝ) := by
      exact_mod_cast min_le_right M (orientedOdometer z.1 z.2 (n - 1) y)
    have hw : (0 : ℝ) ≤ ⨆ m : ℕ, orientedGamma d m y := orientedGammaSup_nonneg hd y
    nlinarith [hm, hw]
  obtain ⟨hSCint, hSCle⟩ :=
    orientedSupCharge_moment (d := d) hd2 ν hν N (n - 1) (p := r / 2) (by linarith)
  have hmono : (∫ z, (∑ j : Fin T.card,
        H j z ^ 2 * ∫ x, g j (sel j z) x ^ 2 ∂(orientedInstructionLaw (q j).1)) ^ (r / 2)
      ∂((iidLaw d ν).prod (orientedStackLaw d)))
      ≤ ∫ ω : Data d, (U ω (n - 1) 0 : ℝ) ^ (r / 2) ∂(orientedLaw d ν) := by
    refine le_trans (integral_mono_of_nonneg
      (ae_of_all _ fun z => Real.rpow_nonneg (hQV0 z) _) hSCint
      (ae_of_all _ fun z => Real.rpow_le_rpow (hQV0 z) (hsq z) (by linarith))) hSCle
  have hfin : (∫ z, |orientedTruncatedInstr (boxFinset (0 : Site d) N) n M z| ^ r
        ∂((iidLaw d ν).prod (orientedStackLaw d))) ^ (1 / r) ≤
      C * (Real.sqrt r * (∫ z, (∑ j : Fin T.card,
          H j z ^ 2 * ∫ x, g j (sel j z) x ^ 2 ∂(orientedInstructionLaw (q j).1)) ^ (r / 2)
        ∂((iidLaw d ν).prod (orientedStackLaw d))) ^ (1 / r) + r) := by
    simpa only [hsum, mul_one, orientedStackLaw] using h
  refine hfin.trans (mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (integral_nonneg fun z => Real.rpow_nonneg (hQV0 z) _) hmono
        (by positivity)) (Real.sqrt_nonneg r)) le_rfl) hC.le)

end Parking
end
