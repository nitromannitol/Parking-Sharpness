/- Removing the stack cutoff from the directed instruction estimate, and the
resulting moment bound on the directed error field at the origin.

This is the first display of `prop:w-moment` for the directed kernel, with
`kappa_d(n)` replaced by one, which is what Step 1 of the proof of
`thm:oriented-walk` (`parking.tex:3238-3277`) asserts.
-/
import Parking.Support.OrientedInstructionMoment

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
open scoped Classical
variable {d : ℕ}

/-- Each instruction's contribution is measurable: its horizon is a finite sum
of odometer indicators and its arrival site is one coordinate. -/
theorem measurable_orientedCumDisc_term (n : ℕ) (y : Site d) (j : ℕ) :
    Measurable fun z : (Site d → ℤ) × (Site d × ℕ → Site d) =>
      orientedCumDisc (orientedAlive z.1 z.2 n y j) y (z.2 (y, j)) := by
  have hA : Measurable fun z : (Site d → ℤ) × (Site d × ℕ → Site d) =>
      orientedAlive z.1 z.2 n y j := by
    have he : (fun z : (Site d → ℤ) × (Site d × ℕ → Site d) => orientedAlive z.1 z.2 n y j)
        = fun z => ∑ m ∈ range n,
            if j < orientedOdometer z.1 z.2 (n - 1 - m) y then 1 else 0 := by
      funext z; exact orientedAlive_eq_sum z.1 z.2 n y j
    rw [he]
    exact Finset.measurable_sum _ fun m _ =>
      (measurable_from_countable' fun k : ℕ => if j < k then (1 : ℕ) else 0).comp
        (measurable_orientedOdometer _ _ measurable_fst measurable_snd (n - 1 - m) y)
  have hz : Measurable fun z : (Site d → ℤ) × (Site d × ℕ → Site d) => z.2 (y, j) :=
    (measurable_pi_apply (y, j)).comp measurable_snd
  exact (measurable_from_countable' fun p : ℕ × Site d => orientedCumDisc p.1 y p.2).comp
    (hA.prodMk hz)

/-- The instruction sum of the directed error with no cutoff on the stacks. -/
def orientedFiniteInstr (S : Finset (Site d)) (n : ℕ)
    (z : (Site d → ℤ) × (Site d × ℕ → Site d)) : ℝ :=
  ∑ y ∈ S, ∑ j ∈ range (orientedOdometer z.1 z.2 (n - 1) y),
    orientedCumDisc (orientedAlive z.1 z.2 n y j) y (z.2 (y, j))

theorem orientedTruncatedInstr_eq_of_le (S : Finset (Site d)) (n M : ℕ)
    (z : (Site d → ℤ) × (Site d × ℕ → Site d))
    (hM : ∀ y ∈ S, orientedOdometer z.1 z.2 (n - 1) y ≤ M) :
    orientedTruncatedInstr S n M z = orientedFiniteInstr S n z := by
  refine sum_congr rfl fun y hy => ?_
  rw [sum_range_ite_lt, min_eq_right (hM y hy)]

theorem orientedTruncatedInstr_eventually_eq (S : Finset (Site d)) (n : ℕ)
    (z : (Site d → ℤ) × (Site d × ℕ → Site d)) :
    ∀ᶠ M in Filter.atTop, orientedTruncatedInstr S n M z = orientedFiniteInstr S n z := by
  filter_upwards [Filter.eventually_ge_atTop
    (S.sup fun y => orientedOdometer z.1 z.2 (n - 1) y)] with M hM
  exact orientedTruncatedInstr_eq_of_le S n M z fun y hy =>
    (le_sup (f := fun y => orientedOdometer z.1 z.2 (n - 1) y) hy).trans hM

theorem abs_orientedFiniteInstr_le (hd : 1 ≤ d) (S : Finset (Site d)) (n : ℕ)
    (z : (Site d → ℤ) × (Site d × ℕ → Site d)) :
    |orientedFiniteInstr S n z| ≤ ∑ y ∈ S, (orientedOdometer z.1 z.2 (n - 1) y : ℝ) := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun y _ => ?_)
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have h := sum_le_sum (s := range (orientedOdometer z.1 z.2 (n - 1) y))
    (fun j _ => abs_orientedCumDisc_le hd (orientedAlive z.1 z.2 n y j) y (z.2 (y, j)))
  simpa using h

theorem abs_orientedTruncatedInstr_le (hd : 1 ≤ d) (S : Finset (Site d)) (n M : ℕ)
    (z : (Site d → ℤ) × (Site d × ℕ → Site d)) :
    |orientedTruncatedInstr S n M z| ≤ ∑ y ∈ S, (orientedOdometer z.1 z.2 (n - 1) y : ℝ) := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun y _ => ?_)
  rw [← sum_filter]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hsub : (range M).filter (fun j => j < orientedOdometer z.1 z.2 (n - 1) y)
      ⊆ range (orientedOdometer z.1 z.2 (n - 1) y) := by
    intro j hj
    simp only [mem_filter, mem_range] at hj ⊢
    exact hj.2
  refine le_trans (sum_le_sum fun j _ =>
    abs_orientedCumDisc_le hd (orientedAlive z.1 z.2 n y j) y (z.2 (y, j))) ?_
  have h1 : ∑ _j ∈ (range M).filter (fun j => j < orientedOdometer z.1 z.2 (n - 1) y), (1 : ℝ)
      ≤ ∑ _j ∈ range (orientedOdometer z.1 z.2 (n - 1) y), (1 : ℝ) :=
    sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => zero_le_one
  simpa using h1

theorem measurable_orientedFiniteInstr (S : Finset (Site d)) (n : ℕ) :
    Measurable (orientedFiniteInstr S n) := by
  refine Finset.measurable_sum _ fun y _ => ?_
  refine measurable_of_countable_partition (fun z => orientedOdometer z.1 z.2 (n - 1) y)
    (measurable_orientedOdometer _ _ measurable_fst measurable_snd _ _) _
    (fun N z => ∑ j ∈ range N,
      orientedCumDisc (orientedAlive z.1 z.2 n y j) y (z.2 (y, j))) ?_ (fun _ => rfl)
  intro N
  exact Finset.measurable_sum _ fun j _ => measurable_orientedCumDisc_term n y j

theorem measurable_orientedTruncatedInstr (S : Finset (Site d)) (n M : ℕ) :
    Measurable (orientedTruncatedInstr S n M) := by
  refine Finset.measurable_sum _ fun y _ => Finset.measurable_sum _ fun j _ => ?_
  exact Measurable.ite (measurableSet_lt measurable_const
    (measurable_orientedOdometer _ _ measurable_fst measurable_snd _ _))
    (measurable_orientedCumDisc_term n y j) measurable_const

/-- **The first display of the directed `prop:w-moment`, with `kappa` replaced by
one** (`parking.tex:3238-3277`), for the instruction sum with no cutoff. -/
theorem exists_oriented_finite_instr_moment (hBern : External.Bernstein) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 2 ≤ d → ∀ (ν : Measure ℤ), CriticalLaw ν →
      ∀ (N n : ℕ) (r : ℝ), 2 ≤ r →
      (∫ z, |orientedFiniteInstr (boxFinset (0 : Site d) N) n z| ^ r
        ∂((iidLaw d ν).prod (orientedStackLaw d))) ^ (1 / r) ≤
        C * (Real.sqrt r * (∫ ω : Data d, (U ω (n - 1) 0 : ℝ) ^ (r / 2)
          ∂(orientedLaw d ν)) ^ (1 / r) + r) := by
  obtain ⟨C, hC, hb⟩ := exists_oriented_instr_moment hBern
  refine ⟨C, hC, fun d hd2 ν hν N n r hr => ?_⟩
  have hd : 1 ≤ d := by omega
  haveI := hν.prob
  set Q := (iidLaw d ν).prod (orientedStackLaw d) with hQdef
  set S : Finset (Site d) := boxFinset (0 : Site d) N with hSdef
  set B : ℝ := C * (Real.sqrt r * (∫ ω : Data d, (U ω (n - 1) 0 : ℝ) ^ (r / 2)
    ∂(orientedLaw d ν)) ^ (1 / r) + r) with hBdef
  have hr0 : (0 : ℝ) < r := by linarith
  have hB0 : 0 ≤ B := by
    refine mul_nonneg hC.le (add_nonneg (mul_nonneg (Real.sqrt_nonneg r)
      (Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) _))
      hr0.le)
  have hnorm (M : ℕ) : (∫ z, |orientedTruncatedInstr S n M z| ^ r ∂Q) ^ (1 / r) ≤ B :=
    hb d hd2 ν hν N n M r hr
  have hbound (M : ℕ) : (∫ z, |orientedTruncatedInstr S n M z| ^ r ∂Q) ≤ B ^ r := by
    have h := Real.rpow_le_rpow
      (Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) r) _)
      (hnorm M) hr0.le
    rwa [← Real.rpow_mul (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) r),
      one_div, inv_mul_cancel₀ hr0.ne', Real.rpow_one] at h
  have hiF : Integrable (fun z => |orientedFiniteInstr S n z| ^ r) Q :=
    integrable_oriented_route_rpow_of_bound hd ν hν S (fun _ => n - 1) (n - 1)
      (fun _ _ => le_rfl) _ (measurable_orientedFiniteInstr S n)
      (abs_orientedFiniteInstr_le hd S n) (by linarith)
  have hiT (M : ℕ) : Integrable (fun z => |orientedTruncatedInstr S n M z| ^ r) Q :=
    integrable_oriented_route_rpow_of_bound hd ν hν S (fun _ => n - 1) (n - 1)
      (fun _ _ => le_rfl) _ (measurable_orientedTruncatedInstr S n M)
      (abs_orientedTruncatedInstr_le hd S n M) (by linarith)
  have hconv : ∀ᵐ z ∂Q, Filter.Tendsto
      (fun M => |orientedTruncatedInstr S n M z| ^ r) Filter.atTop
      (nhds (|orientedFiniteInstr S n z| ^ r)) := by
    filter_upwards [] with z
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [orientedTruncatedInstr_eventually_eq S n z] with M hM
    rw [hM]
  have hI := integral_le_of_tendsto (fun _ _ => Real.rpow_nonneg (abs_nonneg _) r) hiF
    (fun _ => Real.rpow_nonneg (abs_nonneg _) r) hconv hiT hbound
  have h := Real.rpow_le_rpow (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) r)
    hI (by positivity : 0 ≤ 1 / r)
  rwa [← Real.rpow_mul hB0, mul_one_div, div_self hr0.ne', Real.rpow_one] at h

/-- **The directed error field at the origin has the moments of the directed
`prop:w-moment` with `kappa` replaced by one.** -/
theorem exists_oriented_wErr_moment (hBern : External.Bernstein) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 2 ≤ d → ∀ (ν : Measure ℤ), CriticalLaw ν →
      ∀ (n : ℕ) (r : ℝ), 2 ≤ r →
      (∫ z, |wErrOriented z.1 z.2 n 0| ^ r
        ∂((iidLaw d ν).prod (orientedStackLaw d))) ^ (1 / r) ≤
        C * (Real.sqrt r * (∫ ω : Data d, (U ω (n - 1) 0 : ℝ) ^ (r / 2)
          ∂(orientedLaw d ν)) ^ (1 / r) + r) := by
  obtain ⟨C, hC, hb⟩ := exists_oriented_finite_instr_moment hBern
  refine ⟨C, hC, fun d hd2 ν hν n r hr => ?_⟩
  have hd : 1 ≤ d := by omega
  haveI := hν.prob
  haveI := orientedStackLaw_isProbability hd
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  have hae : ∀ᵐ z ∂((iidLaw d ν).prod (orientedStackLaw d)),
      wErrOriented z.1 z.2 n 0 = orientedFiniteInstr (boxFinset (0 : Site d) (n + 1)) n z := by
    have hz := (Measure.quasiMeasurePreserving_snd (μ := iidLaw d ν)
      (ν := orientedStackLaw d)).ae (orientedStackLaw_ae_forward hd)
    filter_upwards [hz] with z hz'
    exact wErrOriented_eq_instructionSum z.1 z.2 hz' n
  have hint : (∫ z, |wErrOriented z.1 z.2 n 0| ^ r
        ∂((iidLaw d ν).prod (orientedStackLaw d)))
      = ∫ z, |orientedFiniteInstr (boxFinset (0 : Site d) (n + 1)) n z| ^ r
        ∂((iidLaw d ν).prod (orientedStackLaw d)) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with z hz
    rw [hz]
  rw [hint]
  exact hb d hd2 ν hν (n + 1) n r hr

/-- **The directed error at the origin, under the law on the data.**  This is the
first display of `prop:w-moment` for the directed kernel with `kappa_d(n)`
replaced by one, in the vocabulary the rest of the directed chain uses. -/
theorem exists_oriented_wErr_moment_law (hBern : External.Bernstein) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 2 ≤ d → ∀ (ν : Measure ℤ), CriticalLaw ν →
      ∀ (n : ℕ) (r : ℝ), 2 ≤ r →
      (∫ ω : Data d, |wErrOriented ω.1 ω.2.1 n 0| ^ r ∂(orientedLaw d ν)) ^ (1 / r) ≤
        C * (Real.sqrt r * (∫ ω : Data d, (U ω (n - 1) 0 : ℝ) ^ (r / 2)
          ∂(orientedLaw d ν)) ^ (1 / r) + r) := by
  obtain ⟨C, hC, hb⟩ := exists_oriented_finite_instr_moment hBern
  refine ⟨C, hC, fun d hd2 ν hν n r hr => ?_⟩
  have hd : 1 ≤ d := by omega
  haveI := hν.prob
  set F : (Site d → ℤ) × (Site d × ℕ → Site d) → ℝ :=
    fun z => |orientedFiniteInstr (boxFinset (0 : Site d) (n + 1)) n z| ^ r with hFdef
  have hFm : Measurable F :=
    (measurable_rpow_const (by linarith : 0 ≤ r)).comp
      (measurable_orientedFiniteInstr (boxFinset (0 : Site d) (n + 1)) n).abs
  have hstep : (∫ ω : Data d, |wErrOriented ω.1 ω.2.1 n 0| ^ r ∂(orientedLaw d ν))
      = ∫ z, F z ∂((iidLaw d ν).prod (orientedStackLaw d)) := by
    rw [← integral_oriented_confStack hd ν hFm]
    refine integral_congr_ae ?_
    filter_upwards [orientedLaw_ae_forward hd ν] with ω hω
    simp only [hFdef]
    rw [wErrOriented_eq_instructionSum ω.1 ω.2.1 hω n]
    rfl
  rw [hstep]
  exact hb d hd2 ν hν (n + 1) n r hr

end Parking
end
