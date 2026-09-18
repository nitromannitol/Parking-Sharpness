/- The second display of the directed moment estimate.

The `r`-th moment of the maximal directed error at the origin is at most
`(n+1)^{1/r}` times the largest `r`-th moment of the error at the origin over the
rounds up to `n`.  This is the second display of `prop:w-moment` for the directed
kernel, used by Steps 2 to 4 of the proof of `thm:oriented-walk`.
-/
import Parking.Support.OrientedInstructionSum
import Parking.Support.OrientedMaxRpow
import Parking.Support.OrientedMaxMeanRpow
import Parking.Support.OrientedEquivariance
import Parking.Support.OrientedPathBox
import Parking.Support.OrientedFiniteRoute
import Parking.Support.OrientedParticleMoment
import Parking.Support.OrientedMeasurability

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

/-! ### The pathwise bound on the directed error by the odometers it reads -/

/-- Each instruction is read once and its cumulative discrepancy is at most one,
so the directed error at the origin is at most the number of instructions read. -/
theorem abs_wErrOriented_le_countSum (hd : 1 ≤ d) (η : Site d → ℤ) (σ : Site d × ℕ → Site d)
    (hσ : ∀ q : Site d × ℕ, ∃ i : Fin d, σ q = q.1 + unit i) (n : ℕ) :
    |wErrOriented η σ n 0| ≤ ∑ y ∈ boxFinset (0 : Site d) (n + 1),
      (orientedOdometer η σ (n - 1) y : ℝ) := by
  rw [wErrOriented_eq_instructionSum η σ hσ n]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ range (orientedOdometer η σ (n - 1) y),
        |orientedCumDisc (orientedAlive η σ n y j) y (σ (y, j))|
      ≤ ∑ _j ∈ range (orientedOdometer η σ (n - 1) y), (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => abs_orientedCumDisc_le hd _ _ _
    _ = (orientedOdometer η σ (n - 1) y : ℝ) := by simp

/-! ### Integrability of the directed error -/

theorem integrable_oriented_countSum_rpow_law (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (S : Finset (Site d)) (n : ℕ) {r : ℝ} (hr : 1 ≤ r) :
    Integrable (fun ω : Data d => (∑ y ∈ S, (orientedOdometer ω.1 ω.2.1 n y : ℝ)) ^ r)
      (orientedLaw d ν) := by
  haveI := hν.prob
  have hm : Measurable (fun z : (Site d → ℤ) × (Site d × ℕ → Site d) =>
      (∑ y ∈ S, (orientedOdometer z.1 z.2 n y : ℝ)) ^ r) :=
    (measurable_rpow_const (by linarith : (0 : ℝ) ≤ r)).comp
      (Finset.measurable_sum _ fun y _ =>
        (measurable_from_countable' fun m : ℕ => (m : ℝ)).comp
          (measurable_orientedOdometer _ _ measurable_fst measurable_snd n y))
  have hmap : AEMeasurable (fun ω : Data d => (ω.1, ω.2.1)) (orientedLaw d ν) :=
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).aemeasurable
  have h := integrable_oriented_countSum_rpow hd ν hν S n hr
  rw [← orientedLaw_map_confStack hd ν] at h
  exact (integrable_map_measure hm.aestronglyMeasurable hmap).mp h

theorem integrable_abs_wErrOriented_rpow_zero (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    {r : ℝ} (hr : 1 ≤ r) (n : ℕ) :
    Integrable (fun ω : Data d => |wErrOriented ω.1 ω.2.1 n 0| ^ r) (orientedLaw d ν) := by
  haveI := hν.prob
  refine (integrable_oriented_countSum_rpow_law hd ν hν
    (boxFinset (0 : Site d) (n + 1)) (n - 1) hr).mono'
    (((measurable_rpow_const (by linarith : (0 : ℝ) ≤ r)).comp
      (measurable_wErrOriented n (0 : Site d)).abs).aestronglyMeasurable) ?_
  filter_upwards [orientedLaw_ae_forward hd ν] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) r)]
  exact Real.rpow_le_rpow (abs_nonneg _) (abs_wErrOriented_le_countSum hd ω.1 ω.2.1 hω n)
    (by linarith)

theorem integrable_abs_wErrOriented_rpow (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    {r : ℝ} (hr : 1 ≤ r) (n : ℕ) (z : Site d) :
    Integrable (fun ω : Data d => |wErrOriented ω.1 ω.2.1 n z| ^ r) (orientedLaw d ν) := by
  haveI := hν.prob
  have hm : Measurable (fun ω : Data d => |wErrOriented ω.1 ω.2.1 n z| ^ r) :=
    (measurable_rpow_const (by linarith : (0 : ℝ) ≤ r)).comp
      (measurable_wErrOriented n z).abs
  have h := integrable_map_measure (μ := orientedLaw d ν) (f := shiftData (-z))
    (g := fun ω : Data d => |wErrOriented ω.1 ω.2.1 n z| ^ r)
    hm.aestronglyMeasurable (measurable_shiftData _).aemeasurable
  rw [orientedLaw_map_shiftData hd ν (-z)] at h
  refine h.mpr ?_
  have heq : ((fun ω : Data d => |wErrOriented ω.1 ω.2.1 n z| ^ r) ∘ shiftData (-z))
      = fun ω : Data d => |wErrOriented ω.1 ω.2.1 n 0| ^ r := by
    funext ω
    simp only [Function.comp_apply, shiftData]
    rw [wErrOriented_shiftData, add_neg_cancel]
  rw [heq]
  exact integrable_abs_wErrOriented_rpow_zero hd ν hν hr n

/-! ### The average over the directed walk -/

theorem sum_orientedPath_prob (hd : 1 ≤ d) (j : ℕ) :
    ∑ z ∈ boxFinset (0 : Site d) j,
      (walkLaw d).real {p | orientedPath (0 : Site d) p j = z} = 1 := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  have h := integral_orientedPath_decomp hd j (fun _ : Site d => (1 : ℝ))
  simp only [mul_one, integral_const, probReal_univ, smul_eq_mul] at h
  exact h.symm

/-- The average over the directed walk of the `r`-th moment of the error at the
position after `j` steps, written as the finite combination it is. -/
def orientedWalkMoment (r : ℝ) (m j : ℕ) (ω : Data d) : ℝ :=
  ∑ z ∈ boxFinset (0 : Site d) j,
    (walkLaw d).real {p | orientedPath (0 : Site d) p j = z} * |wErrOriented ω.1 ω.2.1 m z| ^ r

theorem orientedWalkMoment_eq (hd : 1 ≤ d) (r : ℝ) (m j : ℕ) (ω : Data d) :
    ∫ p, |wErrOriented ω.1 ω.2.1 m (orientedPath (0 : Site d) p j)| ^ r ∂(walkLaw d)
      = orientedWalkMoment (d := d) r m j ω :=
  integral_orientedPath_decomp hd j (fun z => |wErrOriented ω.1 ω.2.1 m z| ^ r)

theorem integrable_orientedWalkMoment (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    {r : ℝ} (hr : 1 ≤ r) (m j : ℕ) :
    Integrable (orientedWalkMoment (d := d) r m j) (orientedLaw d ν) := by
  haveI := hν.prob
  exact integrable_finsetSum _ fun z _ =>
    (integrable_abs_wErrOriented_rpow hd ν hν hr m z).const_mul _

theorem integral_orientedWalkMoment (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    {r : ℝ} (hr : 1 ≤ r) (m j : ℕ) :
    ∫ ω, orientedWalkMoment (d := d) r m j ω ∂(orientedLaw d ν)
      = ∫ ω : Data d, |wErrOriented ω.1 ω.2.1 m 0| ^ r ∂(orientedLaw d ν) := by
  haveI := hν.prob
  simp only [orientedWalkMoment]
  rw [integral_finsetSum _ fun z _ =>
    (integrable_abs_wErrOriented_rpow hd ν hν hr m z).const_mul _]
  have hterm : ∀ z ∈ boxFinset (0 : Site d) j,
      ∫ ω : Data d, (walkLaw d).real {p | orientedPath (0 : Site d) p j = z} *
          |wErrOriented ω.1 ω.2.1 m z| ^ r ∂(orientedLaw d ν)
        = (walkLaw d).real {p | orientedPath (0 : Site d) p j = z} *
            ∫ ω : Data d, |wErrOriented ω.1 ω.2.1 m 0| ^ r ∂(orientedLaw d ν) := by
    intro z _
    rw [integral_const_mul,
      integral_abs_wErrOriented_rpow_shift hd ν (by linarith : (0 : ℝ) ≤ r) m z]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, sum_orientedPath_prob hd j, one_mul]

/-! ### Measurability of the maximal directed average -/

theorem orientedPath_congr (x : Site d) (j : ℕ) {p q : ℕ → Fin d × Bool}
    (h : ∀ i, i < j → p i = q i) : orientedPath x p j = orientedPath x q j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [orientedPath, orientedPath, ih fun i hi => h i (by omega), h j (by omega)]

theorem wStarOriented_nonneg (η : Site d → ℤ) (σ : Site d × ℕ → Site d) (n : ℕ) (x : Site d) :
    0 ≤ wStarOriented η σ n x :=
  integral_nonneg fun p => orientedMax_nonneg _ n x p

theorem measurable_wStarOriented (hd : 1 ≤ d) (n : ℕ) (x : Site d) :
    Measurable fun ω : Data d => wStarOriented ω.1 ω.2.1 n x := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  have hterm : ∀ j : ℕ, Measurable fun a : Data d × (ℕ → Fin d × Bool) =>
      |wErrOriented a.1.1 a.1.2.1 (n - j) (orientedPath x a.2 j)| := by
    intro j
    refine measurable_eval_var (fun a : Data d × (ℕ → Fin d × Bool) => orientedPath x a.2 j)
      ((measurable_orientedPath x j).comp measurable_snd)
      (fun a z => |wErrOriented a.1.1 a.1.2.1 (n - j) z|) ?_
    intro z
    exact ((measurable_wErrOriented (n - j) z).comp measurable_fst).abs
  have hsup := Finset.measurable_sup' (s := Finset.range (n + 1))
    (f := fun j (a : Data d × (ℕ → Fin d × Bool)) =>
      |wErrOriented a.1.1 a.1.2.1 (n - j) (orientedPath x a.2 j)|)
    Finset.nonempty_range_add_one (fun j _ => hterm j)
  have hfun : (fun a : Data d × (ℕ → Fin d × Bool) =>
      orientedMax (wErrOriented a.1.1 a.1.2.1) n x a.2)
      = (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun j (a : Data d × (ℕ → Fin d × Bool)) =>
          |wErrOriented a.1.1 a.1.2.1 (n - j) (orientedPath x a.2 j)|) := by
    funext a
    rw [Finset.sup'_apply]
    exact orientedMax_eq_sup (wErrOriented a.1.1 a.1.2.1) n x a.2
  have hprod : Measurable fun a : Data d × (ℕ → Fin d × Bool) =>
      orientedMax (wErrOriented a.1.1 a.1.2.1) n x a.2 := by rw [hfun]; exact hsup
  exact (hprod.stronglyMeasurable.integral_prod_right' (ν := walkLaw d)).measurable

/-! ### The second display -/

theorem wStarOriented_rpow_le_sum (hd : 1 ≤ d) {r : ℝ} (hr : 1 ≤ r) (n : ℕ) (ω : Data d) :
    wStarOriented ω.1 ω.2.1 n 0 ^ r
      ≤ ∑ j ∈ Finset.range (n + 1), orientedWalkMoment (d := d) r (n - j) j ω := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  have h1 : wStarOriented ω.1 ω.2.1 n 0 ^ r
      ≤ ∫ p, orientedMax (wErrOriented ω.1 ω.2.1) n 0 p ^ r ∂(walkLaw d) :=
    orientedMaxMean_rpow_le hd (wErrOriented ω.1 ω.2.1) n 0 hr
  have hI1 : Integrable (fun p => orientedMax (wErrOriented ω.1 ω.2.1) n 0 p ^ r)
      (walkLaw d) := by
    refine integrable_of_finite_dependence hd n _ fun p q hpq => ?_
    rw [orientedMax_congr (wErrOriented ω.1 ω.2.1) n 0 hpq]
  have hIterm : ∀ j ∈ Finset.range (n + 1),
      Integrable (fun p => |wErrOriented ω.1 ω.2.1 (n - j) (orientedPath (0 : Site d) p j)| ^ r)
        (walkLaw d) := by
    intro j hj
    have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
    refine integrable_of_finite_dependence hd n _ fun p q hpq => ?_
    rw [orientedPath_congr (0 : Site d) j fun i hi => hpq i (by omega)]
  refine h1.trans ?_
  calc ∫ p, orientedMax (wErrOriented ω.1 ω.2.1) n 0 p ^ r ∂(walkLaw d)
      ≤ ∫ p, ∑ j ∈ Finset.range (n + 1),
          |wErrOriented ω.1 ω.2.1 (n - j) (orientedPath (0 : Site d) p j)| ^ r ∂(walkLaw d) :=
        integral_mono hI1 (integrable_finsetSum _ hIterm) fun p =>
          orientedMax_rpow_le_sum (wErrOriented ω.1 ω.2.1) n 0 hr p
    _ = ∑ j ∈ Finset.range (n + 1),
          ∫ p, |wErrOriented ω.1 ω.2.1 (n - j) (orientedPath (0 : Site d) p j)| ^ r
            ∂(walkLaw d) := integral_finsetSum _ hIterm
    _ = ∑ j ∈ Finset.range (n + 1), orientedWalkMoment (d := d) r (n - j) j ω :=
        Finset.sum_congr rfl fun j _ => orientedWalkMoment_eq hd r (n - j) j ω

theorem integrable_wStarOriented_rpow (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    {r : ℝ} (hr : 1 ≤ r) (n : ℕ) :
    Integrable (fun ω : Data d => wStarOriented ω.1 ω.2.1 n 0 ^ r) (orientedLaw d ν) := by
  haveI := hν.prob
  have hdom : Integrable (fun ω : Data d => ∑ j ∈ Finset.range (n + 1),
      orientedWalkMoment (d := d) r (n - j) j ω) (orientedLaw d ν) :=
    integrable_finsetSum _ fun j _ => integrable_orientedWalkMoment hd ν hν hr (n - j) j
  refine hdom.mono' (((measurable_rpow_const (by linarith : (0 : ℝ) ≤ r)).comp
    (measurable_wStarOriented hd n 0)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (wStarOriented_nonneg ω.1 ω.2.1 n 0) r)]
  exact wStarOriented_rpow_le_sum hd hr n ω

/-- **The second display of the directed moment estimate.** -/
theorem wStarOriented_moment_le (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    {r : ℝ} (hr : 1 ≤ r) (n : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ m ≤ n, (∫ ω : Data d, |wErrOriented ω.1 ω.2.1 m 0| ^ r ∂(orientedLaw d ν)) ^ (1 / r)
      ≤ B) :
    (∫ ω : Data d, wStarOriented ω.1 ω.2.1 n 0 ^ r ∂(orientedLaw d ν)) ^ (1 / r)
      ≤ ((n : ℝ) + 1) ^ (1 / r) * B := by
  haveI := hν.prob
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hMS : ∀ m ≤ n,
      (∫ ω : Data d, |wErrOriented ω.1 ω.2.1 m 0| ^ r ∂(orientedLaw d ν)) ≤ B ^ r := by
    intro m hm
    have hM0 : 0 ≤ ∫ ω : Data d, |wErrOriented ω.1 ω.2.1 m 0| ^ r ∂(orientedLaw d ν) :=
      integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) r
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hM0 _) (hb m hm) hr0.le
    rwa [← Real.rpow_mul hM0, one_div, inv_mul_cancel₀ (ne_of_gt hr0), Real.rpow_one] at h2
  have hle : ∫ ω : Data d, wStarOriented ω.1 ω.2.1 n 0 ^ r ∂(orientedLaw d ν)
      ≤ ((n : ℝ) + 1) * B ^ r := by
    calc ∫ ω : Data d, wStarOriented ω.1 ω.2.1 n 0 ^ r ∂(orientedLaw d ν)
        ≤ ∫ ω : Data d, ∑ j ∈ Finset.range (n + 1),
            orientedWalkMoment (d := d) r (n - j) j ω ∂(orientedLaw d ν) :=
          integral_mono (integrable_wStarOriented_rpow hd ν hν hr n)
            (integrable_finsetSum _ fun j _ => integrable_orientedWalkMoment hd ν hν hr (n - j) j)
            fun ω => wStarOriented_rpow_le_sum hd hr n ω
      _ = ∑ j ∈ Finset.range (n + 1),
            ∫ ω : Data d, orientedWalkMoment (d := d) r (n - j) j ω ∂(orientedLaw d ν) :=
          integral_finsetSum _ fun j _ => integrable_orientedWalkMoment hd ν hν hr (n - j) j
      _ = ∑ j ∈ Finset.range (n + 1),
            ∫ ω : Data d, |wErrOriented ω.1 ω.2.1 (n - j) 0| ^ r ∂(orientedLaw d ν) :=
          Finset.sum_congr rfl fun j _ => integral_orientedWalkMoment hd ν hν hr (n - j) j
      _ ≤ ∑ _j ∈ Finset.range (n + 1), B ^ r :=
          Finset.sum_le_sum fun j _ => hMS (n - j) (Nat.sub_le n j)
      _ = ((n : ℝ) + 1) * B ^ r := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have h2 : (∫ ω : Data d, wStarOriented ω.1 ω.2.1 n 0 ^ r ∂(orientedLaw d ν)) ^ (1 / r)
      ≤ (((n : ℝ) + 1) * B ^ r) ^ (1 / r) :=
    Real.rpow_le_rpow
      (integral_nonneg fun ω => Real.rpow_nonneg (wStarOriented_nonneg ω.1 ω.2.1 n 0) r)
      hle (by positivity)
  rwa [Real.mul_rpow (by positivity) (Real.rpow_nonneg hB r), ← Real.rpow_mul hB,
    mul_one_div, div_self (ne_of_gt hr0), Real.rpow_one] at h2

end Parking
end
