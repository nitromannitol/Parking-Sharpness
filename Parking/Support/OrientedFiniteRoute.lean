import Parking.Support.OrientedTruncatedRouting
import Parking.Support.OrientedParticleMoment
import Parking.Support.WeightedMoment

/-!
# Full finite-site routing sum

The full finite-site routing sum and its deterministic truncation limit.
-/

open LatticeProb (measurable_from_countable' measurable_of_countable_partition)

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
open scoped Classical
variable {d : ℕ}

/-- The routing discrepancy summed over every instruction actually used by the sites in
`S`, each read up to its own (data-dependent) odometer count `orientedOdometer z.1 z.2
(m y) y`, at truncation level `l y`. -/
def orientedFiniteRoute (S : Finset (Site d)) (m l : Site d → ℕ)
    (z : (Site d → ℤ) × (Site d × ℕ → Site d)) : ℝ :=
  ∑ y ∈ S, ∑ j ∈ range (orientedOdometer z.1 z.2 (m y) y), orientedRouteDisc (l y) y (z.2 (y, j))

/-- `orientedFiniteRoute S m l` is measurable, since the inner range depends measurably
on the data through `orientedOdometer` and `measurable_of_countable_partition` lets each
countable value of that odometer be handled by a measurable partial sum. -/
theorem measurable_orientedFiniteRoute (S : Finset (Site d)) (m l : Site d → ℕ) :
    Measurable (orientedFiniteRoute S m l) := by
  apply Finset.measurable_sum
  intro y _
  refine measurable_of_countable_partition (fun z => orientedOdometer z.1 z.2 (m y) y)
    (measurable_orientedOdometer _ _ measurable_fst measurable_snd _ _) _
    (fun N z => ∑ j ∈ range N, orientedRouteDisc (l y) y (z.2 (y, j))) ?_ (fun _ => rfl)
  intro N
  exact Finset.measurable_sum _ fun j _ =>
    (Measurable.of_discrete : Measurable (orientedRouteDisc (l y) y)).comp
      ((measurable_pi_apply (y, j)).comp measurable_snd)

/-- `orientedTruncatedRoute S m l M` is measurable, since at each truncation level `M` it
is a finite sum of `if`-then-else terms built from the measurable odometer and the
(discrete-domain) routing discrepancy. -/
theorem measurable_orientedTruncatedRoute (S : Finset (Site d)) (m l : Site d → ℕ) (M : ℕ) :
    Measurable (orientedTruncatedRoute S m l M) := by
  apply Finset.measurable_sum
  intro y _
  apply Finset.measurable_sum
  intro j _
  exact Measurable.ite (measurableSet_lt measurable_const
    (measurable_orientedOdometer _ _ measurable_fst measurable_snd _ _))
    ((Measurable.of_discrete : Measurable (orientedRouteDisc (l y) y)).comp
      ((measurable_pi_apply (y, j)).comp measurable_snd)) measurable_const

/-- Summing `f j` over `j < M` only where `j < N` equals summing `f` over
`range (min M N)`, by rewriting the `if`-guarded sum as a `Finset.filter`. -/
theorem sum_range_ite_lt {α : Type*} [AddCommMonoid α] (M N : ℕ) (f : ℕ → α) :
    (∑ j ∈ range M, if j < N then f j else 0) = ∑ j ∈ range (min M N), f j := by
  rw [← sum_filter]
  congr 1
  ext j
  simp only [mem_filter, mem_range, lt_min_iff]

/-- Once the truncation level `M` dominates every relevant odometer count on `S`, the
truncated route sum `orientedTruncatedRoute S m l M` agrees with the full finite route
sum `orientedFiniteRoute S m l`, via `sum_range_ite_lt`. -/
theorem orientedTruncatedRoute_eq_of_le (S : Finset (Site d)) (m l : Site d → ℕ) (M : ℕ)
    (z : (Site d → ℤ) × (Site d × ℕ → Site d))
    (hM : ∀ y ∈ S, orientedOdometer z.1 z.2 (m y) y ≤ M) :
    orientedTruncatedRoute S m l M z = orientedFiniteRoute S m l z := by
  apply sum_congr rfl
  intro y hy
  rw [sum_range_ite_lt, min_eq_right (hM y hy)]

/-- The truncated route sum eventually equals the full finite route sum as the truncation
level `M → ∞`, taking `M` past the finite supremum of the relevant odometer counts on
`S` and applying `orientedTruncatedRoute_eq_of_le`. -/
theorem orientedTruncatedRoute_eventually_eq (S : Finset (Site d)) (m l : Site d → ℕ)
    (z : (Site d → ℤ) × (Site d × ℕ → Site d)) :
    ∀ᶠ M in Filter.atTop, orientedTruncatedRoute S m l M z = orientedFiniteRoute S m l z := by
  filter_upwards [Filter.eventually_ge_atTop
    (S.sup (fun y => orientedOdometer z.1 z.2 (m y) y))] with M hM
  exact orientedTruncatedRoute_eq_of_le S m l M z (fun y hy =>
    (le_sup (f := fun y => orientedOdometer z.1 z.2 (m y) y) hy).trans hM)

/-- The finite route sum is bounded in absolute value by the sum, over `S`, of the
relevant odometer counts, using the triangle inequality and the single-instruction
bound `abs_orientedRouteDisc_le`. -/
theorem abs_orientedFiniteRoute_le (hd : 1 ≤ d) (S : Finset (Site d)) (m l : Site d → ℕ)
    (z : (Site d → ℤ) × (Site d × ℕ → Site d)) :
    |orientedFiniteRoute S m l z| ≤ ∑ y ∈ S, (orientedOdometer z.1 z.2 (m y) y : ℝ) := by
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro y _
  apply (abs_sum_le_sum_abs _ _).trans
  have h := sum_le_sum (s := range (orientedOdometer z.1 z.2 (m y) y))
    (fun j _ => abs_orientedRouteDisc_le hd (l y) y (z.2 (y, j)))
  simpa only [sum_const, card_range, nsmul_eq_mul, mul_one] using h

/-- The truncated route sum satisfies the same bound as the untruncated one, since
truncating to level `M` only shrinks the range of each inner sum
(`min M (orientedOdometer ...) ≤ orientedOdometer ...`). -/
theorem abs_orientedTruncatedRoute_le (hd : 1 ≤ d) (S : Finset (Site d)) (m l : Site d → ℕ) (M : ℕ)
    (z : (Site d → ℤ) × (Site d × ℕ → Site d)) :
    |orientedTruncatedRoute S m l M z| ≤ ∑ y ∈ S, (orientedOdometer z.1 z.2 (m y) y : ℝ) := by
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro y _
  rw [sum_range_ite_lt]
  apply (abs_sum_le_sum_abs _ _).trans
  have h := sum_le_sum (s := range (min M (orientedOdometer z.1 z.2 (m y) y)))
    (fun j _ => abs_orientedRouteDisc_le hd (l y) y (z.2 (y, j)))
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one] at h
  exact h.trans (by exact_mod_cast min_le_right M (orientedOdometer z.1 z.2 (m y) y))

/-- The `r`-th power (`r ≥ 1`) of the sum, over a finite `S`, of odometer counts at a
common horizon `n` is integrable against the product law, obtained from the general
weighted-power bound `integral_weighted_rpow_le` with unit weights and the per-site
integrability `integrable_orientedOdometer_joint_rpow`. -/
theorem integrable_oriented_countSum_rpow (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (S : Finset (Site d)) (n : ℕ) {r : ℝ} (hr : 1 ≤ r) :
    Integrable (fun z : (Site d → ℤ) × (Site d × ℕ → Site d) =>
      (∑ y ∈ S, (orientedOdometer z.1 z.2 n y : ℝ)) ^ r)
        ((iidLaw d ν).prod (orientedStackLaw d)) := by
  haveI := hν.prob
  have h := integral_weighted_rpow_le ((iidLaw d ν).prod (orientedStackLaw d)) S (fun _ => 1)
    (fun y z => (orientedOdometer z.1 z.2 n y : ℝ)) (fun _ _ => zero_le_one)
    (fun _ _ _ => Nat.cast_nonneg _)
    (fun y _ => (measurable_from_countable' fun k : ℕ => (k : ℝ)).comp
      (measurable_orientedOdometer _ _ measurable_fst measurable_snd n y)) hr
    (fun y _ => integrable_orientedOdometer_joint_rpow hd ν hν hr n y)
    (∫ ω : Data d, (U ω n 0 : ℝ) ^ r ∂(orientedLaw d ν))
    (integral_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) r)
    (fun y _ => (integral_orientedOdometer_joint_rpow hd ν r n y).le)
  simpa only [one_mul] using h.1

/-- Any measurable `F` bounded in absolute value, uniformly over the data, by the
odometer-count sum `∑ y ∈ S, orientedOdometer z.1 z.2 (m y) y` (with each `m y ≤ n`) has
an integrable `r`-th power, `r ≥ 1`, by domination against
`integrable_oriented_countSum_rpow` at the common horizon `n`. -/
theorem integrable_oriented_route_rpow_of_bound (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (S : Finset (Site d)) (m : Site d → ℕ) (n : ℕ) (hm : ∀ y ∈ S, m y ≤ n)
    (F : (Site d → ℤ) × (Site d × ℕ → Site d) → ℝ) (hF : Measurable F)
    (hbd : ∀ z, |F z| ≤ ∑ y ∈ S, (orientedOdometer z.1 z.2 (m y) y : ℝ))
    {r : ℝ} (hr : 1 ≤ r) :
    Integrable (fun z => |F z| ^ r) ((iidLaw d ν).prod (orientedStackLaw d)) := by
  apply (integrable_oriented_countSum_rpow hd ν hν S n hr).mono'
    (((measurable_rpow_const (by linarith : 0 ≤ r)).comp hF.abs).aestronglyMeasurable)
  filter_upwards [] with z
  change ‖|F z| ^ r‖ ≤ (∑ y ∈ S, (orientedOdometer z.1 z.2 n y : ℝ)) ^ r
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) r)]
  apply Real.rpow_le_rpow (abs_nonneg _) _ (by linarith)
  exact (hbd z).trans (sum_le_sum fun y hy => by
    exact_mod_cast orientedOdometer_mono_time z.1 z.2 y (hm y hy))

end Parking
