/- The ball event of `parking.tex:1818-1820`: with limiting probability at least
`1-ε` the parking odometer is positive on the lattice ball of radius `rR`.

The three convergence clauses of `prop:spatial-scaling` give it through a finite
net.  The equicontinuity clause fixes a mesh on which the rescaled divisible
odometer varies by less than the tolerance; on a net of that mesh the
finite-dimensional clause and one bounded continuous test function bound the
probability that the field is large at every net point; the local-uniform
closeness clause transfers the bound to the parking odometer.  Every supremum
in those clauses is a genuine supremum because the rescaled fields read finitely
many lattice sites on a compact set.
-/
import Parking.Support.SpatialTightnessBridge
import Parking.Support.NearestContinuumPositivity

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset Filter Topology

variable {d : ℕ}

/-- A bounded family has a genuine supremum, so each member is below it. -/
theorem le_biSup_of_bound {α : Type*} (K : Set α) (F : α → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hFB : ∀ p ∈ K, F p ≤ B) {z : α} (hz : z ∈ K) : F z ≤ ⨆ p ∈ K, F p := by
  have hbdd : BddAbove (Set.range fun p : α => ⨆ _ : p ∈ K, F p) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact Real.iSup_le (fun hp => hFB p hp) hB
  calc F z = ⨆ _ : z ∈ K, F z := (ciSup_pos (f := fun _ : z ∈ K => F z) hz).symm
    _ ≤ _ := le_ciSup hbdd z

/-- A bounded family of pairs has a genuine supremum, so each pair is below it. -/
theorem le_biSup_pair_of_bound {α : Type*} [PseudoMetricSpace α] (K : Set α) (δ : ℝ)
    (F : α → α → ℝ) {B : ℝ} (hB : 0 ≤ B) (hFB : ∀ p ∈ K, ∀ q ∈ K, F p q ≤ B)
    {z y : α} (hz : z ∈ K) (hy : y ∈ K) (hzy : dist z y ≤ δ) :
    F z y ≤ ⨆ p ∈ K, ⨆ q ∈ K, ⨆ _ : dist p q ≤ δ, F p q := by
  have hMid : ∀ p ∈ K, (⨆ q ∈ K, ⨆ _ : dist p q ≤ δ, F p q) ≤ B := by
    intro p hp
    exact Real.iSup_le (fun q => Real.iSup_le (fun hq =>
      Real.iSup_le (fun _ => hFB p hp q hq) hB) hB) hB
  have hOutBdd : BddAbove (Set.range fun p : α => ⨆ _ : p ∈ K,
      ⨆ q ∈ K, ⨆ _ : dist p q ≤ δ, F p q) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact Real.iSup_le (fun hp => hMid p hp) hB
  have hMidBdd : BddAbove (Set.range fun q : α => ⨆ _ : q ∈ K,
      ⨆ _ : dist z q ≤ δ, F z q) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact Real.iSup_le (fun hq => Real.iSup_le (fun _ => hFB z hz q hq) hB) hB
  calc F z y
      = ⨆ _ : dist z y ≤ δ, F z y :=
        (ciSup_pos (f := fun _ : dist z y ≤ δ => F z y) hzy).symm
    _ = ⨆ _ : y ∈ K, ⨆ _ : dist z y ≤ δ, F z y :=
        (ciSup_pos (f := fun _ : y ∈ K => ⨆ _ : dist z y ≤ δ, F z y) hy).symm
    _ ≤ ⨆ q ∈ K, ⨆ _ : dist z q ≤ δ, F z q := le_ciSup hMidBdd y
    _ = ⨆ _ : z ∈ K, ⨆ q ∈ K, ⨆ _ : dist z q ≤ δ, F z q :=
        (ciSup_pos (f := fun _ : z ∈ K => ⨆ q ∈ K, ⨆ _ : dist z q ≤ δ, F z q) hz).symm
    _ ≤ _ := le_ciSup hOutBdd z

/-- The rescaled parking odometer is bounded on a box, as the divisible one is. -/
theorem abs_barOdometer_le (w : Data d) {R : ℝ} (hR : 0 ≤ R)
    {C : ℝ} (_hC : 0 ≤ C) {p : ℝ × (Fin d → ℝ)} (hp1 : |p.1| ≤ C) (hp2 : ∀ i, |p.2 i| ≤ C) :
    |barOdometer w R p.1 p.2|
      ≤ R ^ ((d : ℝ) / 2 - 2) * ((⌊C * R ^ 2⌋₊ : ℝ) *
          confBox w 0 ((⌈C * R⌉₊ + 1) + ⌊C * R ^ 2⌋₊)) := by
  set N : ℕ := ⌊C * R ^ 2⌋₊ with hN
  set m : ℕ := ⌈C * R⌉₊ + 1 with hm
  have hpow : (0 : ℝ) ≤ R ^ ((d : ℝ) / 2 - 2) := Real.rpow_nonneg hR _
  have hkN : ⌊p.1 * R ^ 2⌋₊ ≤ N := by
    refine Nat.floor_le_floor ?_
    have : p.1 ≤ C := le_trans (le_abs_self _) hp1
    nlinarith [sq_nonneg R]
  have hmem : latticePoint R p.2 ∈ boxFinset (0 : Site d) m := by
    rw [mem_boxFinset_iff]
    intro i
    have hx : |R * p.2 i| ≤ C * R := by
      rw [abs_mul, abs_of_nonneg hR, mul_comm]
      exact mul_le_mul_of_nonneg_right (hp2 i) hR
    have h1 : (⌊R * p.2 i⌋ : ℝ) ≤ C * R := le_trans (Int.floor_le _) (le_trans (le_abs_self _) hx)
    have h2 : -(C * R) - 1 ≤ (⌊R * p.2 i⌋ : ℝ) := by
      have := Int.sub_one_lt_floor (R * p.2 i)
      have h3 : -(C * R) ≤ R * p.2 i := neg_le_of_abs_le hx
      linarith
    have hcr : (C * R : ℝ) ≤ (⌈C * R⌉₊ : ℝ) := Nat.le_ceil _
    simp only [latticePoint, Pi.zero_apply, sub_zero]
    rw [abs_le]
    constructor
    · have : -((m : ℝ)) ≤ (⌊R * p.2 i⌋ : ℝ) := by push_cast [hm]; linarith
      exact_mod_cast this
    · have : (⌊R * p.2 i⌋ : ℝ) ≤ (m : ℝ) := by push_cast [hm]; linarith
      exact_mod_cast this
  have hu : ((U w ⌊p.1 * R ^ 2⌋₊ (latticePoint R p.2) : ℕ) : ℝ)
      ≤ (N : ℝ) * confBox w 0 (m + N) := by
    refine (U_le_confBox w _ _).trans ?_
    have h1 : confBox w (latticePoint R p.2) ⌊p.1 * R ^ 2⌋₊
        ≤ confBox w (0 : Site d) (m + N) :=
      (confBox_mono w _ hkN).trans (confBox_le_of_mem w hmem N)
    have h2 : ((⌊p.1 * R ^ 2⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkN
    exact mul_le_mul h2 h1 (confBox_nonneg _ _ _) (Nat.cast_nonneg _)
  rw [barOdometer, abs_of_nonneg (mul_nonneg hpow (Nat.cast_nonneg _))]
  exact mul_le_mul_of_nonneg_left hu hpow

/-- On a compact set both rescaled fields are bounded, for each fixed scale. -/
theorem exists_bound_on_compact (hd : 1 ≤ d) (w : Data d) {R : ℝ} (hR : 0 ≤ R)
    (K : Set (ℝ × (Fin d → ℝ))) (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ p ∈ K, |barDivisible w R p.1 p.2| ≤ B) ∧
      (∀ p ∈ K, |barOdometer w R p.1 p.2| ≤ B) := by
  obtain ⟨C, hC, hKC⟩ := exists_radius_of_isCompact K hK
  refine ⟨R ^ ((d : ℝ) / 2 - 2) * ((⌊C * R ^ 2⌋₊ : ℝ) *
      confBox w 0 ((⌈C * R⌉₊ + 1) + ⌊C * R ^ 2⌋₊)), ?_, ?_, ?_⟩
  · exact mul_nonneg (Real.rpow_nonneg hR _)
      (mul_nonneg (Nat.cast_nonneg _) (confBox_nonneg _ _ _))
  · exact fun p hp => abs_barDivisible_le hd w hR hC (hKC p hp).1 (hKC p hp).2
  · exact fun p hp => abs_barOdometer_le w hR hC (hKC p hp).1 (hKC p hp).2

/-- The local-uniform closeness clause of `prop:spatial-scaling`, read at a point. -/
theorem abs_barOdometer_sub_barDivisible_le (hd : 1 ≤ d) (w : Data d) {R : ℝ} (hR : 0 ≤ R)
    (K : Set (ℝ × (Fin d → ℝ))) (hK : IsCompact K) {ε : ℝ}
    (hw : ¬ ε < ⨆ p ∈ K, |barOdometer w R p.1 p.2 - barDivisible w R p.1 p.2|)
    {p : ℝ × (Fin d → ℝ)} (hp : p ∈ K) :
    |barOdometer w R p.1 p.2 - barDivisible w R p.1 p.2| ≤ ε := by
  obtain ⟨B, hB, hbd, hbo⟩ := exists_bound_on_compact hd w hR K hK
  refine le_trans (le_biSup_of_bound K
    (fun p => |barOdometer w R p.1 p.2 - barDivisible w R p.1 p.2|) (by linarith : (0:ℝ) ≤ 2 * B)
    (fun q hq => ?_) hp) (not_lt.mp hw)
  calc |barOdometer w R q.1 q.2 - barDivisible w R q.1 q.2|
      ≤ |barOdometer w R q.1 q.2| + |barDivisible w R q.1 q.2| := abs_sub _ _
    _ ≤ 2 * B := by linarith [hbd q hq, hbo q hq]

/-- The equicontinuity clause of `prop:spatial-scaling`, read at a pair of points. -/
theorem abs_barDivisible_sub_le (hd : 1 ≤ d) (w : Data d) {R : ℝ} (hR : 0 ≤ R)
    (K : Set (ℝ × (Fin d → ℝ))) (hK : IsCompact K) {ε δ : ℝ}
    (hw : ¬ ε < ⨆ p ∈ K, ⨆ q ∈ K, ⨆ _ : dist p q ≤ δ,
      |barDivisible w R p.1 p.2 - barDivisible w R q.1 q.2|)
    {p q : ℝ × (Fin d → ℝ)} (hp : p ∈ K) (hq : q ∈ K) (hpq : dist p q ≤ δ) :
    |barDivisible w R p.1 p.2 - barDivisible w R q.1 q.2| ≤ ε := by
  obtain ⟨B, hB, hbd, _⟩ := exists_bound_on_compact hd w hR K hK
  refine le_trans (le_biSup_pair_of_bound K δ
    (fun p q => |barDivisible w R p.1 p.2 - barDivisible w R q.1 q.2|)
    (by linarith : (0:ℝ) ≤ 2 * B) (fun z hz y hy => ?_) hp hq hpq) (not_lt.mp hw)
  calc |barDivisible w R z.1 z.2 - barDivisible w R y.1 y.2|
      ≤ |barDivisible w R z.1 z.2| + |barDivisible w R y.1 y.2| := abs_sub _ _
    _ ≤ 2 * B := by linarith [hbd z hz, hbd y hy]

theorem measurable_barDivisible (R s : ℝ) (x : Fin d → ℝ) :
    Measurable fun w : Data d => barDivisible w R s x :=
  (measurable_uOf _ _).const_mul _

theorem measurable_barOdometer (R s : ℝ) (x : Fin d → ℝ) :
    Measurable fun w : Data d => barOdometer w R s x :=
  ((measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp (measurable_U _ _)).const_mul _

/-- The closed `ℓ¹` ball of the continuum picture. -/
def ellOneBall (d : ℕ) (r : ℝ) : Set (Fin d → ℝ) := {x | (∑ i, |x i|) ≤ r}

theorem isCompact_ellOneBall (d : ℕ) (r : ℝ) : IsCompact (ellOneBall d r) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le (by fun_prop) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Fin d → ℝ)) (r := r)).subset ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg ?_).mpr fun i => ?_
    · exact le_trans (Finset.sum_nonneg fun i _ => abs_nonneg (x i)) hx
    · rw [Real.norm_eq_abs]
      exact (Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)).trans hx

theorem zero_mem_ellOneBall {d : ℕ} {r : ℝ} (hr : 0 ≤ r) : (0 : Fin d → ℝ) ∈ ellOneBall d r := by
  simp [ellOneBall, hr]

/-- The space-time slice at time one over the `ℓ¹` ball. -/
def timeOneSlice (d : ℕ) (r : ℝ) : Set (ℝ × (Fin d → ℝ)) := {(1 : ℝ)} ×ˢ ellOneBall d r

theorem isCompact_timeOneSlice (d : ℕ) (r : ℝ) : IsCompact (timeOneSlice d r) :=
  isCompact_singleton.prod (isCompact_ellOneBall d r)

theorem timeOneSlice_pos {d : ℕ} {r : ℝ} : ∀ p ∈ timeOneSlice d r, 0 < p.1 := by
  rintro ⟨s, x⟩ ⟨hs, -⟩
  simp only [Set.mem_singleton_iff] at hs
  simp [hs]

/-- The clamp that rises from `0` at level `a-η` to `1` at level `a`. -/
def clampAt (a η t : ℝ) : ℝ := min 1 (max 0 ((t - (a - η)) / η))

theorem clampAt_nonneg (a η t : ℝ) (_hη : 0 < η) : 0 ≤ clampAt a η t := by
  unfold clampAt
  exact le_min zero_le_one (le_max_left _ _)

theorem clampAt_le_one (a η t : ℝ) : clampAt a η t ≤ 1 := min_le_left _ _

theorem clampAt_eq_one {a η t : ℝ} (hη : 0 < η) (h : a ≤ t) : clampAt a η t = 1 := by
  unfold clampAt
  have h1 : (1 : ℝ) ≤ (t - (a - η)) / η := by
    rw [le_div_iff₀ hη]; linarith
  exact min_eq_left (le_max_of_le_right h1)

theorem clampAt_eq_zero {a η t : ℝ} (hη : 0 < η) (h : t ≤ a - η) : clampAt a η t = 0 := by
  unfold clampAt
  have h1 : (t - (a - η)) / η ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hη.le
  rw [max_eq_left h1, min_eq_right zero_le_one]

theorem continuous_clampAt (a η : ℝ) : Continuous (clampAt a η) := by
  unfold clampAt; fun_prop

/-- The product of the clamps at the net points, a bounded continuous test function. -/
def netTest (k : ℕ) (a η : ℝ) (hη : 0 < η) : BoundedContinuousFunction (Fin k → ℝ) ℝ :=
  ⟨⟨fun y => ∏ j, clampAt a η (y j), by
      exact continuous_finsetProd _ fun j _ => (continuous_clampAt a η).comp (continuous_apply j)⟩,
    ⟨1, by
      intro x y
      have hx : ∀ z : Fin k → ℝ, 0 ≤ ∏ j, clampAt a η (z j) ∧ (∏ j, clampAt a η (z j)) ≤ 1 := by
        intro z
        refine ⟨Finset.prod_nonneg fun j _ => clampAt_nonneg a η _ hη, ?_⟩
        exact Finset.prod_le_one (fun j _ => clampAt_nonneg a η _ hη)
          (fun j _ => clampAt_le_one a η _)
      have h1 := hx x
      have h2 := hx y
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith⟩⟩

theorem netTest_apply (k : ℕ) (a η : ℝ) (hη : 0 < η) (y : Fin k → ℝ) :
    netTest k a η hη y = ∏ j, clampAt a η (y j) := rfl

theorem netTest_nonneg (k : ℕ) (a η : ℝ) (hη : 0 < η) (y : Fin k → ℝ) :
    0 ≤ netTest k a η hη y := by
  rw [netTest_apply]
  exact Finset.prod_nonneg fun j _ => clampAt_nonneg a η _ hη

theorem netTest_le_one (k : ℕ) (a η : ℝ) (hη : 0 < η) (y : Fin k → ℝ) :
    netTest k a η hη y ≤ 1 := by
  rw [netTest_apply]
  exact Finset.prod_le_one (fun j _ => clampAt_nonneg a η _ hη) (fun j _ => clampAt_le_one a η _)

theorem netTest_eq_one {k : ℕ} {a η : ℝ} (hη : 0 < η) {y : Fin k → ℝ} (h : ∀ j, a ≤ y j) :
    netTest k a η hη y = 1 := by
  rw [netTest_apply]
  exact Finset.prod_eq_one fun j _ => clampAt_eq_one hη (h j)

theorem netTest_eq_zero {k : ℕ} {a η : ℝ} (hη : 0 < η) {y : Fin k → ℝ} {j : Fin k}
    (h : y j ≤ a - η) : netTest k a η hη y = 0 := by
  rw [netTest_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (clampAt_eq_zero hη h)

theorem measurable_netTest {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {a η : ℝ} (hη : 0 < η)
    (X : Fin k → Ω → ℝ) (hX : ∀ j, Measurable (X j)) :
    Measurable fun w => netTest k a η hη (fun j => X j w) :=
  (netTest k a η hη).continuous.measurable.comp (measurable_pi_lambda _ hX)

theorem integrable_netTest {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {k : ℕ} {a η : ℝ} (hη : 0 < η)
    (X : Fin k → Ω → ℝ) (hX : ∀ j, Measurable (X j)) :
    Integrable (fun w => netTest k a η hη (fun j => X j w)) P := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_netTest hη X hX).aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (netTest_nonneg k a η hη _)]
  exact netTest_le_one k a η hη _

theorem measureReal_le_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ) (hfi : Integrable f P)
    (h0 : ∀ w, 0 ≤ f w) (E : Set Ω) (hE : MeasurableSet E)
    (hon : ∀ w ∈ E, 1 ≤ f w) : (P E).toReal ≤ ∫ w, f w ∂P := by
  have hind : Integrable (E.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hE
  have hle : ∀ w, E.indicator (fun _ => (1 : ℝ)) w ≤ f w := by
    intro w
    by_cases hw : w ∈ E
    · simpa [Set.indicator_apply, hw] using hon w hw
    · simpa [Set.indicator_apply, hw] using h0 w
  calc (P E).toReal = ∫ w, E.indicator (fun _ => (1 : ℝ)) w ∂P := by
        rw [integral_indicator_const (1 : ℝ) hE]; simp [measureReal_def]
    _ ≤ ∫ w, f w ∂P := integral_mono hind hfi hle

theorem integral_le_measureReal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ) (hfi : Integrable f P)
    (h1 : ∀ w, f w ≤ 1) (E : Set Ω) (hE : MeasurableSet E)
    (hoff : ∀ w, w ∉ E → f w = 0) : ∫ w, f w ∂P ≤ (P E).toReal := by
  have hind : Integrable (E.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hE
  have hle : ∀ w, f w ≤ E.indicator (fun _ => (1 : ℝ)) w := by
    intro w
    by_cases hw : w ∈ E
    · simpa [Set.indicator_apply, hw] using h1 w
    · simp [hw, hoff w hw]
  calc ∫ w, f w ∂P ≤ ∫ w, E.indicator (fun _ => (1 : ℝ)) w ∂P := integral_mono hfi hind hle
    _ = (P E).toReal := by rw [integral_indicator_const (1 : ℝ) hE]; simp [measureReal_def]

/-- A compact set has a finite net of its own points at every mesh. -/
theorem exists_finite_net {α : Type*} [PseudoMetricSpace α] {K : Set α} (hK : IsCompact K)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (k : ℕ) (pts : Fin k → α), (∀ j, pts j ∈ K) ∧ ∀ x ∈ K, ∃ j, dist x (pts j) ≤ δ := by
  obtain ⟨t, htK, htfin, htcov⟩ :=
    hK.totallyBounded.exists_subset (Metric.dist_mem_uniformity hδ)
  classical
  set s : Finset α := htfin.toFinset with hs
  refine ⟨s.card, fun j => ((s.equivFin.symm j : α)), fun j => ?_, fun x hx => ?_⟩
  · have hmem : ((s.equivFin.symm j : α)) ∈ s := (s.equivFin.symm j).2
    exact htK (htfin.mem_toFinset.mp hmem)
  · have hx' := htcov hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hx'
    obtain ⟨y, hy, hxy⟩ := hx'
    have hys : y ∈ s := htfin.mem_toFinset.mpr hy
    refine ⟨s.equivFin ⟨y, hys⟩, ?_⟩
    simpa using le_of_lt hxy

/-- On the good event of the two local-uniform clauses, a lower bound at the net points is a
lower bound on the whole ball. -/
theorem ball_barOdometer_pos_of_good (hd : 1 ≤ d) (w : Data d) {R : ℝ} (hR0 : 0 ≤ R)
    {r a η δ : ℝ} (_hη : 0 < η) (ha3 : 3 * η < a)
    {k : ℕ} {pts : Fin k → (Fin d → ℝ)} (hptsB : ∀ j, pts j ∈ ellOneBall d r)
    (hnet : ∀ x ∈ ellOneBall d r, ∃ j, dist x (pts j) ≤ δ)
    (hwE : ∀ j, a - η < barDivisible w R 1 (pts j))
    (hb1 : ¬ η < ⨆ p ∈ timeOneSlice d r, ⨆ q ∈ timeOneSlice d r, ⨆ _ : dist p q ≤ δ,
      |barDivisible w R p.1 p.2 - barDivisible w R q.1 q.2|)
    (hb2 : ¬ η < ⨆ p ∈ timeOneSlice d r,
      |barOdometer w R p.1 p.2 - barDivisible w R p.1 p.2|) :
    ∀ x ∈ ellOneBall d r, 0 < barOdometer w R 1 x := by
  intro x hx
  obtain ⟨j, hj⟩ := hnet x hx
  have hxK : ((1 : ℝ), x) ∈ timeOneSlice d r := Set.mem_prod.mpr ⟨Set.mem_singleton _, hx⟩
  have hpK : ((1 : ℝ), pts j) ∈ timeOneSlice d r :=
    Set.mem_prod.mpr ⟨Set.mem_singleton _, hptsB j⟩
  have hdistK : dist (((1 : ℝ), x)) (((1 : ℝ), pts j)) ≤ δ := by
    rw [Prod.dist_eq]
    simp only [dist_self]
    exact max_le (dist_nonneg.trans hj) hj
  have hstep1 : |barDivisible w R 1 x - barDivisible w R 1 (pts j)| ≤ η :=
    abs_barDivisible_sub_le hd w hR0 (timeOneSlice d r) (isCompact_timeOneSlice d r)
      (p := ((1 : ℝ), x)) (q := ((1 : ℝ), pts j)) hb1 hxK hpK hdistK
  have hstep2 : |barOdometer w R 1 x - barDivisible w R 1 x| ≤ η :=
    abs_barOdometer_sub_barDivisible_le hd w hR0 (timeOneSlice d r)
      (isCompact_timeOneSlice d r) (p := ((1 : ℝ), x)) hb2 hxK
  have h4 := (abs_le.mp hstep1).1
  have h5 := (abs_le.mp hstep2).1
  have h3 : a - η < barDivisible w R 1 (pts j) := hwE j
  linarith

/-- **The ball event of `parking.tex:1818-1820`.**  From the finite-dimensional clause, the
local-uniform closeness clause and the equicontinuity clause of `prop:spatial-scaling`, together
with a level `a` below which the continuum field does not fall on the `ℓ¹` ball of radius `r`
except with probability `ε`, the rescaled parking odometer is positive on the whole ball at
every large scale, outside probability `4ε`. -/
theorem eventually_ball_barOdometer_pos (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure (law d ν)]
    {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ) (hUm : ∀ s x, Measurable fun ω => Uc ω s x)
    {r a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hfdd : ∀ (k : ℕ) (pts : Fin k → (Fin d → ℝ)),
      ∀ F : BoundedContinuousFunction (Fin k → ℝ) ℝ,
        Tendsto (fun R : ℝ => ∫ w, F (fun j => barDivisible w R 1 (pts j)) ∂(law d ν))
          atTop (𝓝 (∫ ω, F (fun j => Uc ω 1 (pts j)) ∂Q)))
    (hclose : ∀ η : ℝ, 0 < η →
      Tendsto (fun R : ℝ => ((law d ν) {w | η < ⨆ p ∈ timeOneSlice d r,
          |barOdometer w R p.1 p.2 - barDivisible w R p.1 p.2|}).toReal) atTop (𝓝 0))
    (htight : ∀ η : ℝ, 0 < η → ∀ ε' : ℝ, 0 < ε' → ∃ δ : ℝ, 0 < δ ∧ ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      ((law d ν) {w | η < ⨆ p ∈ timeOneSlice d r, ⨆ q ∈ timeOneSlice d r, ⨆ _ : dist p q ≤ δ,
          |barDivisible w R p.1 p.2 - barDivisible w R q.1 q.2|}).toReal ≤ ε')
    (hcont : ∀ (k : ℕ) (pts : Fin k → (Fin d → ℝ)), (∀ j, pts j ∈ ellOneBall d r) →
      1 - ε ≤ (Q {ω | ∀ j, a ≤ Uc ω 1 (pts j)}).toReal) :
    ∀ᶠ R : ℝ in atTop, 1 - 4 * ε ≤
      ((law d ν) {w | ∀ x ∈ ellOneBall d r, 0 < barOdometer w R 1 x}).toReal := by
  classical
  have hη : (0 : ℝ) < a / 4 := by positivity
  obtain ⟨δ, hδ, R₀, hR₀⟩ := htight (a / 4) hη ε hε
  obtain ⟨k, pts, hptsB, hnet⟩ := exists_finite_net (isCompact_ellOneBall d r) hδ
  have hQint : 1 - ε ≤ ∫ ω, netTest k a (a / 4) hη (fun j => Uc ω 1 (pts j)) ∂Q := by
    refine le_trans (hcont k pts hptsB) ?_
    refine measureReal_le_integral Q _
      (integrable_netTest Q hη (fun j ω => Uc ω 1 (pts j)) (fun j => hUm 1 (pts j)))
      (fun ω => netTest_nonneg k a (a / 4) hη _) _ ?_ (fun ω hω => ?_)
    · simp only [Set.setOf_forall]
      exact MeasurableSet.iInter fun j => measurableSet_le measurable_const (hUm 1 (pts j))
    · exact le_of_eq (netTest_eq_one hη hω).symm
  have hdisc : ∀ᶠ R : ℝ in atTop, 1 - 2 * ε ≤
      ∫ w, netTest k a (a / 4) hη (fun j => barDivisible w R 1 (pts j)) ∂(law d ν) := by
    have hlt : 1 - 2 * ε < ∫ ω, netTest k a (a / 4) hη (fun j => Uc ω 1 (pts j)) ∂Q := by
      linarith
    exact ((hfdd k pts (netTest k a (a / 4) hη)).eventually
      (eventually_gt_nhds hlt)).mono fun R hR => hR.le
  have hbad2 : ∀ᶠ R : ℝ in atTop, ((law d ν) {w | a / 4 < ⨆ p ∈ timeOneSlice d r,
      |barOdometer w R p.1 p.2 - barDivisible w R p.1 p.2|}).toReal ≤ ε :=
    ((hclose (a / 4) hη).eventually (eventually_lt_nhds hε)).mono fun R hR => hR.le
  filter_upwards [hdisc, hbad2, eventually_ge_atTop R₀, eventually_ge_atTop (0 : ℝ)] with
    R hRint hRc hRR₀ hR0
  have hEmeas : MeasurableSet {w : Data d | ∀ j, a - a / 4 < barDivisible w R 1 (pts j)} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun j => measurableSet_lt measurable_const
      (measurable_barDivisible R 1 (pts j))
  have hEbound : 1 - 2 * ε ≤
      ((law d ν) {w : Data d | ∀ j, a - a / 4 < barDivisible w R 1 (pts j)}).toReal := by
    refine le_trans hRint ?_
    refine integral_le_measureReal (law d ν) _
      (integrable_netTest (law d ν) hη (fun j w => barDivisible w R 1 (pts j))
        (fun j => measurable_barDivisible R 1 (pts j)))
      (fun w => netTest_le_one k a (a / 4) hη _) _ hEmeas (fun w hw => ?_)
    obtain ⟨j, hj⟩ := not_forall.mp hw
    exact netTest_eq_zero hη (not_lt.mp hj)
  have hgood : {w : Data d | ∀ j, a - a / 4 < barDivisible w R 1 (pts j)} \
      ({w : Data d | a / 4 < ⨆ p ∈ timeOneSlice d r, ⨆ q ∈ timeOneSlice d r, ⨆ _ : dist p q ≤ δ,
          |barDivisible w R p.1 p.2 - barDivisible w R q.1 q.2|} ∪
        {w : Data d | a / 4 < ⨆ p ∈ timeOneSlice d r,
          |barOdometer w R p.1 p.2 - barDivisible w R p.1 p.2|})
      ⊆ {w : Data d | ∀ x ∈ ellOneBall d r, 0 < barOdometer w R 1 x} := by
    rintro w ⟨hwE, hwb⟩
    exact ball_barOdometer_pos_of_good hd w hR0 hη (by linarith) hptsB hnet hwE
      (fun h => hwb (Or.inl h)) (fun h => hwb (Or.inr h))
  have hchain : ∀ (E b1 b2 : Set (Data d)),
      ((law d ν) E).toReal ≤ ((law d ν) (E \ (b1 ∪ b2))).toReal +
        (((law d ν) b1).toReal + ((law d ν) b2).toReal) := by
    intro E b1 b2
    calc ((law d ν) E).toReal
        ≤ ((law d ν) ((E \ (b1 ∪ b2)) ∪ (b1 ∪ b2))).toReal := by
          refine measureReal_mono (μ := law d ν) ?_ (measure_ne_top _ _)
          intro w hw
          by_cases h : w ∈ b1 ∪ b2
          · exact Or.inr h
          · exact Or.inl ⟨hw, h⟩
      _ ≤ ((law d ν) (E \ (b1 ∪ b2))).toReal + ((law d ν) (b1 ∪ b2)).toReal :=
          measureReal_union_le _ _
      _ ≤ _ := by gcongr; exact measureReal_union_le _ _
  have hch := hchain {w : Data d | ∀ j, a - a / 4 < barDivisible w R 1 (pts j)}
      {w : Data d | a / 4 < ⨆ p ∈ timeOneSlice d r, ⨆ q ∈ timeOneSlice d r, ⨆ _ : dist p q ≤ δ,
        |barDivisible w R p.1 p.2 - barDivisible w R q.1 q.2|}
      {w : Data d | a / 4 < ⨆ p ∈ timeOneSlice d r,
        |barOdometer w R p.1 p.2 - barDivisible w R p.1 p.2|}
  have hfinal := measureReal_mono (μ := law d ν) hgood (measure_ne_top _ _)
  have hb1R := hR₀ R hRR₀
  simp only [measureReal_def] at hch hfinal
  linarith

/-- Smaller `ℓ¹` balls sit inside larger ones. -/
theorem ellOneBall_mono {d : ℕ} {r s : ℝ} (h : r ≤ s) : ellOneBall d r ⊆ ellOneBall d s :=
  fun _ hx => le_trans hx h

theorem exists_radius_level {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hct : ∀ ω, Continuous fun x : Fin d → ℝ => Uc ω 1 x)
    (hpos : ∀ᵐ ω ∂Q, ∃ r : ℝ, 0 < r ∧ ∀ x : Fin d → ℝ, (∑ i, |x i|) ≤ r → 0 < Uc ω 1 x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r a : ℝ, 0 < r ∧ 0 < a ∧ ∀ (k : ℕ) (pts : Fin k → (Fin d → ℝ)),
      (∀ j, pts j ∈ ellOneBall d r) → 1 - ε ≤ (Q {ω | ∀ j, a ≤ Uc ω 1 (pts j)}).toReal := by
  classical
  rcases le_or_gt 1 ε with hge | hlt
  · exact ⟨1, 1, one_pos, one_pos, fun k pts _ => by
      have h0 : (0 : ℝ) ≤ (Q {ω | ∀ j, (1 : ℝ) ≤ Uc ω 1 (pts j)}).toReal := ENNReal.toReal_nonneg
      linarith⟩
  set A : ℕ → Set Ω := fun n =>
    {ω | ∀ x ∈ ellOneBall d (1 / (n + 1) : ℝ), (1 / (n + 1) : ℝ) ≤ Uc ω 1 x} with hA
  have hinv : ∀ n m : ℕ, n ≤ m → (1 / (m + 1) : ℝ) ≤ 1 / (n + 1) := by
    intro n m h
    have : ((n : ℝ) + 1) ≤ ((m : ℝ) + 1) := by exact_mod_cast Nat.succ_le_succ h
    exact one_div_le_one_div_of_le (by positivity) this
  have hmono : Monotone A := by
    intro n m hnm ω hω x hx
    exact le_trans (hinv n m hnm) (hω x (ellOneBall_mono (hinv n m hnm) hx))
  have hcover : {ω | ∃ r : ℝ, 0 < r ∧ ∀ x : Fin d → ℝ, (∑ i, |x i|) ≤ r → 0 < Uc ω 1 x}
      ⊆ ⋃ n, A n := by
    rintro ω ⟨r, hr, hball⟩
    obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt hr
    have hn₀' : (1 / (n₀ + 1) : ℝ) ≤ r := le_of_lt hn₀
    obtain ⟨x₀, hx₀mem, hx₀min⟩ :=
      (isCompact_ellOneBall d (1 / (n₀ + 1) : ℝ)).exists_isMinOn
        ⟨0, zero_mem_ellOneBall (by positivity)⟩ (hct ω).continuousOn
    have hm₀ : 0 < Uc ω 1 x₀ := hball x₀ (le_trans hx₀mem hn₀')
    obtain ⟨n₂, hn₂⟩ := exists_nat_one_div_lt hm₀
    refine Set.mem_iUnion.mpr ⟨max n₀ n₂, fun x hx => ?_⟩
    have h1 : (1 / ((max n₀ n₂ : ℕ) + 1) : ℝ) ≤ 1 / (n₂ + 1) := hinv n₂ _ (le_max_right _ _)
    have h2 : (1 / ((max n₀ n₂ : ℕ) + 1) : ℝ) ≤ 1 / (n₀ + 1) := hinv n₀ _ (le_max_left _ _)
    have h3 : x ∈ ellOneBall d (1 / (n₀ + 1) : ℝ) := ellOneBall_mono h2 hx
    have h4 : Uc ω 1 x₀ ≤ Uc ω 1 x := hx₀min h3
    calc (1 / ((max n₀ n₂ : ℕ) + 1) : ℝ) ≤ 1 / (n₂ + 1) := h1
      _ ≤ Uc ω 1 x₀ := le_of_lt hn₂
      _ ≤ Uc ω 1 x := h4
  have hnull : Q (⋃ n, A n)ᶜ = 0 := by
    have hp := MeasureTheory.ae_iff.mp hpos
    have hsubset : (⋃ n, A n)ᶜ ⊆
        {ω | ¬ ∃ r : ℝ, 0 < r ∧ ∀ x : Fin d → ℝ, (∑ i, |x i|) ≤ r → 0 < Uc ω 1 x} :=
      fun ω hω hc => hω (hcover hc)
    exact measure_mono_null hsubset hp
  have hfull : Q (⋃ n, A n) = 1 := by
    refine le_antisymm prob_le_one ?_
    have h := measure_union_le (μ := Q) (⋃ n, A n) (⋃ n, A n)ᶜ
    rw [Set.union_compl_self, measure_univ, hnull, add_zero] at h
    exact h
  have hsup : ⨆ n, Q (A n) = 1 := by rw [← hmono.measure_iUnion, hfull]
  have hlt1 : ENNReal.ofReal (1 - ε) < ⨆ n, Q (A n) := by
    rw [hsup]
    exact ENNReal.ofReal_lt_one.mpr (by linarith)
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp hlt1
  refine ⟨1 / (n + 1), 1 / (n + 1), by positivity, by positivity, fun k pts hpts => ?_⟩
  have hsub : A n ⊆ {ω | ∀ j, (1 / (n + 1) : ℝ) ≤ Uc ω 1 (pts j)} :=
    fun ω hω j => hω (pts j) (hpts j)
  have h1 : ENNReal.ofReal (1 - ε) ≤ Q {ω | ∀ j, (1 / (n + 1) : ℝ) ≤ Uc ω 1 (pts j)} :=
    le_trans hn.le (measure_mono hsub)
  have h2 := ENNReal.toReal_mono (measure_ne_top Q _) h1
  rwa [ENNReal.toReal_ofReal (by linarith)] at h2

/-- Positivity of the rescaled parking odometer on the `ℓ¹` ball is positivity of the
parking odometer on the lattice ball of radius `rR`, the ball event of
`parking.tex:1818-1820`. -/
theorem U_pos_of_ball_barOdometer_pos {d : ℕ} (w : Data d) {R r : ℝ} (hR : 0 < R)
    (h : ∀ x ∈ ellOneBall d r, 0 < barOdometer w R 1 x) :
    ∀ y : Site d, (Parking.graphNorm y : ℝ) ≤ r * R → 0 < U w ⌊R ^ 2⌋₊ y := by
  intro y hy
  have hgn : ((Parking.graphNorm y : ℕ) : ℝ) = ∑ i, |(y i : ℝ)| := by
    unfold Parking.graphNorm
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have hx : (fun i => (y i : ℝ) / R) ∈ ellOneBall d r := by
    show (∑ i, |(y i : ℝ) / R|) ≤ r
    have hsum : (∑ i, |(y i : ℝ) / R|) = (∑ i, |(y i : ℝ)|) / R := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [abs_div, abs_of_pos hR]
    rw [hsum, div_le_iff₀ hR, ← hgn]
    exact hy
  have hpos := h _ hx
  have hlat : latticePoint R (fun i => (y i : ℝ) / R) = y := by
    funext i
    show ⌊R * ((y i : ℝ) / R)⌋ = y i
    rw [mul_div_cancel₀ _ (ne_of_gt hR), Int.floor_intCast]
  have hfloor : ⌊(1 : ℝ) * R ^ 2⌋₊ = ⌊R ^ 2⌋₊ := by rw [one_mul]
  rw [barOdometer, hlat, hfloor] at hpos
  have hp : (0 : ℝ) < R ^ ((d : ℝ) / 2 - 2) := Real.rpow_pos_of_pos hR _
  have hU : (0 : ℝ) < ((U w ⌊R ^ 2⌋₊ y : ℕ) : ℝ) := by
    by_contra hc
    have hc' : ((U w ⌊R ^ 2⌋₊ y : ℕ) : ℝ) ≤ 0 := not_lt.mp hc
    nlinarith
  exact_mod_cast hU

end Parking
end
