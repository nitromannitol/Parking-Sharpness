/-
A finite-horizon hitting bound for paths driven by fresh independent layers.
The walk hitting probability is a supermartingale bound when each round's
conditional transition is dominated by two walk steps. Waiting rounds are
allowed, and the proof integrates fresh-layer sections directly.
-/
import Parking.Support.LayerLaw
import LatticeProb.Walk.HitProb

noncomputable section

open MeasureTheory LatticeProb
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {d : ℕ}

/-- Integrating a section after replacing a fresh layer gives an integral bound
for the original product measure. -/
theorem Parking.integral_le_of_layer_sections (μ : Measure α) [IsProbabilityMeasure μ]
    (f g : (ℕ → α) → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf1 : ∀ ω, ‖f ω‖ ≤ 1) (hg1 : ∀ ω, ‖g ω‖ ≤ 1) (n : ℕ)
    (hsec : ∀ ω, ∫ v, f (Function.update ω n v) ∂μ ≤ g ω) :
    ∫ ω, f ω ∂(Measure.infinitePi fun _ : ℕ => μ) ≤
      ∫ ω, g ω ∂(Measure.infinitePi fun _ : ℕ => μ) := by
  let P := Measure.infinitePi fun _ : ℕ => μ
  let T : (ℕ → α) × α → ℕ → α := fun q => Function.update q.1 n q.2
  have hT : MeasurePreserving T (P.prod μ) P :=
    LatticeProb.measurePreserving_update_infinitePi (fun _ : ℕ => μ) n
  have hint : Integrable (fun q => f (T q)) (P.prod μ) :=
    Integrable.of_bound ((hf.comp hT.measurable).aestronglyMeasurable) 1
      (Filter.Eventually.of_forall fun q => hf1 (T q))
  have hgint : Integrable g P := Integrable.of_bound hg.aestronglyMeasurable 1
    (Filter.Eventually.of_forall hg1)
  have heq := integral_map (μ := P.prod μ) (φ := T) (f := f) hT.measurable.aemeasurable
    (by rw [hT.map_eq]; exact hf.aestronglyMeasurable)
  rw [hT.map_eq] at heq
  calc ∫ ω, f ω ∂P = ∫ q, f (T q) ∂(P.prod μ) := heq
    _ = ∫ ω, ∫ v, f (Function.update ω n v) ∂μ ∂P := integral_prod _ hint
    _ ≤ ∫ ω, g ω ∂P := integral_mono hint.integral_prod_left hgint hsec

def Parking.layerHits (X : (ℕ → α) → ℕ → Site d) (t : ℕ) : Set (ℕ → α) :=
  {ω | ∃ s ≤ t, X ω s = 0}

theorem Parking.measurableSet_layerHits (X : (ℕ → α) → ℕ → Site d)
    (hX : Measurable X) (t : ℕ) : MeasurableSet (Parking.layerHits X t) := by
  have heq : Parking.layerHits X t =
      ⋃ s ∈ Set.Iic t, (fun ω => X ω s) ⁻¹' {(0 : Site d)} := by
    ext ω
    simp [Parking.layerHits]
  rw [heq]
  exact MeasurableSet.biUnion (Set.to_countable _) fun s _ =>
    ((measurable_pi_apply s).comp hX) (measurableSet_singleton _)

theorem Parking.srwHitBy_origin (n : ℕ) : LatticeProb.srwHitBy d n 0 = 1 := by
  cases n with
  | zero => simp [LatticeProb.srwHitBy_zero]
  | succ n => exact LatticeProb.srwHitBy_succ_origin n

/-- The probability of a hit already observed, or the remaining walk hitting
probability from the current position. -/
def Parking.layerHitPotential (X : (ℕ → α) → ℕ → Site d) (T s : ℕ) (ω : ℕ → α) : ℝ := by
  classical
  exact if ω ∈ Parking.layerHits X s then 1 else LatticeProb.srwHitBy d (2 * (T - s)) (X ω s)

omit [MeasurableSpace α] in
theorem Parking.layerHitPotential_bounds (hd : 1 ≤ d) (X : (ℕ → α) → ℕ → Site d)
    (T s : ℕ) (ω : ℕ → α) :
    0 ≤ Parking.layerHitPotential X T s ω ∧ Parking.layerHitPotential X T s ω ≤ 1 := by
  unfold Parking.layerHitPotential
  split
  · norm_num
  · exact ⟨LatticeProb.srwHitBy_nonneg _ _, LatticeProb.srwHitBy_le_one hd _ _⟩

omit [MeasurableSpace α] in
theorem Parking.norm_layerHitPotential_le (hd : 1 ≤ d) (X : (ℕ → α) → ℕ → Site d)
    (T s : ℕ) (ω : ℕ → α) : ‖Parking.layerHitPotential X T s ω‖ ≤ 1 := by
  have hb := Parking.layerHitPotential_bounds hd X T s ω
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

theorem Parking.measurable_layerHitPotential (X : (ℕ → α) → ℕ → Site d)
    (hX : Measurable X) (T s : ℕ) : Measurable (Parking.layerHitPotential X T s) := by
  exact Measurable.ite (Parking.measurableSet_layerHits X hX s) measurable_const
    ((measurable_of_countable (LatticeProb.srwHitBy d (2 * (T - s)))).comp
      ((measurable_pi_apply s).comp hX))

/-- An adapted lattice path whose fresh-layer transition is dominated by two
walk steps has no greater finite-horizon hitting probability. -/
theorem Parking.layerPath_hit_le (hd : 1 ≤ d) (μ : Measure α) [IsProbabilityMeasure μ]
    (X : (ℕ → α) → ℕ → Site d) (hX : Measurable X) (x : Site d)
    (hX0 : ∀ ω, X ω 0 = x)
    (hpast : ∀ ω n k v, k ≤ n → X (Function.update ω n v) k = X ω k)
    (hkernel : ∀ ω n m,
      ∫ v, LatticeProb.srwHitBy d m (X (Function.update ω n v) (n + 1)) ∂μ ≤
        LatticeProb.srwHitBy d (m + 2) (X ω n)) (T : ℕ) :
    (Measure.infinitePi fun _ : ℕ => μ) (Parking.layerHits X T) ≤
      ENNReal.ofReal (LatticeProb.srwHitBy d (2 * T) x) := by
  classical
  let P := Measure.infinitePi fun _ : ℕ => μ
  have hpre : ∀ ω s v, Function.update ω s v ∈ Parking.layerHits X (s + 1) ↔
      ω ∈ Parking.layerHits X s ∨ X (Function.update ω s v) (s + 1) = 0 := by
    intro ω s v
    constructor
    · rintro ⟨k, hk, hk0⟩
      by_cases hks : k ≤ s
      · exact Or.inl ⟨k, hks, by rwa [hpast ω s k v hks] at hk0⟩
      · have hk' : k = s + 1 := by omega
        exact Or.inr (hk' ▸ hk0)
    · rintro (⟨k, hk, hk0⟩ | hk0)
      · exact ⟨k, by omega, by rw [hpast ω s k v hk]; exact hk0⟩
      · exact ⟨s + 1, le_rfl, hk0⟩
  have hsec : ∀ s < T, ∀ ω,
      ∫ v, Parking.layerHitPotential X T (s + 1) (Function.update ω s v) ∂μ ≤
        Parking.layerHitPotential X T s ω := by
    intro s hs ω
    by_cases hhit : ω ∈ Parking.layerHits X s
    · have heq : ∀ v, Parking.layerHitPotential X T (s + 1) (Function.update ω s v) = 1 := by
        intro v
        exact if_pos ((hpre ω s v).mpr (Or.inl hhit))
      simp only [heq, integral_const, probReal_univ, smul_eq_mul, one_mul]
      simp [Parking.layerHitPotential, hhit]
    · have heq : ∀ v, Parking.layerHitPotential X T (s + 1) (Function.update ω s v) =
          LatticeProb.srwHitBy d (2 * (T - (s + 1))) (X (Function.update ω s v) (s + 1)) := by
        intro v
        by_cases hzero : X (Function.update ω s v) (s + 1) = 0
        · rw [Parking.layerHitPotential, if_pos ((hpre ω s v).mpr (Or.inr hzero)),
            hzero, Parking.srwHitBy_origin]
        · exact if_neg (fun hh => (hpre ω s v).mp hh |>.elim hhit hzero)
      rw [integral_congr_ae (Filter.Eventually.of_forall heq)]
      have hk := hkernel ω s (2 * (T - (s + 1)))
      have htime : 2 * (T - (s + 1)) + 2 = 2 * (T - s) := by omega
      rw [htime] at hk
      simpa [Parking.layerHitPotential, hhit] using hk
  have hstep : ∀ s < T,
      ∫ ω, Parking.layerHitPotential X T (s + 1) ω ∂P ≤
        ∫ ω, Parking.layerHitPotential X T s ω ∂P := by
    intro s hs
    exact Parking.integral_le_of_layer_sections μ _ _
      (Parking.measurable_layerHitPotential X hX T (s + 1))
      (Parking.measurable_layerHitPotential X hX T s)
      (Parking.norm_layerHitPotential_le hd X T (s + 1))
      (Parking.norm_layerHitPotential_le hd X T s) s (hsec s hs)
  have hmono : ∀ s ≤ T, (∫ ω, Parking.layerHitPotential X T s ω ∂P) ≤
      ∫ ω, Parking.layerHitPotential X T 0 ω ∂P := by
    intro s
    induction s with
    | zero => exact fun _ => le_rfl
    | succ s ih => intro hs; exact le_trans (hstep s (by omega)) (ih (by omega))
  have hlast : Parking.layerHitPotential X T T = (Parking.layerHits X T).indicator 1 := by
    funext ω
    by_cases hh : ω ∈ Parking.layerHits X T
    · simp [Parking.layerHitPotential, hh]
    · have hx : X ω T ≠ 0 := fun h => hh ⟨T, le_rfl, h⟩
      simp [Parking.layerHitPotential, hh, LatticeProb.srwHitBy_zero, hx]
  have hfirst : Parking.layerHitPotential X T 0 = fun _ => LatticeProb.srwHitBy d (2 * T) x := by
    funext ω
    by_cases hx : x = 0
    · have hh : ω ∈ Parking.layerHits X 0 := ⟨0, le_rfl, (hX0 ω).trans hx⟩
      simp [Parking.layerHitPotential, hh, hx, Parking.srwHitBy_origin]
    · have hh : ω ∉ Parking.layerHits X 0 := by
        rintro ⟨k, hk, hk0⟩
        have hk' : k = 0 := by omega
        subst k
        exact hx ((hX0 ω).symm.trans hk0)
      simp [Parking.layerHitPotential, hh, hX0]
  have hb := hmono T le_rfl
  rw [hlast, integral_indicator_one (Parking.measurableSet_layerHits X hX T), hfirst,
    integral_const, probReal_univ, smul_eq_mul, one_mul] at hb
  have he := ENNReal.ofReal_le_ofReal hb
  rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top P _)] at he
  exact he

end
