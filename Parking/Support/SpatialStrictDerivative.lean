import Parking.External.HeatStrongMinimum
import Parking.Generic.HeatPositivity
import Parking.Generic.BackwardPositivity
import Parking.Generic.MeasurableTimeDerivative

open MeasureTheory

noncomputable section

namespace Parking

/-- The strong minimum principle makes the time derivative strictly positive wherever
its continuous monotone primitive, initially zero, is positive. -/
theorem spatial_time_derivative_pos
    (hMinimum : External.HeatStrongMinimum) {d : ℕ}
    {u v : ℝ × (Fin d → ℝ) → ℝ}
    (hu : Continuous u) (hu0 : ∀ x, u (0, x) = 0)
    (hmono : ∀ x, Monotone fun s => u (s, x))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v {p | 0 < u p})
    (hderiv : ∀ p, 0 < u p → HasDerivAt (fun s => u (s, p.2)) (v p) p.1)
    (hheat : ∀ p, 0 < u p → HasDerivAt (fun s => v (s, p.2))
      (contOp d (fun x => v (p.1, x)) p.2) p.1) :
    ∀ p, 0 < u p → 0 < v p := by
  have hopen : IsOpen {p | 0 < u p} := isOpen_lt continuous_const hu
  have hnonneg : ∀ p ∈ {p | 0 < u p}, 0 ≤ v p := by
    intro p hp
    exact (hderiv p hp).nonneg_of_monotone (hmono p.2)
  intro p hp
  refine Generic.HeatPositivity.derivative_pos_of_backward_zero
    (hu.comp (continuous_id.prodMk continuous_const)) (hmono p.2) (hu0 p.2)
    (fun t ht => hderiv (t, p.2) ht) ?_ p.1 hp
  intro b hb hzero a hab ha t ht
  exact hMinimum d {q | 0 < u q} hopen v hv hnonneg hheat b p.2 hb hzero a hab
    (by
      rintro ⟨s, x⟩ ⟨hs, hx⟩
      have hx' : x = p.2 := Set.mem_singleton_iff.mp hx
      subst x
      exact ha.trans_le (hmono p.2 hs.1.le)) t ht


/-- A classical caloric time derivative of the continuum value is strictly
positive wherever the value is positive. -/
theorem strict_time_derivative_of_heat_strong_minimum
    (hminimum : External.HeatStrongMinimum) {d : ℕ}
    {u v : ℝ → (Fin d → ℝ) → ℝ}
    (hcont : Continuous fun p : ℝ × (Fin d → ℝ) => u p.1 p.2)
    (hzero : ∀ x, u 0 x = 0) (hmono : ∀ x, Monotone fun s => u s x)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) => v p.1 p.2)
      {p | 0 < u p.1 p.2})
    (hderiv : ∀ s x, 0 < u s x → HasDerivAt (fun t => u t x) (v s x) s)
    (hheat : ∀ s x, 0 < u s x → HasDerivAt (fun t => v t x)
      (contOp d (fun y => v s y) x) s) :
    ∀ s x, 0 < u s x → 0 < v s x := by
  have hopen : IsOpen {p : ℝ × (Fin d → ℝ) | 0 < u p.1 p.2} :=
    isOpen_lt continuous_const hcont
  have hnonneg : ∀ p : ℝ × (Fin d → ℝ), 0 < u p.1 p.2 → 0 ≤ v p.1 p.2 :=
    fun p hp => (hderiv p.1 p.2 hp).nonneg_of_monotone (hmono p.2)
  intro s x hs
  apply Generic.BackwardPositivity.derivative_pos
    (hcont.comp (continuous_id.prodMk continuous_const)) (hmono x) (hzero x)
    (fun t ht => hderiv t x ht) ?_ hs
  intro s₀ hs₀ hvzero τ hτ hsegment t ht
  exact hminimum d {p | 0 < u p.1 p.2} hopen (fun p => v p.1 p.2)
    hsmooth hnonneg (fun p hp => hheat p.1 p.2 hp) s₀ x hs₀ hvzero τ hτ
    (by rintro ⟨r, y⟩ ⟨hr, hy⟩; simp only [Set.mem_singleton_iff] at hy
        subst y; exact hsegment r hr) t ht

/-- Pathwise classical derivatives can be chosen measurably on the original
probability space. Their strict positivity follows from the strong minimum
principle, without making a measurable choice of the pathwise witnesses. -/
theorem exists_measurable_strict_time_derivative
    (hminimum : External.HeatStrongMinimum) {d : ℕ}
    (Ω : Type*) [MeasurableSpace Ω] (Q : Measure Ω)
    (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hmeas : ∀ s x, Measurable fun ω => Uc ω s x)
    (hcont : ∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2)
    (hzero : ∀ ω x, Uc ω 0 x = 0)
    (hmono : ∀ ω x, Monotone fun s => Uc ω s x)
    (hclassical : ∀ᵐ ω ∂Q, ∃ v : ℝ → (Fin d → ℝ) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) => v p.1 p.2)
        {p | 0 < Uc ω p.1 p.2} ∧
      (∀ s x, 0 < Uc ω s x → HasDerivAt (fun t => Uc ω t x) (v s x) s) ∧
      (∀ s x, 0 < Uc ω s x → HasDerivAt (fun t => v t x)
        (contOp d (fun y => v s y) x) s)) :
    ∃ v : Ω → ℝ → (Fin d → ℝ) → ℝ,
      (∀ s x, Measurable fun ω => v ω s x) ∧
      ∀ᵐ ω ∂Q,
        ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) => v ω p.1 p.2)
          {p | 0 < Uc ω p.1 p.2} ∧
        (∀ s x, 0 < Uc ω s x → HasDerivAt (fun t => Uc ω t x) (v ω s x) s) ∧
        (∀ s x, 0 < Uc ω s x → 0 < v ω s x) := by
  let v : Ω → ℝ → (Fin d → ℝ) → ℝ :=
    fun ω s x => Generic.MeasurableTimeDerivative.value (fun t => Uc ω t x) s
  refine ⟨v, fun s x => Generic.MeasurableTimeDerivative.measurable_value
    (fun t => hmeas t x) s, ?_⟩
  filter_upwards [hclassical] with ω hω
  obtain ⟨w, hsmooth, hderiv, hheat⟩ := hω
  have heq : ∀ s x, 0 < Uc ω s x → v ω s x = w s x :=
    fun s x hs => Generic.MeasurableTimeDerivative.value_eq (hderiv s x hs)
  refine ⟨hsmooth.congr (fun p hp => heq p.1 p.2 hp), ?_, ?_⟩
  · intro s x hs
    rw [heq s x hs]
    exact hderiv s x hs
  · intro s x hs
    rw [heq s x hs]
    exact strict_time_derivative_of_heat_strong_minimum hminimum (hcont ω)
      (hzero ω) (hmono ω) hsmooth hderiv hheat s x hs


end Parking
