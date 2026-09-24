/- Measurable walk maxima and the upper comparison for the directed divisible process. -/
import Parking.Support.OrientedPotential

noncomputable section
namespace Parking
open LatticeProb Finset MeasureTheory
variable {d : ℕ}

/-- A walk in the negative coordinate directions, using the coordinate of
each uniform signed direction. -/
def orientedPath (x : Site d) (p : ℕ → Fin d × Bool) : ℕ → Site d
  | 0 => x
  | j + 1 => orientedPath x p j - unit (p j).1

/-- The largest absolute reward along the directed path, with decreasing horizon. -/
def orientedMax (F : ℕ → Site d → ℝ) : ℕ → Site d → (ℕ → Fin d × Bool) → ℝ
  | 0, x, _ => |F 0 x|
  | n + 1, x, p => max |F (n + 1) x| (orientedMax F n (x - unit (p 0).1) (tailNat p))

/-- The expected maximum along the auxiliary directed walk. -/
def orientedMaxMean (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d) : ℝ :=
  ∫ p, orientedMax F n x p ∂(walkLaw d)

theorem exists_bound_of_finite_dependence (hd : 1 ≤ d) (n : ℕ)
    (f : (ℕ → Fin d × Bool) → ℝ)
    (hf : ∀ p q, (∀ i, i < n → p i = q i) → f p = f q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p, |f p| ≤ C := by
  classical
  let a : Fin d × Bool := (⟨0, hd⟩, true)
  let e : (Fin n → Fin d × Bool) → (ℕ → Fin d × Bool) :=
    fun c k => if hk : k < n then c ⟨k, hk⟩ else a
  refine ⟨∑ c : Fin n → Fin d × Bool, |f (e c)|,
    sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro p
  have he : f (e (fun k : Fin n => p k)) = f p := by
    apply hf
    intro k hk
    simp only [e, dif_pos hk]
  rw [← he]
  exact single_le_sum (f := fun c : Fin n → Fin d × Bool => |f (e c)|)
    (fun _ _ => abs_nonneg _) (mem_univ (fun k : Fin n => p (k : ℕ)))

theorem integrable_of_finite_dependence (hd : 1 ≤ d) (n : ℕ)
    (f : (ℕ → Fin d × Bool) → ℝ)
    (hf : ∀ p q, (∀ i, i < n → p i = q i) → f p = f q) :
    Integrable f (walkLaw d) := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  obtain ⟨C, _, hC⟩ := exists_bound_of_finite_dependence hd n f hf
  exact (integrable_const C).mono' (measurable_of_finite_dependence hd n f hf).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hC p)

theorem orientedMax_congr (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d)
    {p q : ℕ → Fin d × Bool} (h : ∀ i, i < n → p i = q i) :
    orientedMax F n x p = orientedMax F n x q := by
  induction n generalizing x p q with
  | zero => rfl
  | succ n ih =>
    simp only [orientedMax]
    rw [h 0 (by omega)]
    congr 1
    exact ih _ (fun i hi => h (i + 1) (by omega))

theorem measurable_orientedMax (hd : 1 ≤ d) (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d) :
    Measurable (orientedMax F n x) :=
  measurable_of_finite_dependence hd n _ (fun _ _ h => orientedMax_congr F n x h)

theorem integrable_orientedMax (hd : 1 ≤ d) (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d) :
    Integrable (orientedMax F n x) (walkLaw d) :=
  integrable_of_finite_dependence hd n _ (fun _ _ h => orientedMax_congr F n x h)

theorem abs_le_orientedMax (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d) (p : ℕ → Fin d × Bool) :
    |F n x| ≤ orientedMax F n x p := by
  cases n with
  | zero => rfl
  | succ n => exact le_max_left _ _

theorem orientedMax_nonneg (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d) (p : ℕ → Fin d × Bool) :
    0 ≤ orientedMax F n x p := (abs_nonneg _).trans (abs_le_orientedMax F n x p)

theorem abs_le_orientedMaxMean (hd : 1 ≤ d) (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d) :
    |F n x| ≤ orientedMaxMean F n x := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  have h := integral_mono (integrable_const |F n x|) (integrable_orientedMax hd F n x)
    (abs_le_orientedMax F n x)
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, orientedMaxMean] using h

theorem integral_stepLaw_oriented (hd : 1 ≤ d) (f : Site d → ℝ) (x : Site d) :
    (∫ b : Fin d × Bool, f (x - unit b.1) ∂(stepLaw d)) = orientedOp f x := by
  rw [integral_stepLaw hd, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, ← two_mul, ← mul_sum, orientedOp]
  ring

theorem orientedOp_orientedMaxMean_le (hd : 1 ≤ d) (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d) :
    orientedOp (orientedMaxMean F n) x ≤ orientedMaxMean F (n + 1) x := by
  haveI := stepLaw_isProbability hd
  let f : (ℕ → Fin d × Bool) → ℝ :=
    fun p => orientedMax F n (x - unit (p 0).1) (tailNat p)
  have hi : Integrable f (walkLaw d) := by
    apply integrable_of_finite_dependence hd (n + 1)
    intro p q hpq
    dsimp only [f]
    rw [hpq 0 (by omega)]
    exact orientedMax_congr F n _ (fun i hi => hpq (i + 1) (by omega))
  have he : (∫ p, f p ∂(walkLaw d)) = orientedOp (orientedMaxMean F n) x := by
    rw [show walkLaw d = Measure.infinitePi (fun _ : ℕ => stepLaw d) from rfl,
      integral_infinitePi_nat_head_tail (stepLaw d) f hi]
    have ht : ∀ (b : Fin d × Bool) (p : ℕ → Fin d × Bool), tailNat (consNat b p) = p := fun b p => rfl
    simp only [f, consNat_zero, ht]
    exact integral_stepLaw_oriented hd (orientedMaxMean F n) x
  rw [← he]
  exact integral_mono hi (integrable_orientedMax hd F (n + 1) x) (fun p => le_max_right _ _)

theorem uOriented_le_potential_add_max (hd : 1 ≤ d) (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    uOriented η n x ≤ orientedPotential η n x + orientedMaxMean (orientedPotential η) n x := by
  have hmain : ∀ n x, uOriented η n x - orientedPotential η n x ≤
      orientedMaxMean (orientedPotential η) n x := by
    intro n
    induction n with
    | zero =>
      intro x
      have h := abs_le_orientedMaxMean hd (orientedPotential η) 0 x
      simpa [orientedPotential_zero, uOriented] using h
    | succ n ih =>
      intro x
      rw [uOriented_sub_potential_succ]
      apply max_le
      · exact (neg_le_abs _).trans (abs_le_orientedMaxMean hd (orientedPotential η) (n + 1) x)
      · exact (orientedOp_mono ih x).trans (orientedOp_orientedMaxMean_le hd (orientedPotential η) n x)
  linarith [hmain n x]

end Parking
