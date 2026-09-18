/-
The hitting comparison for two particles whose motion in each round may be
switched on or off using the past. Distinct fresh table entries give independent
increments, and reversing one direction records the difference of positions.
-/
import Parking.Support.RoundFresh
import Parking.Support.LayerHitting
import Parking.Support.UBound
import Parking.Support.RangeHitting
import LatticeProb.Prob.MapPi

noncomputable section

open MeasureTheory LatticeProb
open scoped ENNReal

variable {d : ℕ}

theorem Parking.srwHitBy_mono (x : Site d) : Monotone fun m => LatticeProb.srwHitBy d m x := by
  intro m n hmn
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right hmn 1)) (fun i _ _ => LatticeProb.srwFirstHit_nonneg i x)

theorem Parking.walkOp_srwHitBy_le (hd : 1 ≤ d) (m : ℕ) (x : Site d) :
    walkOp (LatticeProb.srwHitBy d m) x ≤ LatticeProb.srwHitBy d (m + 1) x := by
  by_cases hx : x = 0
  · rw [hx, Parking.srwHitBy_origin]
    exact Parking.walkOp_le_of_nbr hd fun y _ => LatticeProb.srwHitBy_le_one hd m y
  · rw [LatticeProb.srwHitBy_succ_of_ne hx]

theorem Parking.integral_stepLaw_add (hd : 1 ≤ d) (f : Site d → ℝ) (x : Site d) :
    ∫ b, f (x + Parking.stepVec b) ∂(Parking.stepLaw d) = walkOp f x := by
  rw [Parking.integral_stepLaw hd, Parking.sum_stepVec, walkOp]

/-- A difference takes either, both, or neither of its two available increments. -/
def Parking.roundDifference (x : Site d) (u v : Bool) (b₁ b₂ : Fin d × Bool) : Site d :=
  x + (if u then Parking.stepVec b₁ else 0) + (if v then Parking.stepVec b₂ else 0)

theorem Parking.integral_roundDifference_hitBy_le (hd : 1 ≤ d) (m : ℕ) (x : Site d)
    (u v : Bool) :
    ∫ q, LatticeProb.srwHitBy d m (Parking.roundDifference x u v q.1 q.2)
        ∂((Parking.stepLaw d).prod (Parking.stepLaw d)) ≤
      LatticeProb.srwHitBy d (m + 2) x := by
  haveI := Parking.stepLaw_isProbability hd
  have hint : Integrable (fun q : (Fin d × Bool) × (Fin d × Bool) =>
      LatticeProb.srwHitBy d m (Parking.roundDifference x u v q.1 q.2))
      ((Parking.stepLaw d).prod (Parking.stepLaw d)) :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs, abs_of_nonneg (LatticeProb.srwHitBy_nonneg _ _)]
        exact LatticeProb.srwHitBy_le_one hd _ _)
  rw [integral_prod _ hint]
  cases u <;> cases v
  · simpa [Parking.roundDifference] using Parking.srwHitBy_mono (d := d) x (show m ≤ m + 2 by omega)
  · simp only [Parking.roundDifference, Bool.false_eq_true, if_false, if_true, add_zero]
    rw [Parking.integral_stepLaw_add hd, integral_const, probReal_univ, smul_eq_mul, one_mul]
    exact le_trans (Parking.walkOp_srwHitBy_le hd m x)
      (Parking.srwHitBy_mono x (show m + 1 ≤ m + 2 by omega))
  · simp only [Parking.roundDifference, Bool.false_eq_true, if_false, if_true, add_zero]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [Parking.integral_stepLaw_add hd]
    exact le_trans (Parking.walkOp_srwHitBy_le hd m x)
      (Parking.srwHitBy_mono x (show m + 1 ≤ m + 2 by omega))
  · simp only [Parking.roundDifference, if_true]
    simp_rw [Parking.integral_stepLaw_add hd]
    exact le_trans (Parking.walkOp_mono hd (Parking.walkOp_srwHitBy_le hd m) x)
      (Parking.walkOp_srwHitBy_le hd (m + 1) x)

theorem Parking.walkPath_eq_sitePath (x : Site d) (p : ℕ → Fin d × Bool) (t : ℕ) :
    Parking.walkPath x p t = LatticeProb.sitePath x (fun n => Parking.stepVec (p n)) t := by
  induction t with
  | zero => simp [Parking.walkPath, LatticeProb.sitePath]
  | succ t ih =>
      rw [Parking.walkPath, ih, LatticeProb.sitePath, LatticeProb.sitePath, Finset.sum_range_succ]
      abel

/-- The truncated hitting kernel is the probability in the signed-direction
walk model used by the parking process. -/
theorem Parking.walkLaw_hitZero_eq (hd : 1 ≤ d) (x : Site d) (t : ℕ) :
    (Parking.walkLaw d) {p | ∃ s ≤ t, Parking.walkPath x p s = 0} =
      ENNReal.ofReal (LatticeProb.srwHitBy d t x) := by
  haveI : NeZero d := ⟨by omega⟩
  haveI := Parking.stepLaw_isProbability hd
  let M : (ℕ → Fin d × Bool) → ℕ → Site d := fun p n => Parking.stepVec (p n)
  have hM : Measurable M := measurable_pi_lambda _ fun n =>
    (measurable_of_countable Parking.stepVec).comp (measurable_pi_apply n)
  have hMLaw : (Parking.walkLaw d).map M = Measure.infinitePi fun _ : ℕ => LatticeProb.incLaw d := by
    rw [Parking.walkLaw]
    rw [LatticeProb.infinitePi_map_pi (Parking.stepLaw d) (measurable_of_countable Parking.stepVec),
      Parking.map_stepLaw_stepVec]
    rfl
  have hpath : (Parking.walkLaw d).map (Parking.walkPath x) = LatticeProb.siteWalkLaw d x := by
    have heq : Parking.walkPath x = LatticeProb.sitePath x ∘ M :=
      funext fun p => funext fun t => Parking.walkPath_eq_sitePath x p t
    rw [heq, ← Measure.map_map (LatticeProb.measurable_sitePath x) hM, hMLaw]
    rfl
  have hm : Measurable (Parking.walkPath x) := measurable_pi_lambda _ fun t =>
    Parking.measurable_walkPath x t
  rw [← LatticeProb.siteWalkLaw_hitOriginBy hd t x, ← hpath,
    Measure.map_apply hm (LatticeProb.measurableSet_hitOriginBy t)]
  rfl

/-- The hitting comparison for two predictable, possibly waiting particles.
Both selected entries are fresh and distinct; the second direction is reversed
to record the difference of the positions. -/
theorem Parking.roundPath_hit_le (hd : 1 ≤ d)
    (X : Parking.RoundNoise d → ℕ → Site d) (hX : Measurable X) (x : Site d)
    (i j : Parking.RoundNoise d → ℕ → Parking.RoundSlot d)
    (u v : Parking.RoundNoise d → ℕ → Bool)
    (hX0 : ∀ σ, X σ 0 = x)
    (hpast : ∀ σ n k τ, k ≤ n → X (Function.update σ n τ) k = X σ k)
    (hip : ∀ σ n τ, i (Function.update σ n τ) n = i σ n)
    (hjp : ∀ σ n τ, j (Function.update σ n τ) n = j σ n)
    (hup : ∀ σ n τ, u (Function.update σ n τ) n = u σ n)
    (hvp : ∀ σ n τ, v (Function.update σ n τ) n = v σ n)
    (hij : ∀ σ n, i σ n ≠ j σ n)
    (hnext : ∀ σ n, X σ (n + 1) = Parking.roundDifference (X σ n) (u σ n) (v σ n)
      (σ n (i σ n)) (Parking.reverseDirection (σ n (j σ n)))) (T : ℕ) :
    (Parking.roundNoiseLaw d) {σ | ∃ s ≤ T, X σ s = 0} ≤
      (Parking.walkLaw d) {p | ∃ s ≤ 2 * T, Parking.walkPath x p s = 0} := by
  classical
  haveI := Parking.stepLaw_isProbability hd
  rw [Parking.walkLaw_hitZero_eq hd x (2 * T)]
  apply Parking.layerPath_hit_le hd
    (Measure.infinitePi fun _ : Parking.RoundSlot d => Parking.stepLaw d) X hX x hX0 hpast
  intro σ n m
  let f : (Fin d × Bool) × (Fin d × Bool) → ℝ :=
    fun q => LatticeProb.srwHitBy d m
      (Parking.roundDifference (X σ n) (u σ n) (v σ n) q.1 q.2)
  let F : (Parking.RoundSlot d → Fin d × Bool) → (Fin d × Bool) × (Fin d × Bool) :=
    fun τ => (τ (i σ n), Parking.reverseDirection (τ (j σ n)))
  have hF : Measurable F := (measurable_pi_apply (i σ n)).prodMk
    ((measurable_of_countable Parking.reverseDirection).comp (measurable_pi_apply (j σ n)))
  have hf : Measurable f := measurable_of_countable _
  have hlaw : (Measure.infinitePi fun _ : Parking.RoundSlot d => Parking.stepLaw d).map F =
      (Parking.stepLaw d).prod (Parking.stepLaw d) :=
    Parking.map_pair_roundEntries hd (i σ n) (j σ n) (hij σ n)
  have heq : (fun τ => LatticeProb.srwHitBy d m (X (Function.update σ n τ) (n + 1))) =
      fun τ => f (F τ) := by
    funext τ
    rw [hnext, hpast σ n n τ le_rfl, hip σ n τ, hjp σ n τ, hup σ n τ, hvp σ n τ,
      Function.update_self]
  rw [heq]
  have hi := integral_map (μ := Measure.infinitePi fun _ : Parking.RoundSlot d => Parking.stepLaw d)
    (φ := F) (f := f) hF.aemeasurable hf.aestronglyMeasurable
  rw [hlaw] at hi
  rw [← hi]
  exact Parking.integral_roundDifference_hitBy_le hd m (X σ n) (u σ n) (v σ n)

end
