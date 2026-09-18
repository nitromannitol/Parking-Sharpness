/-
**The cutoff construction for the `d`-dimensional simple random walk's optimal-stopping value.**
(Distinct from `Parking.spatialCutoff`, `Parking/Support/SpatialCutoff.lean`'s own real-valued
bump function for the ORIENTED node's rescaled potential field: this module's cutoff acts on the
UNDIRECTED walk's stopping-problem REWARD, by `Parking.graphNorm`-radius, not on a real argument.)

In `Parking.abs_u_sub_le_of_linPotential_osc` (`USpatialOscillation.lean`), the odometer's
spatial oscillation reduces to `Parking.stoppingSup` at the reward `-Parking.linPotential`, a
reward that is a.s. UNBOUNDED on the whole lattice, so no uniform (in probability) bound on the
reward's oscillation over every site the walk can reach holds directly. The fix, matching what
BP's own citations for the analogous oriented node already anticipate ("the application supplies
the reward through a spatial cutoff"), is to compare the TRUE stopping value to the value of the
SAME problem with the reward truncated to a growing box, and control the error by the walk's own
probability of leaving that box within its horizon
(`Parking.measureReal_sup_walkPath_graphNorm_le`, `WalkMaximal.lean`).

This module builds exactly that comparison for a GENERAL bounded reward field, with NO
probabilistic hypothesis beyond a uniform sup bound on the reward: the cutoff reward
(`Parking.cutoffReward`), its exactness inside the box (`Parking.cutoffReward_eq_of_le`), the
cutoff value (`Parking.cutoffStoppingSup`), and the cutoff error bound
(`Parking.abs_terminalValue_sub_cutoffReward_le`), which visibly tends to `0` as `A → ∞` for
each fixed `n` (via `Parking.measureReal_sup_walkPath_graphNorm_le'`), and stays small as
`n, A → ∞` together provided `A` grows faster than `√n`, matching the usual parabolic cutoff
scaling. This is unconditional: no External, no `sorry`.
-/
import Parking.Support.WalkMaximal
import Parking.Support.ValueLipschitz

open MeasureTheory

noncomputable section

namespace Parking

variable {d : ℕ}

/-! ### The cutoff reward, and its exactness inside the box -/

/-- **The cutoff reward**: `F` truncated to the box of `Parking.graphNorm`-radius `A` about the
origin, `0` outside. -/
def cutoffReward (F : ℕ → Site d → ℝ) (A : ℝ) (k : ℕ) (z : Site d) : ℝ :=
  if (graphNorm z : ℝ) ≤ A then F k z else 0

/-- **Exactness inside the box**: the cutoff reward agrees with the true reward at every site
within radius `A`. No hat-interpolation, no clamping error: the reward itself is exact inside
the box. -/
theorem cutoffReward_eq_of_le (F : ℕ → Site d → ℝ) (A : ℝ) (k : ℕ) (z : Site d)
    (hz : (graphNorm z : ℝ) ≤ A) : cutoffReward F A k z = F k z :=
  if_pos hz

theorem cutoffReward_eq_zero_of_lt (F : ℕ → Site d → ℝ) (A : ℝ) (k : ℕ) (z : Site d)
    (hz : ¬ (graphNorm z : ℝ) ≤ A) : cutoffReward F A k z = 0 :=
  if_neg hz

/-- **A bound on the true reward bounds the cutoff reward, everywhere, not just inside the
box.** -/
theorem abs_cutoffReward_le (F : ℕ → Site d → ℝ) (A : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hFb : ∀ k y, |F k y| ≤ M) (k : ℕ) (z : Site d) : |cutoffReward F A k z| ≤ M := by
  unfold cutoffReward
  split_ifs
  · exact hFb k z
  · simpa using hM

/-! ### The maximal-displacement tail, restated at the natural cutoff threshold `A` -/

/-- **`Parking.measureReal_sup_walkPath_graphNorm_le`, restated at the natural cutoff threshold
`A`** (rather than `d·A`): the walk's own `Parking.graphNorm` displacement exceeds `A` by time
`n` with probability at most `n·d²/A²`. -/
theorem measureReal_sup_walkPath_graphNorm_le' (hd : 1 ≤ d) (n : ℕ) {A : ℝ} (hA : 0 < A) :
    (walkLaw d).real {p | ∃ k ≤ n, A ≤ (graphNorm (walkPath (0 : Site d) p k) : ℝ)}
      ≤ (n : ℝ) * d ^ 2 / A ^ 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hA' : 0 < A / d := by positivity
  have h := measureReal_sup_walkPath_graphNorm_le hd n hA'
  have hdA : (d : ℝ) * (A / d) = A := by field_simp
  rw [hdA] at h
  refine h.trans_eq ?_
  rw [div_pow]
  field_simp

/-! ### The cutoff optimal-stopping value -/

/-- **The cutoff optimal-stopping value**: `Parking.stoppingSup` at the cutoff reward, started
at the origin (the general starting site reduces to this one by `Parking.stoppingSup_eq_shift`,
exactly as `Parking.USpatialOscillation` already uses for the true reward). -/
def cutoffStoppingSup (F : ℕ → Site d → ℝ) (A : ℝ) (n : ℕ) : ℝ :=
  stoppingSup d (cutoffReward F A) n (0 : Site d)

/-- **The cutoff value is bounded by any bound on the true reward.** -/
theorem abs_cutoffStoppingSup_le (hd : 1 ≤ d) (F : ℕ → Site d → ℝ) (A : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hFb : ∀ k y, |F k y| ≤ M) (n : ℕ) : |cutoffStoppingSup F A n| ≤ M := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  unfold cutoffStoppingSup
  have hbd : ∀ k y, |cutoffReward F A k y| ≤ M := abs_cutoffReward_le F A hM hFb
  have hub : stoppingSup d (cutoffReward F A) n (0 : Site d) ≤ M :=
    stoppingSup_le hd (cutoffReward F A) n (0 : Site d) hM (fun k y => (abs_le.mp (hbd k y)).2)
  have hlb : -M ≤ stoppingSup d (cutoffReward F A) n (0 : Site d) := by
    have hmem : cutoffReward F A 0 (0 : Site d)
        ∈ terminalValues d (cutoffReward F A) n (0 : Site d) := by
      refine ⟨fun _ => 0, ⟨fun _ => Nat.zero_le _, fun _ _ _ => rfl⟩, ?_⟩
      unfold terminalValue
      simp [walkPath]
    have hle : cutoffReward F A 0 (0 : Site d) ≤ stoppingSup d (cutoffReward F A) n (0 : Site d) :=
      le_csSup (bddAbove_terminalValues hd (cutoffReward F A) n (0 : Site d) hbd) hmem
    linarith [(abs_le.mp (hbd 0 0)).1]
  exact abs_le.mpr ⟨hlb, hub⟩

/-- **`Parking.cutoffStoppingSup` is Lipschitz in the underlying reward**, for the same reason
`Parking.stoppingSup` itself is (`Parking.abs_stoppingSup_sub_le`): the cutoff of a
uniformly-close pair of rewards is a uniformly-close pair of cutoff rewards, at the same
constant. -/
theorem abs_cutoffStoppingSup_sub_le (hd : 1 ≤ d) (F G : ℕ → Site d → ℝ) (A : ℝ) {c M : ℝ}
    (hFb : ∀ k y, |F k y| ≤ M) (hGb : ∀ k y, |G k y| ≤ M)
    (hdiff : ∀ k y, |F k y - G k y| ≤ c) (n : ℕ) :
    |cutoffStoppingSup F A n - cutoffStoppingSup G A n| ≤ c := by
  unfold cutoffStoppingSup
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hFb 0 0)
  refine abs_stoppingSup_sub_le hd (cutoffReward F A) (cutoffReward G A) n (0 : Site d)
    (c := c) (M := M) (abs_cutoffReward_le F A hM hFb) (abs_cutoffReward_le G A hM hGb) ?_
  intro k y
  unfold cutoffReward
  split_ifs with h
  · exact hdiff k y
  · rw [sub_self, abs_zero]
    exact le_trans (abs_nonneg _) (hdiff 0 0)

/-! ### The cutoff error bound: the crux of the construction -/

/-- **The cutoff error bound, rule by rule**: for one fixed bounded stopping rule, the true and
cutoff terminal rewards differ only through the event that the walk's own position at some time
up to the horizon lies outside the box, and there by at most the reward's own bound. -/
theorem abs_terminalValue_sub_cutoffReward_le (hd : 1 ≤ d) (F : ℕ → Site d → ℝ) (A M : ℝ)
    (hFb : ∀ k y, |F k y| ≤ M) (n : ℕ) {σ : (ℕ → Fin d × Bool) → ℕ}
    (hσ : IsStoppingTimeLE n σ) :
    |terminalValue F (0 : Site d) σ - terminalValue (cutoffReward F A) (0 : Site d) σ|
      ≤ M * (walkLaw d).real {p | ∃ k ≤ n, A < (graphNorm (walkPath (0 : Site d) p k) : ℝ)} := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hFb 0 0)
  have hF := integrable_terminalReward hd hσ F (0 : Site d)
  have hG := integrable_terminalReward hd hσ (cutoffReward F A) (0 : Site d)
  set E : Set (ℕ → Fin d × Bool) :=
      {p | ∃ k ≤ n, A < (graphNorm (walkPath (0 : Site d) p k) : ℝ)} with hEdef
  have hEmeas : MeasurableSet E := by
    have hEeq : E = ⋃ k ∈ Finset.range (n + 1),
        {p | A < (graphNorm (walkPath (0 : Site d) p k) : ℝ)} := by
      ext p
      simp only [hEdef, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range]
      constructor
      · rintro ⟨k, hk, hlt⟩; exact ⟨k, by omega, hlt⟩
      · rintro ⟨k, hk, hlt⟩; exact ⟨k, by omega, hlt⟩
    rw [hEeq]
    refine Finset.measurableSet_biUnion _ (fun k _ => ?_)
    exact measurableSet_lt measurable_const
      ((Measurable.of_discrete (f := fun z : Site d => (graphNorm z : ℝ))).comp
        (measurable_walkPath (0 : Site d) k))
  have hsub : terminalValue F (0 : Site d) σ - terminalValue (cutoffReward F A) (0 : Site d) σ
      = ∫ p, (F (σ p) (walkPath (0 : Site d) p (σ p))
          - cutoffReward F A (σ p) (walkPath (0 : Site d) p (σ p))) ∂(walkLaw d) := by
    rw [terminalValue, terminalValue, ← integral_sub hF hG]
  rw [hsub]
  have hpt : ∀ p, |F (σ p) (walkPath (0 : Site d) p (σ p))
      - cutoffReward F A (σ p) (walkPath (0 : Site d) p (σ p))| ≤ E.indicator (fun _ => M) p := by
    intro p
    unfold cutoffReward
    by_cases hbox : (graphNorm (walkPath (0 : Site d) p (σ p)) : ℝ) ≤ A
    · rw [if_pos hbox, sub_self, abs_zero]
      exact Set.indicator_nonneg (fun _ _ => hM) p
    · rw [if_neg hbox, sub_zero]
      have hmem : p ∈ E := ⟨σ p, hσ.1 p, not_le.mp hbox⟩
      rw [Set.indicator_of_mem hmem]
      exact hFb (σ p) (walkPath (0 : Site d) p (σ p))
  calc |∫ p, (F (σ p) (walkPath (0 : Site d) p (σ p))
        - cutoffReward F A (σ p) (walkPath (0 : Site d) p (σ p))) ∂(walkLaw d)|
      ≤ ∫ p, |F (σ p) (walkPath (0 : Site d) p (σ p))
          - cutoffReward F A (σ p) (walkPath (0 : Site d) p (σ p))| ∂(walkLaw d) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ p, E.indicator (fun _ => M) p ∂(walkLaw d) :=
        integral_mono (hF.sub hG).abs ((integrable_const M).indicator hEmeas) hpt
    _ = M * (walkLaw d).real E := by
        rw [integral_indicator_const _ hEmeas, smul_eq_mul, mul_comm, measureReal_def]

/-- **The cutoff error bound for the VALUE**: the true and cutoff optimal-stopping values differ
by at most `M` times the walk's own probability of leaving the box of radius `A` within the
horizon `n`, uniformly over every stopping rule bounded by `n`. Combined with
`Parking.measureReal_sup_walkPath_graphNorm_le'`, the right-hand side is `≤ M·n·d²/A²`, which
visibly `→ 0` as `A → ∞` for each fixed `n`: **this is the cutoff construction's main theorem**,
assembling the cutoff value, the exactness inside the box, the maximal-displacement tail, and the
cutoff error `→ 0` as `A → ∞`. -/
theorem abs_stoppingSup_sub_cutoffStoppingSup_le (hd : 1 ≤ d) (F : ℕ → Site d → ℝ) (A M : ℝ)
    (hFb : ∀ k y, |F k y| ≤ M) (n : ℕ) :
    |stoppingSup d F n (0 : Site d) - cutoffStoppingSup F A n|
      ≤ M * (walkLaw d).real {p | ∃ k ≤ n, A < (graphNorm (walkPath (0 : Site d) p k) : ℝ)} := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hFb 0 0)
  set c : ℝ :=
      M * (walkLaw d).real {p | ∃ k ≤ n, A < (graphNorm (walkPath (0 : Site d) p k) : ℝ)}
    with hcdef
  have hc0 : 0 ≤ c := by
    rw [hcdef]; exact mul_nonneg hM (measureReal_nonneg)
  have hbF := bddAbove_terminalValues hd F n (0 : Site d) hFb
  have hbG := bddAbove_terminalValues hd (cutoffReward F A) n (0 : Site d)
    (abs_cutoffReward_le F A hM hFb)
  have hneF := terminalValues_nonempty d F n (0 : Site d)
  have hneG := terminalValues_nonempty d (cutoffReward F A) n (0 : Site d)
  have key : ∀ (F' : ℕ → Site d → ℝ) (G' : ℕ → Site d → ℝ),
      (∀ (τ : (ℕ → Fin d × Bool) → ℕ), IsStoppingTimeLE n τ →
        |terminalValue F' (0 : Site d) τ - terminalValue G' (0 : Site d) τ| ≤ c) →
      BddAbove (terminalValues d G' n (0 : Site d)) →
      (terminalValues d F' n (0 : Site d)).Nonempty →
      stoppingSup d F' n (0 : Site d) ≤ stoppingSup d G' n (0 : Site d) + c := by
    intro F' G' hbound hb hne
    refine csSup_le hne ?_
    rintro a ⟨τ, hτ, rfl⟩
    have h1 : terminalValue G' (0 : Site d) τ ≤ stoppingSup d G' n (0 : Site d) :=
      le_csSup hb ⟨τ, hτ, rfl⟩
    have h2 := hbound τ hτ
    have := (abs_sub_le_iff.mp h2).1
    linarith
  have h1 := key F (cutoffReward F A)
    (fun τ hτ => abs_terminalValue_sub_cutoffReward_le hd F A M hFb n hτ) hbG hneF
  have h2 := key (cutoffReward F A) F
    (fun τ hτ => by
      rw [abs_sub_comm]
      exact abs_terminalValue_sub_cutoffReward_le hd F A M hFb n hτ) hbF hneG
  unfold cutoffStoppingSup
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- **The cutoff error, in the natural threshold `A`**: combining
`Parking.abs_stoppingSup_sub_cutoffStoppingSup_le` with
`Parking.measureReal_sup_walkPath_graphNorm_le'`. The right-hand side `→ 0` as `A → ∞` for each
fixed `n`, and stays small as `n → ∞` provided `A` grows faster than `√n` times a constant
depending only on `d`. -/
theorem abs_stoppingSup_sub_cutoffStoppingSup_le' (hd : 1 ≤ d) (F : ℕ → Site d → ℝ) {A M : ℝ}
    (hA : 0 < A) (hFb : ∀ k y, |F k y| ≤ M) (n : ℕ) :
    |stoppingSup d F n (0 : Site d) - cutoffStoppingSup F A n| ≤ M * ((n : ℝ) * d ^ 2 / A ^ 2) := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hFb 0 0)
  have h1 := abs_stoppingSup_sub_cutoffStoppingSup_le hd F A M hFb n
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ hM)
  have hsub : {p | ∃ k ≤ n, A < (graphNorm (walkPath (0 : Site d) p k) : ℝ)}
      ⊆ {p | ∃ k ≤ n, A ≤ (graphNorm (walkPath (0 : Site d) p k) : ℝ)} :=
    fun p ⟨k, hk, hlt⟩ => ⟨k, hk, hlt.le⟩
  exact (measureReal_mono hsub).trans (measureReal_sup_walkPath_graphNorm_le' hd n hA)

end Parking

end
