/-
The deleted-particle comparison functionals of Step 2.

Step 2 of `lem:product` (`parking.tex:2367-2394`) compares the observable with
"the value after particle `i` is deleted".  Deleting the particle labelled `i`
at a site with `k` particles means exchanging it with the particle labelled
`k-1` and lowering the count by one: the exchange is an admissible relabeling,
so it changes neither the law of the noise nor the value of an observable
symmetric in the particles present, and after it the label `(x, i)` is not read
at all.  That is exactly what the two increment bounds of
`Support/SpliceAvg.lean` ask of a comparison functional.
-/
import Parking.Support.RelabelLaw
import Parking.Support.ParticleSum

open MeasureTheory

noncomputable section

namespace Parking

/-- Adding a particle undoes deleting one at the same site. -/
theorem addAt_delAt {d : ℕ} (x₀ : Site d) (ω : PData d) :
    addAt x₀ (delAt x₀ ω) = ω := by
  refine Prod.ext ?_ rfl
  funext x
  by_cases hx : x = x₀
  · simp [addAt, delAt, addParticle, hx]
  · simp [addAt, delAt, addParticle, hx]

/-- The count of a site after one particle is deleted there. -/
theorem delAt_fst_self {d : ℕ} (x₀ : Site d) (ω : PData d) :
    (delAt x₀ ω).1 x₀ = ω.1 x₀ - 1 := by simp [delAt]

/-- The count of another site is unchanged. -/
theorem delAt_fst_of_ne {d : ℕ} {x₀ x : Site d} (hx : x ≠ x₀) (ω : PData d) :
    (delAt x₀ ω).1 x = ω.1 x := by simp [delAt, hx]

/-- The noise is unchanged by a deletion. -/
theorem delAt_snd {d : ℕ} (x₀ : Site d) (ω : PData d) : (delAt x₀ ω).2 = ω.2 := rfl

/-- **The value after the particle labelled `i` at `x` is deleted.**  The
particle is exchanged with the last particle at the site and the count is
lowered by one. -/
def deleted {d : ℕ} (F : PData d → ℝ) (a : Site d → ℤ) (x : Site d) (i : ℕ)
    (b : PNoise d) : ℝ :=
  F (delAt x (a, relabelNoise x (Equiv.swap i ((a x).toNat - 1)) b))

/-- After the exchange of particle `i` with the last particle, no label below
the lowered count is sent to `i`. -/
theorem swap_ne_left {i k j : ℕ} (hj : j < k - 1) : (Equiv.swap i (k - 1)) j ≠ i := by
  by_cases h : j = i
  · subst h
    rw [Equiv.swap_apply_left]
    omega
  · rw [Equiv.swap_apply_of_ne_of_ne h (by omega)]
    exact h

/-- **The deleted-particle functional does not read the deleted label.**  This
is what makes it a legitimate comparison functional for the step of the
filtration that reveals that label. -/
theorem deleted_congr {d : ℕ} {F : PData d → ℝ} (hFP : ReadsParticles F)
    (a : Site d → ℤ) (x : Site d) (i : ℕ) (b b' : PNoise d)
    (hb : Function.Injective b.2) (hb' : Function.Injective b'.2)
    (hb1 : ∀ q : Label d × ℕ, q.1 ≠ (x, i) → b.1 q = b'.1 q)
    (hb2 : ∀ q : Label d × ℕ, q.1 ≠ (x, i) → b.2 q = b'.2 q) :
    deleted F a x i b = deleted F a x i b' := by
  unfold deleted
  have key : ∀ q : Label d × ℕ,
      q.1.2 < ((delAt x ((a, relabelNoise x (Equiv.swap i ((a x).toNat - 1)) b) : PData d)).1
        q.1.1).toNat →
      (relabelIdx x (Equiv.swap i ((a x).toNat - 1)) q).1 ≠ (x, i) := by
    intro q hq
    by_cases hqx : q.1.1 = x
    · have hcount : (delAt x ((a, relabelNoise x (Equiv.swap i ((a x).toNat - 1)) b)
          : PData d)).1 q.1.1 = a x - 1 := by
        simp [delAt, hqx]
      rw [hcount] at hq
      have hj : q.1.2 < (a x).toNat - 1 := by omega
      simp only [relabelIdx, hqx, ne_eq, Prod.mk.injEq, not_and]
      intro _
      exact swap_ne_left hj
    · simp only [relabelIdx, ne_eq, Prod.mk.injEq, not_and]
      intro hcon
      exact absurd hcon hqx
  refine hFP _ _ (injective_relabelNoise_snd x (Equiv.swap i ((a x).toNat - 1)) hb)
    (injective_relabelNoise_snd x (Equiv.swap i ((a x).toNat - 1)) hb') rfl ?_ ?_
  · intro q hq
    exact hb1 _ (key q hq)
  · intro q hq
    exact hb2 _ (key q hq)

/-- **The deletion does not raise the functional.**  A functional that does not
decrease when a particle is added and is symmetric in the particles present
dominates its deleted-particle comparison. -/
theorem deleted_le {d : ℕ} {F : PData d → ℝ} (hFsym : SymmetricInParticles F)
    (hFmono : ∀ (x₀ : Site d) (ω : PData d), F ω ≤ F (addAt x₀ ω))
    (a : Site d → ℤ) (x : Site d) (i : ℕ) (hi : i < (a x).toNat) (b : PNoise d)
    (hb : Function.Injective b.2) :
    deleted F a x i b ≤ F (a, b) := by
  have hfix : ∀ j : ℕ, (a x).toNat ≤ j → (Equiv.swap i ((a x).toNat - 1)) j = j :=
    swap_apply_of_le hi (by omega)
  have h1 : F ((a, relabelNoise x (Equiv.swap i ((a x).toNat - 1)) b) : PData d)
      = F ((a, b) : PData d) :=
    hFsym x (Equiv.swap i ((a x).toNat - 1)) (a, b) hb hfix
  calc deleted F a x i b
      ≤ F (addAt x (delAt x
          ((a, relabelNoise x (Equiv.swap i ((a x).toNat - 1)) b) : PData d))) :=
        hFmono _ _
    _ = F ((a, relabelNoise x (Equiv.swap i ((a x).toNat - 1)) b) : PData d) := by
        rw [addAt_delAt]
    _ = F ((a, b) : PData d) := h1

/-- **The guarded comparison functional.**  Off the set where the uniform
variables are pairwise distinct, where the relabeling clauses of `lem:product`
say nothing, the comparison is the observable itself, so the two increment
bounds hold at every realization; the guard is almost surely irrelevant. -/
def deletedGuard {d : ℕ} (F : PData d → ℝ) (a : Site d → ℤ) (x : Site d)
    (i : ℕ) (b : PNoise d) : ℝ :=
  Set.indicator {c : PNoise d | Function.Injective c.2}
    (fun c => deleted F a x i c - F ((a, c) : PData d)) b + F ((a, b) : PData d)

theorem deletedGuard_of_injective {d : ℕ} (F : PData d → ℝ) (a : Site d → ℤ) (x : Site d)
    (i : ℕ) {b : PNoise d} (hb : Function.Injective b.2) :
    deletedGuard F a x i b = deleted F a x i b := by
  unfold deletedGuard
  rw [Set.indicator_of_mem hb]
  ring

theorem deletedGuard_of_not_injective {d : ℕ} (F : PData d → ℝ) (a : Site d → ℤ)
    (x : Site d) (i : ℕ) {b : PNoise d} (hb : ¬ Function.Injective b.2) :
    deletedGuard F a x i b = F ((a, b) : PData d) := by
  unfold deletedGuard
  rw [Set.indicator_of_notMem hb]
  ring

/-- The guarded comparison never exceeds a monotone functional. -/
theorem deletedGuard_le {d : ℕ} {F : PData d → ℝ} (hFsym : SymmetricInParticles F)
    (hFmono : ∀ (x₀ : Site d) (ω : PData d), F ω ≤ F (addAt x₀ ω))
    (a : Site d → ℤ) (x : Site d) (i : ℕ) (hi : i < (a x).toNat) (b : PNoise d) :
    deletedGuard F a x i b ≤ F ((a, b) : PData d) := by
  by_cases hb : Function.Injective b.2
  · rw [deletedGuard_of_injective F a x i hb]
    exact deleted_le hFsym hFmono a x i hi b hb
  · rw [deletedGuard_of_not_injective F a x i hb]

/-- **The mean of the deleted-particle functional** is the mean of the
functional at the lowered count. -/
theorem integral_deleted {d : ℕ} (hd : 1 ≤ d) {F : PData d → ℝ} (hFm : Measurable F)
    (a : Site d → ℤ) (x : Site d) (i : ℕ) :
    ∫ b, deleted F a x i b ∂(noiseLaw d)
      = ∫ b, F (delAt x ((a, b) : PData d)) ∂(noiseLaw d) := by
  haveI : IsProbabilityMeasure (stepLaw d) := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    LatticeProb.uniformUnit_isProbability
  haveI : IsProbabilityMeasure (moveLaw d) := by unfold moveLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  haveI : IsProbabilityMeasure (noiseLaw d) := by unfold noiseLaw; infer_instance
  have hmp := measurePreserving_relabelNoise hd x (Equiv.swap i ((a x).toNat - 1))
  have hpair : Measurable fun b : PNoise d =>
      (((fun y => if y = x then a y - 1 else a y) : Site d → ℤ), b) :=
    measurable_const.prodMk measurable_id
  have hg : Measurable fun b : PNoise d => F (delAt x ((a, b) : PData d)) := hFm.comp hpair
  have hkey := integral_map (φ := relabelNoise x (Equiv.swap i ((a x).toNat - 1)))
    (μ := noiseLaw d) (f := fun b : PNoise d => F (delAt x ((a, b) : PData d)))
    hmp.measurable.aemeasurable
    (by rw [hmp.map_eq]; exact hg.aestronglyMeasurable)
  rw [hmp.map_eq] at hkey
  exact hkey.symm

/-- The guard does not change the mean of the comparison. -/
theorem integral_deletedGuard {d : ℕ} (hd : 1 ≤ d) {F : PData d → ℝ} (hFm : Measurable F)
    (a : Site d → ℤ) (x : Site d) (i : ℕ) :
    ∫ b, deletedGuard F a x i b ∂(noiseLaw d)
      = ∫ b, F (delAt x ((a, b) : PData d)) ∂(noiseLaw d) := by
  rw [← integral_deleted hd hFm a x i]
  refine integral_congr_ae ?_
  filter_upwards [noiseLaw_ae_injective hd] with b hb
  exact deletedGuard_of_injective F a x i hb

end Parking

end