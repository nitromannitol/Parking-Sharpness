/-
Step 2 of `thm:subcritical` (`parking.tex:2464-2482`): the pair `(F, Z)` of
`Support/SubcriticalPair.lean` satisfies every hypothesis of `lem:product`, so
its covariance under the conditioned tilted law is at most three times the
derivative of `E_λ F` in the tilt.

"Both `F` and `Z` depend only on the finitely many sites within distance `t` of
`R_t`.  They are invariant under relabeling the particles at those sites.  By
Lemma 4.6, `F` is nondecreasing when a particle is added; by Lemma 3.4, `Z` is
nonincreasing and changes by at most one.  Thus Lemma 9.2 applies."
-/
import Parking.Support.SubcriticalInvariance
import Parking.Support.HoleObsIntegrable
import Parking.Support.TiltCov

open MeasureTheory LatticeProb

noncomputable section

namespace Parking

variable {d : ℕ}

/-- The box of sites the two observables read: the range of the prescribed walk
lies in it, and so does everything the process can reach from it by time `t`. -/
def subcriticalBox (d : ℕ) (t : ℕ) : Finset (Site d) :=
  boxFinset (0 : Site d) (t + t * (t + 1))

/-- A functional of the data at the sites of `N` is one of the data at the sites
of any larger finite set. -/
theorem DependsOn.mono {N M : Finset (Site d)} {F : PData d → ℝ} (hNM : N ⊆ M)
    (hF : DependsOn N F) : DependsOn M F := fun ω ω' hc hm hr =>
  hF ω ω' (fun x hx => hc x (hNM hx)) (fun q hq => hm q (hNM hq)) fun q hq => hr q (hNM hq)

/-- **Step 2 of `thm:subcritical`.**  The covariance of the survival indicator
and the hole count of the range, under the law in which the sites of `N` carry
the tilted law and the rest is a fixed background, is at most three times the
derivative of the tilted mean of the survival indicator. -/
theorem abs_cov_subcritical_le (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    {θ : ℝ} (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamθ : lam < θ)
    (hmeanint : Integrable (fun k : ℤ => (k : ℝ)) (tiltLaw ν lam))
    (hmeanle : ∫ k, (k : ℝ) ∂(tiltLaw ν lam) ≤ 0)
    (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) (t : ℕ) {N : Finset (Site d)}
    (hN : subcriticalBox d t ⊆ N) (ω₀ : PData d) {D : ℝ}
    (hD : HasDerivAt (fun s => ∫ ω, survivalObs w r t ω
        ∂(restrictLaw d N (tiltLaw ν s) ω₀)) D lam) :
    Integrable (fun ω => survivalObs w r t ω * holeObs w t ω)
        (restrictLaw d N (tiltLaw ν lam) ω₀) ∧
      |cov (restrictLaw d N (tiltLaw ν lam) ω₀) (survivalObs w r t) (holeObs w t)|
        ≤ 3 * D := by
  haveI : IsProbabilityMeasure (tiltLaw ν lam) :=
    tiltLaw_isProbability (integrable_exp_tilt hexp hlam0 (le_of_lt hlamθ))
  have hrange : rangeFinset (0 : Site d) w t ⊆ N := fun x hx =>
    hN (boxFinset_mono (by omega) (rangeFinset_subset_box w t hx))
  refine abs_cov_le_deriv (N := N) (F := survivalObs w r t) (Z := holeObs w t)
    hd hint hθ hexp hlam0 hlamθ hmeanint hmeanle ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hD
  · exact (dependsOn_survivalObs w r t).mono hN
  · exact relabelInvariant_survivalObs w r t
  · exact (dependsOn_holeObs w t).mono hN
  · exact relabelInvariant_holeObs w t
  · exact measurable_survivalObs w r t
  · exact measurable_holeObs w t
  · exact survivalObs_mem_Icc w r t
  · exact fun x₀ ω => survivalObs_mono hd w r t x₀ ω
  · exact fun x₀ ω => holeObs_anti hd w t x₀ ω
  · exact fun x₀ ω => ⟨holeObs_add_lip hd w t x₀ ω, holeObs_del_lip hd w t x₀ ω⟩
  · exact integrable_holeObs (ν := tiltLaw ν lam) hd hmeanint.abs w t hrange ω₀

/-- The tagged uniform variables are pairwise distinct as soon as those of the
realization are, the prescribed ones are, and the two families do not meet.
This is what the guard on the survival observable used to assert; it is now
discharged where it is needed instead of carried by the observable. -/
theorem taggedRank_tagged (r : ℕ → ℝ) (v : LatticeProb.Label d × ℕ → ℝ) (s : ℕ) :
    taggedRank r v (((0 : Site d), 0), s) = r s := by
  simp [taggedRank]

theorem injective_taggedRank {r : ℕ → ℝ} {v : LatticeProb.Label d × ℕ → ℝ}
    (hv : Function.Injective v) (hr : Function.Injective r)
    (hdisj : ∀ (s : ℕ) (q : LatticeProb.Label d × ℕ), r s ≠ v q) :
    Function.Injective (taggedRank r v) := by
  rintro ⟨p, s⟩ ⟨q, u⟩ h
  by_cases hp : p = ((0 : Site d), 0) <;> by_cases hq : q = ((0 : Site d), 0)
  · subst hp
    subst hq
    rw [taggedRank_tagged, taggedRank_tagged] at h
    rw [hr h]
  · subst hp
    rw [taggedRank_tagged, taggedRank_apply_of_ne r v q u hq] at h
    exact absurd h (hdisj s (taggedSource q, u))
  · subst hq
    rw [taggedRank_apply_of_ne r v p s hp, taggedRank_tagged] at h
    exact absurd h.symm (hdisj u (taggedSource p, s))
  · rw [taggedRank_apply_of_ne r v p s hp, taggedRank_apply_of_ne r v q u hq] at h
    have h2 := hv h
    have h3 : taggedSource p = taggedSource q := congrArg Prod.fst h2
    have h4 : s = u := congrArg Prod.snd h2
    rw [taggedSource_inj hp hq h3, h4]

/-- A realization whose origin carries a hole carries no tagged particle: adding
one particle to a negative count still leaves no particle there, so the tagged
label is inactive and the survival indicator vanishes. -/
theorem survivalObs_eq_zero_of_neg (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) (t : ℕ)
    {ω : PData d} (hη : ω.1 (0 : Site d) < 0) : survivalObs w r t ω = 0 := by
  classical
  unfold survivalObs
  refine Set.indicator_of_notMem ?_ _
  intro hmem
  have hact : (pState (taggedDriver w r ω) t).active ((0 : Site d), 0) = true := hmem
  have hlt := pState_active_lt (taggedDriver w r ω) t ((0 : Site d), 0) hact
  have heta : (taggedDriver w r ω).eta (0 : Site d) = ω.1 (0 : Site d) + 1 := by
    show addParticle (0 : Site d) ω.1 (0 : Site d) = ω.1 (0 : Site d) + 1
    simp [addParticle]
  rw [heta] at hlt
  simp only at hlt
  omega

/-- **`FZ = 0`, Step 1 of `thm:subcritical`** (`parking.tex:2448-2452`), at every
realization whose tagged uniform variables are pairwise distinct.  Where the
origin carries a hole the survival indicator vanishes outright, so no condition
on the count at the origin is needed. -/
theorem survivalObs_mul_holeObs_of_injective (w : ℕ → Fin d × Bool) (rk : ℕ → ℝ) (t : ℕ)
    (ω : PData d) (hinj : Function.Injective (taggedRank rk ω.2.2)) :
    survivalObs w rk t ω * holeObs w t ω = 0 := by
  rcases le_or_gt (0 : ℤ) (ω.1 (0 : Site d)) with h | h
  · exact survivalObs_mul_holeObs w rk t ω h hinj
  · rw [survivalObs_eq_zero_of_neg w rk t h, zero_mul]

/-- When the product of two observables vanishes almost surely, their covariance
is minus the product of their means.  This is the first sentence of Step 2,
`parking.tex:2477-2479`. -/
theorem cov_of_mul_ae_zero {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    {F Z : Ω → ℝ} (hFZ : ∀ᵐ ω ∂μ, F ω * Z ω = 0) :
    cov μ F Z = -((∫ ω, F ω ∂μ) * ∫ ω, Z ω ∂μ) := by
  unfold cov
  have h0 : ∫ ω, F ω * Z ω ∂μ = 0 := by
    rw [integral_congr_ae (g := fun _ => (0 : ℝ)) hFZ, integral_zero]
  rw [h0, zero_sub]

/-- **The differential inequality of Step 2** (`parking.tex:2471-2474`), given
that the product of the two observables vanishes almost surely: the mean number
of unfilled holes of the range times the survival probability is at most three
times the derivative of the survival probability in the tilt. -/
theorem mean_mul_mean_le_deriv (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    {θ : ℝ} (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamθ : lam < θ)
    (hmeanint : Integrable (fun k : ℤ => (k : ℝ)) (tiltLaw ν lam))
    (hmeanle : ∫ k, (k : ℝ) ∂(tiltLaw ν lam) ≤ 0)
    (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) (t : ℕ) {N : Finset (Site d)}
    (hN : subcriticalBox d t ⊆ N) (ω₀ : PData d) {D : ℝ}
    (hD : HasDerivAt (fun s => ∫ ω, survivalObs w r t ω
        ∂(restrictLaw d N (tiltLaw ν s) ω₀)) D lam)
    (hFZ : ∀ᵐ ω ∂(restrictLaw d N (tiltLaw ν lam) ω₀),
      survivalObs w r t ω * holeObs w t ω = 0) :
    (∫ ω, survivalObs w r t ω ∂(restrictLaw d N (tiltLaw ν lam) ω₀))
        * ∫ ω, holeObs w t ω ∂(restrictLaw d N (tiltLaw ν lam) ω₀) ≤ 3 * D := by
  haveI : IsProbabilityMeasure (tiltLaw ν lam) :=
    tiltLaw_isProbability (integrable_exp_tilt hexp hlam0 (le_of_lt hlamθ))
  have hbound := abs_cov_subcritical_le hd hint hθ hexp hlam0 hlamθ hmeanint hmeanle
    w r t hN ω₀ hD
  have hcov := cov_of_mul_ae_zero (restrictLaw d N (tiltLaw ν lam) ω₀) hFZ
  have habs := hbound.2
  rw [hcov, abs_neg] at habs
  exact le_trans (le_abs_self _) habs

end Parking

end
