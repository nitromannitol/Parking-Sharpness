/-
The uniform variables of the tagged realization with the origin prescribed are
almost surely pairwise distinct.

`FZ = 0` (`parking.tex:2448-2452`) is proved at every realization whose tagged
uniform variables are pairwise distinct (`Parking.survivalObs_mul_holeObs_of_injective`).
With the origin prescribed those variables come from two sources: the
prescription, which supplies the tagged particle's own family `r` and the
uniform variables of the `k-1` particles put back at the origin, and the
realization, which supplies everything else.  The prescribed family is a
countable family of fixed reals, so for almost every realization its uniform
variables are pairwise distinct and avoid the prescription; then the whole
tagged family is pairwise distinct as soon as the prescribed part is.
-/
import Parking.Support.SubcriticalGraftStep1
import Parking.Support.TaggedRankAe

open MeasureTheory

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

theorem graftOrigin_rank_zero {q : Label d × ℕ} (hq : q.1.1 = (0 : Site d)) (ω₁ ω : PData d) :
    (graftOrigin ω₁ ω).2.2 q = ω₁.2.2 q := by
  simp [graftOrigin, hq]

/-- The uniform variables prescribed at the origin: the tagged particle's own
family at the bottom label, and the prescription's at the labels above it. -/
def originRank (r : ℕ → ℝ) (ω₁ : PData d) : ℕ × ℕ → ℝ :=
  fun p => if p.1 = 0 then r p.2 else ω₁.2.2 (((0 : Site d), p.1 - 1), p.2)

theorem taggedRank_graft_origin (r : ℕ → ℝ) (ω₁ ω : PData d) (i s : ℕ) :
    taggedRank r (graftOrigin ω₁ ω).2.2 (((0 : Site d), i), s) = originRank r ω₁ (i, s) := by
  rw [taggedRank_apply]
  unfold originRank
  by_cases hi : i = 0
  · simp [hi]
  · simp [hi, graftOrigin]

theorem taggedRank_graft_of_ne (r : ℕ → ℝ) (ω₁ ω : PData d) {q : Label d × ℕ}
    (hq : q.1.1 ≠ (0 : Site d)) : taggedRank r (graftOrigin ω₁ ω).2.2 q = ω.2.2 q := by
  rw [taggedRank_apply, if_neg hq]
  exact graftOrigin_rank_of_ne hq ω₁ ω

/-- **The tagged uniform variables of the grafted realization are pairwise
distinct** as soon as the prescribed family is, the realization's are, and the
two do not meet. -/
theorem injective_graftTaggedRank {r : ℕ → ℝ} {ω₁ ω : PData d}
    (hP : Function.Injective (originRank r ω₁)) (hω : Function.Injective ω.2.2)
    (hdisj : ∀ (p : ℕ × ℕ) (q : Label d × ℕ), originRank r ω₁ p ≠ ω.2.2 q) :
    Function.Injective (taggedRank r (graftOrigin ω₁ ω).2.2) := by
  rintro ⟨⟨x, i⟩, s⟩ ⟨⟨y, j⟩, u⟩ h
  by_cases hx : x = (0 : Site d) <;> by_cases hy : y = (0 : Site d)
  · subst hx
    subst hy
    rw [taggedRank_graft_origin, taggedRank_graft_origin] at h
    have h2 := hP h
    have hi : i = j := congrArg Prod.fst h2
    have hs : s = u := congrArg Prod.snd h2
    rw [hi, hs]
  · subst hx
    rw [taggedRank_graft_origin,
      taggedRank_graft_of_ne r ω₁ ω (q := (((y, j) : Label d), u)) hy] at h
    exact absurd h (hdisj (i, s) (((y, j) : Label d), u))
  · subst hy
    rw [taggedRank_graft_of_ne r ω₁ ω (q := (((x, i) : Label d), s)) hx,
      taggedRank_graft_origin] at h
    exact absurd h.symm (hdisj (j, u) (((x, i) : Label d), s))
  · rw [taggedRank_graft_of_ne r ω₁ ω (q := (((x, i) : Label d), s)) hx,
      taggedRank_graft_of_ne r ω₁ ω (q := (((y, j) : Label d), u)) hy] at h
    exact hω h

/-- The uniform variables almost surely avoid a countable prescribed family. -/
theorem rankLaw_ae_avoid_countable (d : ℕ) {ι : Type} [Countable ι] (f : ι → ℝ) :
    ∀ᵐ ρ ∂(LatticeProb.rankLaw d),
      ∀ (i : ι) (q : LatticeProb.Label d × ℕ), f i ≠ ρ q := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro q
  have h0 := rankLaw_eq_const_zero d q (f i)
  rw [ae_iff]
  simpa [eq_comm] using h0

/-- The driving data almost surely avoids a countable prescribed family. -/
theorem ae_avoid_pDataLaw_countable (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {ι : Type} [Countable ι] (f : ι → ℝ) :
    ∀ᵐ ω ∂(pDataLaw d ν), ∀ (i : ι) (q : LatticeProb.Label d × ℕ), f i ≠ ω.2.2 q := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (moveLaw d) := by unfold moveLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  have hmap : (pDataLaw d ν).map (fun ω : PData d => ω.2.2) = LatticeProb.rankLaw d := by
    have h1 : (fun ω : PData d => ω.2.2) = Prod.snd ∘ Prod.snd := rfl
    rw [h1, ← Measure.map_map measurable_snd measurable_snd]
    unfold pDataLaw
    rw [Measure.map_snd_prod, measure_univ, one_smul, Measure.map_snd_prod, measure_univ,
      one_smul]
  refine ae_of_ae_map (f := fun ω : PData d => ω.2.2)
    (p := fun ρ : LatticeProb.Label d × ℕ → ℝ =>
      ∀ (i : ι) (q : LatticeProb.Label d × ℕ), f i ≠ ρ q)
    (measurable_snd.comp measurable_snd).aemeasurable ?_
  rw [hmap]
  exact rankLaw_ae_avoid_countable d f

/-- **The tagged uniform variables of the grafted realization are almost surely
pairwise distinct.** -/
theorem ae_injective_graftTaggedRank (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {r : ℕ → ℝ} {ω₁ : PData d} (hP : Function.Injective (originRank r ω₁)) :
    ∀ᵐ ω ∂(pDataLaw d ν), Function.Injective (taggedRank r (graftOrigin ω₁ ω).2.2) := by
  filter_upwards [ae_injective_pDataLaw hd ν,
    ae_avoid_pDataLaw_countable hd ν (originRank r ω₁)] with ω h1 h2
  exact injective_graftTaggedRank hP h1 h2

/-- **`FZ = 0` almost surely**, with the particles at the origin prescribed. -/
theorem ae_graftSurvivalObs_mul_graftHoleObs (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] (w : ℕ → Fin d × Bool) {r : ℕ → ℝ} {ω₁ : PData d}
    (hP : Function.Injective (originRank r ω₁)) (t : ℕ) :
    ∀ᵐ ω ∂(pDataLaw d ν), graftSurvivalObs w r ω₁ t ω * graftHoleObs w ω₁ t ω = 0 := by
  filter_upwards [ae_injective_graftTaggedRank hd ν hP] with ω hω
  exact graftSurvivalObs_mul_graftHoleObs w r ω₁ t ω hω

end Parking

end
