/-
The law of the noise under a relabeling of the particles at a site.

`relabelAt x₀ σ` moves the walk and the uniform variables attached to the label
`(x₀, i)` to the label `(x₀, σ i)` and leaves every other label alone, so on the
noise it is the reindexing of a product of identical factors along an injective
map of the index set.  Such a reindexing preserves the law, which is what makes
the deleted-particle comparison functional of Step 2 of `lem:product`
(`parking.tex:2367-2394`) have the mean the paper's `f(k-1)` gives it: exchanging
the particle to be deleted with the last particle at the site changes neither
the law of the noise nor, by the symmetry hypothesis, the value of the
observable.
-/
import Parking.Support.Relabel
import Parking.Support.NoiseSplice
import LatticeProb.Prob.ZeroOne

open MeasureTheory

noncomputable section

namespace Parking

/-- The reindexing of the labels performed by relabeling at `x₀` by `σ`. -/
def relabelIdx {d : ℕ} (x₀ : Site d) (σ : Equiv.Perm ℕ) (q : Label d × ℕ) : Label d × ℕ :=
  ((q.1.1, if q.1.1 = x₀ then σ q.1.2 else q.1.2), q.2)

/-- The reindexing is injective. -/
theorem relabelIdx_injective {d : ℕ} (x₀ : Site d) (σ : Equiv.Perm ℕ) :
    Function.Injective (relabelIdx x₀ σ) := by
  rintro ⟨⟨x, i⟩, t⟩ ⟨⟨y, j⟩, s⟩ h
  simp only [relabelIdx, Prod.mk.injEq] at h
  obtain ⟨⟨hxy, hij⟩, hts⟩ := h
  subst hxy
  subst hts
  by_cases hx : x = x₀
  · rw [if_pos hx, if_pos hx] at hij
    have hij' : i = j := σ.injective hij
    subst hij'
    rfl
  · rw [if_neg hx, if_neg hx] at hij
    subst hij
    rfl

/-- Relabeling the noise at a site by `σ`. -/
def relabelNoise {d : ℕ} (x₀ : Site d) (σ : Equiv.Perm ℕ) (b : PNoise d) : PNoise d :=
  (LatticeProb.coordShift (relabelIdx x₀ σ) b.1,
    LatticeProb.coordShift (relabelIdx x₀ σ) b.2)

/-- Relabeling the particles at a site keeps the counts and relabels the noise. -/
theorem relabelAt_eq_relabelNoise {d : ℕ} (x₀ : Site d) (σ : Equiv.Perm ℕ) (ω : PData d) :
    relabelAt x₀ σ ω = (ω.1, relabelNoise x₀ σ ω.2) := rfl

/-- Reading a relabeled configuration at a label of the relabeled site. -/
theorem relabelNoise_fst {d : ℕ} (x₀ : Site d) (σ : Equiv.Perm ℕ) (b : PNoise d)
    (q : Label d × ℕ) : (relabelNoise x₀ σ b).1 q = b.1 (relabelIdx x₀ σ q) := rfl

/-- The same for the uniform variables. -/
theorem relabelNoise_snd {d : ℕ} (x₀ : Site d) (σ : Equiv.Perm ℕ) (b : PNoise d)
    (q : Label d × ℕ) : (relabelNoise x₀ σ b).2 q = b.2 (relabelIdx x₀ σ q) := rfl

/-- Relabeling permutes the uniform variables, so it preserves their distinctness. -/
theorem injective_relabelNoise_snd {d : ℕ} (x₀ : Site d) (σ : Equiv.Perm ℕ) {b : PNoise d}
    (hb : Function.Injective b.2) : Function.Injective (relabelNoise x₀ σ b).2 := by
  intro q q' hq
  rw [relabelNoise_snd, relabelNoise_snd] at hq
  exact relabelIdx_injective x₀ σ (hb hq)

/-- **Relabeling the noise at a site preserves its law.** -/
theorem measurePreserving_relabelNoise {d : ℕ} (hd : 1 ≤ d) (x₀ : Site d) (σ : Equiv.Perm ℕ) :
    MeasurePreserving (relabelNoise x₀ σ) (noiseLaw d) (noiseLaw d) := by
  haveI : IsProbabilityMeasure (stepLaw d) := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    LatticeProb.uniformUnit_isProbability
  haveI : IsProbabilityMeasure (moveLaw d) := by unfold moveLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  have h1 : MeasurePreserving (LatticeProb.coordShift (relabelIdx x₀ σ))
      (moveLaw d) (moveLaw d) :=
    LatticeProb.measurePreserving_coordShift (fun _ : Label d × ℕ => stepLaw d)
      (relabelIdx_injective x₀ σ) (fun _ => rfl)
  have h2 : MeasurePreserving (LatticeProb.coordShift (relabelIdx x₀ σ))
      (LatticeProb.rankLaw d) (LatticeProb.rankLaw d) :=
    LatticeProb.measurePreserving_coordShift
      (fun _ : Label d × ℕ => MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
      (relabelIdx_injective x₀ σ) (fun _ => rfl)
  exact h1.prod h2

end Parking

end
