/-
`LatticeProb.dtail` is ANTITONE in its level argument (a tail sum over MORE removed terms is
smaller, for a nonnegative summable sequence): `dtail a m2 ≤ dtail a m1` for `m1 ≤ m2`.  This
lets `Parking.exists_dtail_moment`'s moment bound, called ONCE at `n1 := 0`, bound `E[dtail(
levelInc, R, ·)^p]` UNIFORMLY IN `R` — avoiding the need to track how `exists_levelInc_tail_
moment`'s own constant depends on `n1` (it is not exposed, and re-deriving that dependence would
duplicate a large part of `TightBoxSupTail.lean`).
-/
import Parking.Support.TightBoxSupTailMoment

open MeasureTheory LatticeProb Filter Topology

noncomputable section

namespace Parking

/-- **`dtail` is antitone in its level argument**, for a nonnegative summable sequence: removing
more leading terms from the tail only shrinks it. -/
theorem dtail_antitone {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hsum : Summable a) {m1 m2 : ℕ}
    (hm : m1 ≤ m2) : LatticeProb.dtail a m2 ≤ LatticeProb.dtail a m1 := by
  have hsum1 : Summable (fun i : ℕ => a (i + (m1 + 1))) := (summable_nat_add_iff (m1 + 1)).mpr hsum
  have hinj : Function.Injective (fun i : ℕ => i + (m2 - m1)) := fun x y h => by
    simpa using h
  have hle := tsum_comp_le_tsum_of_inj hsum1 (fun i => ha _) hinj
  have heq : (fun i : ℕ => a (i + (m1 + 1))) ∘ (fun i : ℕ => i + (m2 - m1)) =
      fun i : ℕ => a (i + (m2 + 1)) := by
    funext i
    simp only [Function.comp_apply]
    congr 1
    omega
  rw [heq] at hle
  show (∑' i, a (i + (m2 + 1))) ≤ ∑' i, a (i + (m1 + 1))
  exact hle

/-- **`dtail(levelInc, R, ·) ≤ dtail(levelInc, 0, ·)` a.e., for EVERY `R`, uniformly in the
scale `n`.** -/
theorem ae_dtail_le_dtail_zero (ν : Measure ℤ) (hν : CriticalLaw ν) {A : ℝ} (hA : 0 ≤ A)
    (n : ℕ) (hn : 1 ≤ n) (R : ℕ) :
    ∀ᵐ η ∂(iidLaw 2 (realLaw ν)),
      LatticeProb.dtail (fun m => levelInc A hA n m η) R ≤
        LatticeProb.dtail (fun m => levelInc A hA n m η) 0 := by
  filter_upwards [ae_summable_levelInc ν hν hA n hn 0] with η hsum
  exact dtail_antitone (levelInc_nonneg A hA n · η) hsum (Nat.zero_le R)

/-- **`E[dtail(levelInc, R, ·)^p]` is bounded by a SINGLE constant, uniform in BOTH the scale `n`
and the box radius `R`**, with the constant itself bounded by `K * (1 + A) ^ (p / 2)` for a
SINGLE constant `K`, chosen before `A` and independent of it. -/
theorem exists_dtail_moment_uniform (ν : Measure ℤ) (hν : CriticalLaw ν) (p : ℝ) (hp : 12 < p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ℝ) (hA : 0 ≤ A), ∃ C : ℝ, 0 ≤ C ∧ C ≤ K * (1 + A) ^ (p / 2) ∧
      ∀ (R n : ℕ), 1 ≤ n →
      Integrable (fun η : Site 2 → ℝ =>
          (LatticeProb.dtail (fun m => levelInc A hA n m η) R) ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, (LatticeProb.dtail (fun m => levelInc A hA n m η) R) ^ p
          ∂(iidLaw 2 (realLaw ν))) ≤ C := by
  obtain ⟨K, hKnn, hKall⟩ := exists_dtail_moment ν hν 0 p hp
  refine ⟨K, hKnn, fun A hA => ?_⟩
  obtain ⟨C, hCnn, hCbd, hbound⟩ := hKall A hA
  refine ⟨C, hCnn, hCbd, fun R n hn => ?_⟩
  obtain ⟨hint0, hbound0⟩ := hbound n hn
  obtain ⟨K', _hK'nn, hK'all⟩ := exists_dtail_moment ν hν R p hp
  obtain ⟨CR, _, _, hboundR⟩ := hK'all A hA
  obtain ⟨hintR, _⟩ := hboundR n hn
  have hae := ae_dtail_le_dtail_zero ν hν hA n hn R
  have hnnR : ∀ η, 0 ≤ LatticeProb.dtail (fun m => levelInc A hA n m η) R :=
    fun η => LatticeProb.dtail_nonneg (levelInc_nonneg A hA n · η) R
  refine ⟨hintR, ?_⟩
  calc (∫ η, (LatticeProb.dtail (fun m => levelInc A hA n m η) R) ^ p
        ∂(iidLaw 2 (realLaw ν)))
      ≤ ∫ η, (LatticeProb.dtail (fun m => levelInc A hA n m η) 0) ^ p
          ∂(iidLaw 2 (realLaw ν)) :=
        integral_mono_ae hintR hint0 (by
          filter_upwards [hae] with η hη
          exact Real.rpow_le_rpow (hnnR η) hη (by linarith))
    _ ≤ C := hbound0

end Parking

end
