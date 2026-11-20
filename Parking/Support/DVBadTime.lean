import Parking.Support.DVTrialsMartingale

/-!
# Little time in porous boxes

A walk with a small range spends little time in boxes that its range leaves porous:

  `P_0(|R_t| ≤ n, #{j < t : X_j in a box porous at time t} ≥ θ t) ≤ 2 e^{n - q (θ t - 3ℓ)/(2ℓ)}`

with `ℓ = 2m^2` and `q = (1 - e^{-1}) p₀` (`measureReal_endPorous_le`).  Each time in an
end-porous box makes the trial of its block present, so at least `(θ t - 3ℓ)/ℓ` trials are
present among the blocks before `t`, at least half of them in one parity class; the successes
in that class are at most `|R_t| ≤ n`; and many present trials with few successes are unlikely
(`measureReal_present_success_le`).
-/

noncomputable section

namespace Parking

open LatticeProb MeasureTheory

variable {d : ℕ}

open scoped Classical in
/-- **The deterministic count**: the number of times in end-porous boxes is at most `ℓ` times
the number of present trials of the two parity classes, plus `3ℓ`. -/
theorem card_endPorous_le {m : ℕ} [NeZero m] {δ : ℝ} {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {t : ℕ}
    (hℓt : ℓ ≤ t) (X : ℕ → Site d) :
    ((Finset.range t).filter fun j => EndPorous m δ X t j).card
      ≤ ℓ * (((Finset.range ((t / ℓ - 1) / 2)).filter fun i => Present m δ ℓ (0 + 2 * i) X).card
        + ((Finset.range ((t / ℓ - 1) / 2)).filter fun i => Present m δ ℓ (1 + 2 * i) X).card)
        + 3 * ℓ := by
  set J := (t / ℓ - 1) / 2 with hJ
  set B := (Finset.range t).filter fun j => EndPorous m δ X t j
  set P0 := (Finset.range J).filter fun i => Present m δ ℓ (0 + 2 * i) X
  set P1 := (Finset.range J).filter fun i => Present m δ ℓ (1 + 2 * i) X
  set P := (Finset.range (2 * J)).filter fun k => Present m δ ℓ k X
  have htl : 1 ≤ t / ℓ := (Nat.one_le_div_iff (by omega)).mpr hℓt
  have hdiv := Nat.div_add_mod t ℓ
  have hmod := Nat.mod_lt t (by omega : 0 < ℓ)
  have hrest : t - 2 * J * ℓ ≤ 3 * ℓ := by
    have h2J : t / ℓ ≤ 2 * J + 2 := by omega
    have : t < (t / ℓ + 1) * ℓ := by nlinarith
    have : (t / ℓ + 1) * ℓ ≤ (2 * J + 3) * ℓ := Nat.mul_le_mul_right ℓ (by omega)
    have : t < (2 * J + 3) * ℓ := by omega
    have : (2 * J + 3) * ℓ = 2 * J * ℓ + 3 * ℓ := by ring
    omega
  have hsub : B ⊆ P.biUnion (fun k => Finset.Ico (k * ℓ) ((k + 1) * ℓ)) ∪
      Finset.Ico (2 * J * ℓ) t := by
    intro j hj
    have hjt := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hbad := (Finset.mem_filter.mp hj).2
    by_cases hjJ : j < 2 * J * ℓ
    · refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j / ℓ, ?_, ?_⟩)
      · have hk : j / ℓ < 2 * J := (Nat.div_lt_iff_lt_mul (by omega)).mpr hjJ
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, ?_⟩
        exact present_of_endPorous (Nat.div_mul_le_self j ℓ)
          (by have := Nat.lt_div_mul_add (a := j) (by omega : 0 < ℓ); nlinarith) hjt.le hbad
      · rw [Finset.mem_Ico]
        exact ⟨Nat.div_mul_le_self j ℓ, by
          have := Nat.lt_div_mul_add (a := j) (by omega : 0 < ℓ); nlinarith⟩
    · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega, hjt⟩)
  have hP : P.card ≤ P0.card + P1.card := by
    have hPsub : P ⊆ P0.image (fun i => 0 + 2 * i) ∪ P1.image (fun i => 1 + 2 * i) := by
      intro k hk
      obtain ⟨hk1, hk2⟩ := Finset.mem_filter.mp hk
      have hk1 := Finset.mem_range.mp hk1
      rcases Nat.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
      · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), ?_⟩, by omega⟩)
        rwa [show 0 + 2 * r = k by omega]
      · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), ?_⟩, by omega⟩)
        rwa [show 1 + 2 * r = k by omega]
    refine (Finset.card_le_card hPsub).trans ((Finset.card_union_le _ _).trans ?_)
    exact add_le_add Finset.card_image_le Finset.card_image_le
  have hU : (P.biUnion fun k => Finset.Ico (k * ℓ) ((k + 1) * ℓ)).card ≤ P.card * ℓ := by
    refine Finset.card_biUnion_le.trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl fun k _ => show (Finset.Ico (k * ℓ) ((k + 1) * ℓ)).card = ℓ by
      rw [Nat.card_Ico]; ring_nf; omega]
    rw [Finset.sum_const, smul_eq_mul]
  calc B.card ≤ (P.biUnion fun k => Finset.Ico (k * ℓ) ((k + 1) * ℓ)).card
          + (Finset.Ico (2 * J * ℓ) t).card :=
        (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    _ ≤ P.card * ℓ + 3 * ℓ := by
        rw [Nat.card_Ico]
        omega
    _ ≤ ℓ * (P0.card + P1.card) + 3 * ℓ := by
        have := Nat.mul_le_mul_right ℓ hP
        nlinarith

open scoped Classical in
/-- **Little time in end-porous boxes.** -/
theorem measureReal_endPorous_le (hd : 1 ≤ d) {m : ℕ} [NeZero m] {δ p₀ : ℝ} (hp₀ : 0 ≤ p₀)
    (hhit : ∀ (z y : Site d), y ∈ boxCell m z → ∀ A : Finset (Site d), A ⊆ boxCell m z →
      δ * (m : ℝ) ^ d ≤ A.card →
        p₀ ≤ (siteWalkLaw d y).real {Y | ∃ j, 1 ≤ j ∧ j ≤ 2 * m ^ 2 ∧ Y j ∈ A})
    {t : ℕ} (hℓt : 2 * m ^ 2 ≤ t) (n : ℕ) (θ : ℝ) :
    (siteWalkLaw d 0).real {X | LatticeProb.rangeCard X t ≤ n ∧
        θ * t ≤ ((Finset.range t).filter fun j => EndPorous m δ X t j).card}
      ≤ 2 * Real.exp (n - (1 - Real.exp (-1)) * p₀
        * ((θ * t - 3 * (2 * m ^ 2 : ℕ)) / (2 * (2 * m ^ 2 : ℕ)))) := by
  have : NeZero d := ⟨by omega⟩
  set ℓ := 2 * m ^ 2 with hℓ
  have hℓ1 : 1 ≤ ℓ := by have := Nat.pos_of_neZero m; rw [hℓ]; nlinarith
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
  set J := (t / ℓ - 1) / 2 with hJ
  set N : ℝ := (θ * t - 3 * ℓ) / (2 * ℓ) with hN
  let E : ℕ → Set (ℕ → Site d) := fun π => {X | N ≤ ((Finset.range J).filter fun i =>
        Present m δ ℓ (π + 2 * i) X).card ∧
      (((Finset.range J).filter fun i => Success m δ ℓ (π + 2 * i) X).card : ℝ) ≤ n}
  have htl : 1 ≤ t / ℓ := (Nat.one_le_div_iff (by omega)).mpr hℓt
  have hJt : ∀ π ≤ 1, (π + 2 * J) * ℓ ≤ t := by
    intro π hπ
    have h1 : π + 2 * J ≤ t / ℓ := by omega
    exact le_trans (Nat.mul_le_mul_right ℓ h1) (Nat.div_mul_le_self t ℓ)
  have hsub : {X : ℕ → Site d | LatticeProb.rangeCard X t ≤ n ∧
      θ * t ≤ ((Finset.range t).filter fun j => EndPorous m δ X t j).card} ⊆ E 0 ∪ E 1 := by
    intro X ⟨hR, hB⟩
    have hcount := card_endPorous_le (m := m) (δ := δ) hℓ1 hℓt X
    have hS : ∀ π ≤ 1, (((Finset.range J).filter fun i => Success m δ ℓ (π + 2 * i) X).card : ℝ)
        ≤ n := by
      intro π hπ
      have := card_success_le m δ π J t (hJt π hπ) X
      rw [card_rangeSet] at this
      exact_mod_cast this.trans hR
    have hsum : 2 * N ≤ (((Finset.range J).filter fun i => Present m δ ℓ (0 + 2 * i) X).card : ℝ)
        + ((Finset.range J).filter fun i => Present m δ ℓ (1 + 2 * i) X).card := by
      have h1 : (((Finset.range t).filter fun j => EndPorous m δ X t j).card : ℝ)
          ≤ ℓ * ((((Finset.range J).filter fun i => Present m δ ℓ (0 + 2 * i) X).card : ℝ)
            + ((Finset.range J).filter fun i => Present m δ ℓ (1 + 2 * i) X).card) + 3 * ℓ := by
        exact_mod_cast hcount
      rw [hN, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    by_cases h0 : N ≤ (((Finset.range J).filter fun i => Present m δ ℓ (0 + 2 * i) X).card : ℝ)
    · exact Or.inl ⟨h0, hS 0 (by norm_num)⟩
    · refine Or.inr ⟨by linarith, hS 1 le_rfl⟩
  have hE : ∀ π, (siteWalkLaw d 0).real (E π) ≤ Real.exp (n - (1 - Real.exp (-1)) * p₀ * N) :=
    fun π => measureReal_present_success_le hd hp₀ hℓ hhit π J N n
  calc (siteWalkLaw d 0).real {X : ℕ → Site d | LatticeProb.rangeCard X t ≤ n ∧
        θ * t ≤ ((Finset.range t).filter fun j => EndPorous m δ X t j).card}
      ≤ (siteWalkLaw d 0).real (E 0 ∪ E 1) := measureReal_mono hsub
    _ ≤ (siteWalkLaw d 0).real (E 0) + (siteWalkLaw d 0).real (E 1) := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (n - (1 - Real.exp (-1)) * p₀ * N) := by linarith [hE 0, hE 1]
    _ = _ := by rw [hN]

end Parking

end
