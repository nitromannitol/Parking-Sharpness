import Parking.Support.DVEnergy

/-!
# Soft killing and the least Dirichlet ratio

A killing rate `κ` outside a finite set `U` is almost as good as a wall at the boundary of
`U`, once `κ` is large compared with the Dirichlet ratio.  Precisely, let `g ≥ 0` have unit
mass and

  `latEnergy g + κ ∑_{x ∉ U} g(x)^2 ≤ λ`.

Truncating at a level `s > 0`, `h = (g - s)⁺` vanishes off `W = {g > s}`, whose part outside
`U` has at most `λ / (κ s^2)` sites, and

  `‖h‖² ≥ 1 - 2s √(|U| + λ/(κ s^2)) - s^2 |U| - λ/κ`,

while `latEnergy h ≤ latEnergy g ≤ λ`.  Hence (`dirichletRate_mul_le_of_soft`)

  `dirichletRate d N · (1 - 2s √(|U| + λ/(κ s^2)) - s^2 |U| - λ/κ) ≤ λ`

for every `N ≥ |fatten U| + 2^d λ/(κ s^2)`.  This is the step that replaces the enlargement of
obstacles in the upper bound for the range: the walk pays the killing rate `κ` outside the
boxes its range fills, and the inequality turns that soft killing into the Dirichlet ratio of
a region barely larger than those boxes.
-/

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- `∑_{x ∉ U} g(x)^2`. -/
def massOff (U : Finset (Site d)) (g : Site d → ℝ) : ℝ :=
  ∑' x, if x ∈ U then 0 else g x ^ 2

theorem massOff_nonneg (U : Finset (Site d)) (g : Site d → ℝ) : 0 ≤ massOff U g :=
  tsum_nonneg fun x => by split_ifs <;> positivity

theorem fatten_union (A B : Finset (Site d)) : fatten (A ∪ B) = fatten A ∪ fatten B := by
  classical
  ext x
  simp only [Finset.mem_union, mem_fatten]
  constructor
  · rintro ⟨S, hS | hS⟩
    · exact Or.inl ⟨S, hS⟩
    · exact Or.inr ⟨S, hS⟩
  · rintro (⟨S, hS⟩ | ⟨S, hS⟩)
    · exact ⟨S, Or.inl hS⟩
    · exact ⟨S, Or.inr hS⟩

/-- **The soft-killing Faber-Krahn step.** -/
theorem dirichletRate_mul_le_of_soft {U : Finset (Site d)} {g : Site d → ℝ} (hgfs : FinSupp g)
    (hg0 : ∀ x, 0 ≤ g x) (hM : sqMass g = 1) {κ lam s : ℝ} (hκ : 0 < κ) (hs : 0 < s)
    (hE : latEnergy g + κ * massOff U g ≤ lam) {N : ℕ}
    (hN : ((fatten U).card : ℝ) + 2 ^ d * (lam / (κ * s ^ 2)) ≤ N)
    (herr : 2 * s * Real.sqrt (U.card + lam / (κ * s ^ 2)) + s ^ 2 * U.card + lam / κ < 1) :
    dirichletRate d N
        * (1 - (2 * s * Real.sqrt (U.card + lam / (κ * s ^ 2)) + s ^ 2 * U.card + lam / κ))
      ≤ lam := by
  classical
  obtain ⟨V, hV⟩ := hgfs
  set W : Finset (Site d) := V.filter fun x => s < g x with hW
  set Wout : Finset (Site d) := W.filter fun x => x ∉ U with hWout
  set Mout := massOff U g with hMout
  have hMout0 : 0 ≤ Mout := massOff_nonneg U g
  have hEg : latEnergy g ≤ lam := le_trans (le_add_of_nonneg_right
    (mul_nonneg hκ.le hMout0)) hE
  have hκMout : κ * Mout ≤ lam := le_trans (le_add_of_nonneg_left (latEnergy_nonneg g)) hE
  have hMoutle : Mout ≤ lam / κ := by rw [le_div_iff₀ hκ]; linarith
  have hlam0 : 0 ≤ lam := le_trans (latEnergy_nonneg g) hEg
  -- `Mout` as a finite sum
  have hMoutV : Mout = ∑ x ∈ V, if x ∈ U then 0 else g x ^ 2 :=
    tsum_eq_sum fun x hx => by rw [hV x hx]; simp
  have hMV : ∑ x ∈ V, g x ^ 2 = 1 := by rw [← sqMass_eq_sum hV, hM]
  -- the part of `W` outside `U` is small
  have hWout : (Wout.card : ℝ) * s ^ 2 ≤ Mout := by
    rw [hMoutV]
    calc (Wout.card : ℝ) * s ^ 2 = ∑ x ∈ Wout, s ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ Wout, (if x ∈ U then 0 else g x ^ 2) := by
          refine Finset.sum_le_sum fun x hx => ?_
          have hx' := Finset.mem_filter.mp hx
          have hxW := Finset.mem_filter.mp hx'.1
          rw [ite_eq_right hx'.2]
          exact pow_le_pow_left₀ hs.le hxW.2.le 2
      _ ≤ ∑ x ∈ V, (if x ∈ U then 0 else g x ^ 2) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (fun x hx => (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1) fun x _ _ => ?_
          split_ifs <;> positivity
  have hWoutle : (Wout.card : ℝ) ≤ lam / (κ * s ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    calc (Wout.card : ℝ) * (κ * s ^ 2) = κ * ((Wout.card : ℝ) * s ^ 2) := by ring
      _ ≤ κ * Mout := mul_le_mul_of_nonneg_left hWout hκ.le
      _ ≤ lam := hκMout
  have hWsub : W ⊆ U ∪ Wout := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Finset.mem_union_left _ hxU
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, hxU⟩)
  have hWcard : (W.card : ℝ) ≤ U.card + lam / (κ * s ^ 2) := by
    have := Finset.card_le_card hWsub
    have h2 := Finset.card_union_le U Wout
    have : (W.card : ℝ) ≤ U.card + Wout.card := by exact_mod_cast this.trans h2
    linarith
  -- the cube hull of `W`
  have hfat : ((fatten W).card : ℝ) ≤ N := by
    have h1 : fatten W ⊆ fatten U ∪ fatten Wout := by
      rw [← fatten_union]
      exact fatten_mono hWsub
    have h2 : ((fatten W).card : ℝ) ≤ (fatten U).card + 2 ^ d * Wout.card := by
      have := (Finset.card_le_card h1).trans (Finset.card_union_le _ _)
      have h3 := card_fatten_le (d := d) Wout
      have : (fatten W).card ≤ (fatten U).card + 2 ^ d * Wout.card := by omega
      exact_mod_cast this
    have h4 : (2 : ℝ) ^ d * Wout.card ≤ 2 ^ d * (lam / (κ * s ^ 2)) :=
      mul_le_mul_of_nonneg_left hWoutle (by positivity)
    linarith
  -- the truncation
  set h : Site d → ℝ := fun x => max (g x - s) 0 with hh
  have hhW : ∀ x ∉ W, h x = 0 := by
    intro x hx
    by_cases hxV : x ∈ V
    · have : ¬ s < g x := fun h' => hx (Finset.mem_filter.mpr ⟨hxV, h'⟩)
      simp only [hh]
      exact max_eq_right (by linarith)
    · simp only [hh, hV x hxV]
      exact max_eq_right (by linarith)
  have hEh : latEnergy h ≤ lam := (latEnergy_posPart_le ⟨V, hV⟩ hs.le).trans hEg
  -- the mass of the truncation
  have hpt : ∀ x ∈ V, g x ^ 2 - 2 * s * (if s < g x then g x else 0)
      - (if x ∈ U then s ^ 2 else (if x ∈ U then 0 else g x ^ 2)) ≤ h x ^ 2 := by
    intro x _
    have hgx := hg0 x
    by_cases hsg : s < g x
    · rw [ite_eq_left hsg]
      have : h x = g x - s := by simp only [hh]; exact max_eq_left (by linarith)
      rw [this]
      split_ifs <;> nlinarith
    · rw [ite_eq_right hsg]
      have : h x = 0 := by simp only [hh]; exact max_eq_right (by linarith)
      rw [this]
      push Not at hsg
      split_ifs <;> nlinarith
  have hmassV : sqMass h = ∑ x ∈ V, h x ^ 2 := sqMass_eq_sum fun x hx => by
    by_cases hxW : x ∈ W
    · exact absurd (Finset.mem_filter.mp hxW).1 hx
    · rw [hhW x hxW]
  have hsumW : ∑ x ∈ V, (if s < g x then g x else 0) = ∑ x ∈ W, g x := by
    rw [hW, Finset.sum_filter]
  have hsumU : ∑ x ∈ V, (if x ∈ U then s ^ 2 else (if x ∈ U then 0 else g x ^ 2))
      ≤ s ^ 2 * U.card + Mout := by
    rw [hMoutV]
    have hsplit : ∀ x ∈ V, (if x ∈ U then s ^ 2 else (if x ∈ U then 0 else g x ^ 2))
        = (if x ∈ U then s ^ 2 else 0) + (if x ∈ U then 0 else g x ^ 2) := by
      intro x _; split_ifs <;> simp
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    have : ∑ x ∈ V, (if x ∈ U then s ^ 2 else 0) ≤ s ^ 2 * U.card := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      have hc : (V.filter fun x => x ∈ U).card ≤ U.card :=
        Finset.card_le_card fun x hx => (Finset.mem_filter.mp hx).2
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hc) (sq_nonneg s)
    linarith
  have hCS : (∑ x ∈ W, g x) ≤ Real.sqrt (U.card + lam / (κ * s ^ 2)) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq W (fun _ => (1 : ℝ)) g
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
    have hW2 : ∑ x ∈ W, g x ^ 2 ≤ 1 := by
      rw [← hMV]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun x _ _ => sq_nonneg _
    have hS0 : 0 ≤ ∑ x ∈ W, g x := Finset.sum_nonneg fun x _ => hg0 x
    rw [← Real.sqrt_sq hS0]
    refine Real.sqrt_le_sqrt ?_
    calc (∑ x ∈ W, g x) ^ 2 ≤ W.card * ∑ x ∈ W, g x ^ 2 := hcs
      _ ≤ W.card * 1 := mul_le_mul_of_nonneg_left hW2 (Nat.cast_nonneg _)
      _ ≤ U.card + lam / (κ * s ^ 2) := by rw [mul_one]; exact hWcard
  have hmass : 1 - (2 * s * Real.sqrt (U.card + lam / (κ * s ^ 2)) + s ^ 2 * U.card + lam / κ)
      ≤ sqMass h := by
    rw [hmassV]
    have h1 := Finset.sum_le_sum hpt
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hMV, ← Finset.mul_sum, hsumW] at h1
    have h2 : 2 * s * ∑ x ∈ W, g x ≤ 2 * s * Real.sqrt (U.card + lam / (κ * s ^ 2)) :=
      mul_le_mul_of_nonneg_left hCS (by positivity)
    linarith
  have hpos : 0 < sqMass h := lt_of_lt_of_le (by linarith) hmass
  have hrate := dirichletRate_le (by exact_mod_cast hfat) hhW hpos
  have hρ0 := dirichletRate_nonneg d N
  calc dirichletRate d N
        * (1 - (2 * s * Real.sqrt (U.card + lam / (κ * s ^ 2)) + s ^ 2 * U.card + lam / κ))
      ≤ dirichletRate d N * sqMass h := mul_le_mul_of_nonneg_left hmass hρ0
    _ ≤ latEnergy h / sqMass h * sqMass h := mul_le_mul_of_nonneg_right hrate hpos.le
    _ = latEnergy h := div_mul_cancel₀ _ hpos.ne'
    _ ≤ lam := hEh

end Parking

end
