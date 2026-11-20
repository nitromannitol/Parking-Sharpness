import Parking.Support.DVBlowup

/-!
# Scaling of the least Dirichlet ratio

Interpolating a function `h` vanishing off `V` in all `d` coordinates at scale `L`
(`Parking.blowList`) gives a function vanishing off the union of the `L`-cells over the cube
hull of `V`.  Its mass is at least `L^d (‖h‖² - 2d E(h))` and its energy at most
`L^{d-2} E(h)`, and the cube hull of its support has at most
`L^d |fatten V| + d L^{d-1} |fatten (fatten V)|` sites: a site of the hull of the fine support
lies in a cell over `fatten V`, unless one of its residues is `L - 1`, which happens for
`d L^{d-1}` residues per cell.  Hence (`dirichletRate_blowup`)

  `L^2 · dirichletRate d n · (‖h‖² - 2d E(h)) ≤ E(h)`,  `n ≥ L^d |fatten V| + d L^{d-1} |fatten (fatten V)|`.
-/

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-! ### Splitting every coordinate modulo `L` -/

/-- `y ↦ (⌊y / L⌋, y mod L)`, coordinatewise. -/
def fullSplit (L : ℕ) [NeZero L] : Site d ≃ Site d × (Fin d → Fin L) where
  toFun y := (fun j => (Int.divModEquiv L (y j)).1, fun j => (Int.divModEquiv L (y j)).2)
  invFun p := fun j => (Int.divModEquiv L).symm (p.1 j, p.2 j)
  left_inv y := by
    funext j
    simp only [Prod.mk.eta, Equiv.symm_apply_apply]
  right_inv p := by
    obtain ⟨x, s⟩ := p
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
    · simp only [Equiv.apply_symm_apply]
    · simp only [Equiv.apply_symm_apply]

theorem fullSplit_symm_apply (L : ℕ) [NeZero L] (x : Site d) (s : Fin d → Fin L) :
    (fullSplit L).symm (x, s) = fun j => x j * L + ((s j : ℕ) : ℤ) := by
  funext j
  simp [fullSplit]

theorem fullSplit_fst (L : ℕ) [NeZero L] (y : Site d) :
    (fullSplit L y).1 = fun j => y j / (L : ℤ) := by
  funext j
  simp [fullSplit]

theorem coarseIn_finRange (L : ℕ) [NeZero L] (y : Site d) :
    coarseIn L (List.finRange d) y = (fullSplit L y).1 := by
  rw [fullSplit_fst]
  funext j
  simp [coarseIn]

theorem sum_unit_apply (S : Finset (Fin d)) (k : Fin d) :
    (∑ j ∈ S, unit j) k = if k ∈ S then 1 else 0 := by
  classical
  rw [Finset.sum_apply]
  simp only [unit, Pi.single_apply]
  rw [Finset.sum_ite_eq]

/-- Moving by `∑_{j ∈ S} e_j` moves the coarse point by the coordinates of `S` whose residue
wraps around. -/
theorem fullSplit_fst_add_sum_unit (L : ℕ) [NeZero L] (x : Site d) (s : Fin d → Fin L)
    (S : Finset (Fin d)) :
    (fullSplit L ((fullSplit L).symm (x, s) + ∑ j ∈ S, unit j)).1
      = x + ∑ j ∈ S.filter (fun j => (s j : ℕ) + 1 = L), unit j := by
  classical
  have hL : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_neZero L
  rw [fullSplit_fst]
  funext k
  simp only [Pi.add_apply, fullSplit_symm_apply, sum_unit_apply, Finset.mem_filter]
  have hs := (s k).isLt
  by_cases hk : k ∈ S
  · by_cases hw : (s k : ℕ) + 1 = L
    · rw [ite_eq_left hk, ite_eq_left ⟨hk, hw⟩]
      have : x k * L + ((s k : ℕ) : ℤ) + 1 = (x k + 1) * L := by
        have : ((s k : ℕ) : ℤ) + 1 = L := by exact_mod_cast hw
        linear_combination this
      rw [this, Int.mul_ediv_cancel _ hL.ne']
    · rw [ite_eq_left hk, ite_eq_right fun h => hw h.2, add_zero, add_assoc,
        Int.add_comm (x k * L), Int.add_mul_ediv_right _ _ hL.ne',
        Int.ediv_eq_zero_of_lt (by positivity) (by omega), zero_add]
  · rw [ite_eq_right hk, ite_eq_right fun h => hk h.1, add_zero, add_zero, Int.add_comm (x k * L),
      Int.add_mul_ediv_right _ _ hL.ne', Int.ediv_eq_zero_of_lt (by positivity) (by omega),
      zero_add]

/-- The residues with some coordinate equal to `L - 1`. -/
def wrapResidues (d L : ℕ) : Finset (Fin d → Fin L) :=
  Finset.univ.filter fun s => ∃ j, (s j : ℕ) + 1 = L

theorem card_wrapResidues_le (L : ℕ) [NeZero L] : (wrapResidues d L).card ≤ d * L ^ (d - 1) := by
  classical
  have hL := Nat.pos_of_neZero L
  set last : Fin L := ⟨L - 1, by omega⟩
  have hsub : wrapResidues d L ⊆ Finset.univ.biUnion fun j : Fin d =>
      Finset.univ.filter fun s : Fin d → Fin L => s j = last := by
    intro s hs
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hs).2
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Fin.ext (by simp [last]; omega)⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  have hj : ∀ j : Fin d, (Finset.univ.filter fun s : Fin d → Fin L => s j = last).card
      = L ^ (d - 1) := by
    intro j
    have := Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset (Fin L)) j
      (Finset.mem_univ last)
    simpa [Fintype.piFinset_univ, Finset.card_univ, Fintype.card_fin] using this
  simp [hj]

/-- The cells over `A`. -/
def cellsOver (L : ℕ) [NeZero L] (A : Finset (Site d)) : Finset (Site d) :=
  (A ×ˢ (Finset.univ : Finset (Fin d → Fin L))).image (fullSplit L).symm

theorem mem_cellsOver {L : ℕ} [NeZero L] {A : Finset (Site d)} {y : Site d} :
    y ∈ cellsOver L A ↔ (fullSplit L y).1 ∈ A := by
  classical
  constructor
  · intro hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    rw [Equiv.apply_symm_apply]
    exact (Finset.mem_product.mp hp).1
  · intro hy
    exact Finset.mem_image.mpr ⟨fullSplit L y, Finset.mem_product.mpr ⟨hy, Finset.mem_univ _⟩,
      Equiv.symm_apply_apply _ _⟩

/-- **The cube hull of the cells over `fatten V`.** -/
theorem card_fatten_cellsOver_le (L : ℕ) [NeZero L] (V : Finset (Site d)) :
    (fatten (cellsOver L (fatten V))).card
      ≤ L ^ d * (fatten V).card + d * L ^ (d - 1) * (fatten (fatten V)).card := by
  classical
  have hsub : fatten (cellsOver L (fatten V)) ⊆
      ((fatten V ×ˢ (Finset.univ : Finset (Fin d → Fin L)))
        ∪ (fatten (fatten V) ×ˢ wrapResidues d L)).image (fullSplit L).symm := by
    intro y hy
    obtain ⟨S, hS⟩ := mem_fatten.mp hy
    rw [mem_cellsOver] at hS
    set p := fullSplit L y with hp
    have hy' : y = (fullSplit L).symm (p.1, p.2) := by rw [hp]; simp
    rw [hy', fullSplit_fst_add_sum_unit] at hS
    refine Finset.mem_image.mpr ⟨p, ?_, by rw [hy']⟩
    by_cases hw : (S.filter fun j => (p.2 j : ℕ) + 1 = L) = ∅
    · rw [hw, Finset.sum_empty, add_zero] at hS
      exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨hS, Finset.mem_univ _⟩)
    · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hw
      refine Finset.mem_union_right _ (Finset.mem_product.mpr ⟨mem_fatten.mpr ⟨_, hS⟩, ?_⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, (Finset.mem_filter.mp hj).2⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  refine (Finset.card_union_le _ _).trans ?_
  rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]
  have := card_wrapResidues_le (d := d) L
  nlinarith [Nat.zero_le (fatten (fatten V)).card]

/-! ### The blow-up of the least Dirichlet ratio -/

/-- **Scaling of the least Dirichlet ratio.**  A function `h` vanishing off `V` with
`2d E(h) < ‖h‖²`, blown up at scale `L`, gives
`L^2 · dirichletRate d n · (‖h‖² - 2d E(h)) ≤ E(h)` for every `n` at least
`L^d |fatten V| + d L^{d-1} |fatten (fatten V)|`. -/
theorem dirichletRate_blowup (hd : 1 ≤ d) (L : ℕ) [NeZero L] {V : Finset (Site d)}
    {h : Site d → ℝ} (hV : ∀ x ∉ V, h x = 0) (hsmall : 2 * d * latEnergy h < sqMass h) {n : ℕ}
    (hn : L ^ d * (fatten V).card + d * L ^ (d - 1) * (fatten (fatten V)).card ≤ n) :
    (L : ℝ) ^ 2 * dirichletRate d n * (sqMass h - 2 * d * latEnergy h) ≤ latEnergy h := by
  classical
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_neZero L
  have hd0 : (0 : ℝ) < 2 * d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hh : FinSupp h := ⟨V, hV⟩
  set g := blowList L (List.finRange d) h with hg
  have hnd : (List.finRange d).Nodup := List.nodup_finRange d
  have hsumD : ((List.finRange d).map fun i => dirEnergy i h).sum = 2 * d * latEnergy h := by
    rw [← Fin.sum_univ_def, latEnergy]
    field_simp
  have hmass : (L : ℝ) ^ d * (sqMass h - 2 * d * latEnergy h) ≤ sqMass g := by
    have := sqMass_blowList_ge L hh (List.finRange d) hnd
    rwa [List.length_finRange, hsumD] at this
  have hpos : 0 < sqMass h - 2 * d * latEnergy h := by linarith
  have hgpos : 0 < sqMass g := lt_of_lt_of_le (by positivity) hmass
  have henergy : (L : ℝ) ^ 2 * latEnergy g ≤ (L : ℝ) ^ d * latEnergy h := by
    have hj : ∀ j : Fin d, (L : ℝ) ^ 2 * dirEnergy j g ≤ (L : ℝ) ^ d * dirEnergy j h := by
      intro j
      have := dirEnergy_blowList_le L hh (List.finRange d) hnd j
      rwa [ite_eq_left (List.mem_finRange j), List.length_finRange] at this
    unfold latEnergy
    rw [mul_div_assoc', mul_div_assoc', Finset.mul_sum, Finset.mul_sum]
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun j _ => hj j) hd0.le
  have hsupp : ∀ y ∉ cellsOver L (fatten V), g y = 0 := by
    intro y hy
    by_contra hne
    obtain ⟨S, -, hS⟩ := exists_ne_zero_of_blowList_ne_zero L h (List.finRange d) hnd y hne
    apply hy
    rw [mem_cellsOver, ← coarseIn_finRange]
    exact mem_fatten.mpr ⟨S, by_contra fun hn => hS (hV _ hn)⟩
  have hrate := dirichletRate_le ((card_fatten_cellsOver_le L V).trans hn) hsupp hgpos
  have hrate0 := dirichletRate_nonneg d n
  set ρ := dirichletRate d n
  rw [le_div_iff₀ hgpos] at hrate
  have hLd : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  have h1 : (L : ℝ) ^ 2 * ρ * ((L : ℝ) ^ d * (sqMass h - 2 * d * latEnergy h))
      ≤ (L : ℝ) ^ 2 * (ρ * sqMass g) :=
    by nlinarith [mul_le_mul_of_nonneg_left hmass (mul_nonneg (sq_nonneg (L : ℝ)) hrate0)]
  have h2 : (L : ℝ) ^ 2 * (ρ * sqMass g) ≤ (L : ℝ) ^ d * latEnergy h := by nlinarith
  have h3 : (L : ℝ) ^ d * ((L : ℝ) ^ 2 * ρ * (sqMass h - 2 * d * latEnergy h))
      ≤ (L : ℝ) ^ d * latEnergy h := by nlinarith
  exact le_of_mul_le_mul_left h3 hLd

end Parking

end
