import Parking.Support.DVBadTime
import Parking.Support.DVFeynmanKac

/-!
# The upper bound for the probability of a small range

On the event `|R_t| ≤ n`, call a box of side `m` full if the range covers at least
`(1 - δ) m^d` of its sites.  Off an event of probability at most
`2 e^{n - q (θ t - 3ℓ)/(2ℓ)}` (`Parking.measureReal_endPorous_le`), the walk spends less than
`θ t` units of time outside the union `U` of the full boxes.  There are at most
`K₀ = ⌊n / ((1 - δ) m^d)⌋` full boxes, all with coarse index in the box of radius `t`, so `U`
ranges over at most `(K₀ + 1) (2t + 1)^{d K₀}` sets, each of volume at most `n / (1 - δ)`
and with a cube hull of at most `K₀ (m + 1)^d` sites.  For each of them the soft-killing
bound of `Parking.Support.DVFeynmanKac` applies (`measureReal_rangeCard_le`).
-/

noncomputable section

namespace Parking

open LatticeProb MeasureTheory

variable {d : ℕ}

/-! ### The cube hull of a union of boxes -/

/-- The box `z m - 1 + [0, m]^d`, which contains the cube hull of the box of index `z`. -/
def hullBox (m : ℕ) (z : Site d) : Finset (Site d) :=
  (Finset.univ : Finset (Fin d → Fin (m + 1))).image fun s i => z i * m - 1 + (s i : ℕ)

theorem card_hullBox_le (m : ℕ) (z : Site d) : (hullBox m z).card ≤ (m + 1) ^ d := by
  refine Finset.card_image_le.trans (le_of_eq ?_)
  simp [Finset.card_univ, Fintype.card_fin]

theorem fatten_cellsOver_subset (m : ℕ) [NeZero m] (F : Finset (Site d)) :
    fatten (cellsOver m F) ⊆ F.biUnion (hullBox m) := by
  classical
  intro x hx
  obtain ⟨S, hS⟩ := mem_fatten.mp hx
  rw [mem_cellsOver, fullSplit_fst] at hS
  set z : Site d := fun i => (x + ∑ j ∈ S, unit j) i / (m : ℤ) with hz
  have hm : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_neZero m
  refine Finset.mem_biUnion.mpr ⟨z, hS, Finset.mem_image.mpr ⟨fun i => ⟨(x i - (z i * m - 1)).toNat,
    ?_⟩, Finset.mem_univ _, ?_⟩⟩
  · have h1 := Int.ediv_mul_le ((x + ∑ j ∈ S, unit j) i) hm.ne'
    have h2 := Int.lt_ediv_add_one_mul_self ((x + ∑ j ∈ S, unit j) i) hm
    rw [Pi.add_apply, sum_unit_apply] at h1 h2
    have hzi : z i = (x i + (if i ∈ S then 1 else 0)) / (m : ℤ) := by
      rw [hz]; simp only [Pi.add_apply, sum_unit_apply]
    rw [← hzi] at h1 h2
    have hexp : (z i + 1) * (m : ℤ) = z i * m + m := by ring
    rw [hexp] at h2
    split_ifs at h1 h2 <;> omega
  · funext i
    have h1 := Int.ediv_mul_le ((x + ∑ j ∈ S, unit j) i) hm.ne'
    rw [Pi.add_apply, sum_unit_apply] at h1
    have hzi : z i = (x i + (if i ∈ S then 1 else 0)) / (m : ℤ) := by
      rw [hz]; simp only [Pi.add_apply, sum_unit_apply]
    rw [← hzi] at h1
    have h0 : 0 ≤ x i - (z i * m - 1) := by split_ifs at h1 <;> omega
    simp only
    rw [Int.toNat_of_nonneg h0]
    ring

theorem card_fatten_cellsOver_le' (m : ℕ) [NeZero m] (F : Finset (Site d)) :
    (fatten (cellsOver m F)).card ≤ F.card * (m + 1) ^ d :=
  (Finset.card_le_card (fatten_cellsOver_subset m F)).trans
    (Finset.card_biUnion_le.trans (by
      simpa using Finset.sum_le_sum fun z (_ : z ∈ F) => card_hullBox_le (d := d) m z))

theorem card_cellsOver (m : ℕ) [NeZero m] (F : Finset (Site d)) :
    (cellsOver m F).card = F.card * m ^ d := by
  classical
  rw [cellsOver, Finset.card_image_of_injective _ (fullSplit m).symm.injective,
    Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-! ### The number of candidate sets of full boxes -/

/-- The sets of at most `K` boxes with index in the box of radius `t`. -/
def boxFamilies (t K : ℕ) : Finset (Finset (Site d)) :=
  (Finset.range (K + 1)).biUnion fun k => (boxFinset (0 : Site d) t).powersetCard k

theorem mem_boxFamilies {t K : ℕ} {F : Finset (Site d)} (hF : F ⊆ boxFinset 0 t)
    (hK : F.card ≤ K) : F ∈ boxFamilies t K :=
  Finset.mem_biUnion.mpr ⟨F.card, Finset.mem_range.mpr (by omega),
    Finset.mem_powersetCard.mpr ⟨hF, rfl⟩⟩

theorem card_boxFamilies_le (t K : ℕ) :
    (boxFamilies (d := d) t K).card ≤ (K + 1) * ((2 * t + 1) ^ d) ^ K := by
  refine Finset.card_biUnion_le.trans ?_
  have hZ : (boxFinset (0 : Site d) t).card = (2 * t + 1) ^ d := card_boxFinset_zero t
  have h1 : 1 ≤ (2 * t + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  calc ∑ k ∈ Finset.range (K + 1), ((boxFinset (0 : Site d) t).powersetCard k).card
      ≤ ∑ _k ∈ Finset.range (K + 1), ((2 * t + 1) ^ d) ^ K := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [Finset.card_powersetCard, hZ]
        exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_right h1
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
    _ = (K + 1) * ((2 * t + 1) ^ d) ^ K := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-! ### The full boxes -/

open scoped Classical in
/-- The boxes with index in the box of radius `t` whose sites the range up to time `t` covers
in at least `(1 - δ) m^d` places. -/
def fullBoxes (m : ℕ) [NeZero m] (δ : ℝ) (t : ℕ) (X : ℕ → Site d) : Finset (Site d) :=
  (boxFinset 0 t).filter fun z => (1 - δ) * (m : ℝ) ^ d ≤ ((boxCell m z ∩ rangeSet X t).card : ℝ)

theorem boxCell_disjoint {m : ℕ} [NeZero m] {z z' : Site d} (h : z ≠ z') :
    Disjoint (boxCell m z) (boxCell m z') :=
  Finset.disjoint_left.mpr fun _ hy hy' => h ((mem_boxCell.mp hy).symm.trans (mem_boxCell.mp hy'))

/-- The full boxes are at most `|R_t| / ((1 - δ) m^d)`. -/
theorem card_fullBoxes_mul_le {m : ℕ} [NeZero m] {δ : ℝ} (t : ℕ) (X : ℕ → Site d) :
    ((fullBoxes m δ t X).card : ℝ) * ((1 - δ) * (m : ℝ) ^ d) ≤ (rangeSet X t).card := by
  classical
  set F := fullBoxes m δ t X
  have hdisj : (F : Set (Site d)).PairwiseDisjoint fun z => boxCell m z ∩ rangeSet X t :=
    fun z _ z' _ hzz' => Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left (boxCell_disjoint hzz'))
  have hsub : F.biUnion (fun z => boxCell m z ∩ rangeSet X t) ⊆ rangeSet X t :=
    Finset.biUnion_subset.mpr fun z _ => Finset.inter_subset_right
  have h1 : (∑ z ∈ F, ((boxCell m z ∩ rangeSet X t).card : ℝ)) ≤ (rangeSet X t).card := by
    have := Finset.card_le_card hsub
    rw [Finset.card_biUnion hdisj] at this
    exact_mod_cast this
  have h2 : ((F.card : ℝ) * ((1 - δ) * (m : ℝ) ^ d))
      ≤ ∑ z ∈ F, ((boxCell m z ∩ rangeSet X t).card : ℝ) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun z hz => (Finset.mem_filter.mp hz).2
  linarith

/-- On a walk path from the origin, the position at time `j ≤ t` has its box index in the box
of radius `t`. -/
theorem fullSplit_mem_boxFinset {m : ℕ} [NeZero m] {X : ℕ → Site d} (h0 : X 0 = 0)
    (hadj : ∀ k, (lattice d).Adj (X k) (X (k + 1))) {t j : ℕ} (hj : j ≤ t) :
    (fullSplit m (X j)).1 ∈ boxFinset 0 t := by
  have hm : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_neZero m
  have hpos : ∀ k i, |X k i| ≤ k := by
    intro k
    induction k with
    | zero => intro i; simp [h0]
    | succ k ih =>
        intro i
        obtain ⟨a, ha | ha⟩ := Graph.Zd.adj_iff.mp (hadj k)
        · rw [ha]
          have := ih i
          simp only [Pi.add_apply, unit, Pi.single_apply]
          split_ifs <;> push_cast <;> rw [abs_le] at this ⊢ <;> constructor <;> linarith
        · rw [ha]
          have := ih i
          simp only [Pi.sub_apply, unit, Pi.single_apply]
          split_ifs <;> push_cast <;> rw [abs_le] at this ⊢ <;> constructor <;> linarith
  rw [mem_boxFinset_iff, fullSplit_fst]
  intro i
  simp only [Pi.zero_apply, sub_zero]
  have h := hpos j i
  have h1 := Int.ediv_mul_le (X j i) hm.ne'
  have h2 := Int.lt_ediv_add_one_mul_self (X j i) hm
  have hjt : (j : ℤ) ≤ t := by exact_mod_cast hj
  rw [abs_le] at h ⊢
  constructor
  · by_contra hc
    push Not at hc
    have : (X j i / m + 1) * (m : ℤ) ≤ (-(t : ℤ)) * m := by
      have : X j i / m + 1 ≤ -(t : ℤ) := by omega
      exact Int.mul_le_mul_of_nonneg_right this hm.le
    have : (-(t : ℤ)) * m ≤ -(t : ℤ) := by nlinarith
    linarith
  · by_contra hc
    push Not at hc
    have : ((t : ℤ) + 1) * m ≤ X j i / m * m := Int.mul_le_mul_of_nonneg_right (by omega) hm.le
    nlinarith

/-! ### The bound -/

/-- The error term of the soft-killing step, for a set of volume `U`. -/
def softErr (U lam κ s : ℝ) : ℝ :=
  2 * s * Real.sqrt (U + lam / ((1 - lam) * κ * s ^ 2)) + s ^ 2 * U + lam / ((1 - lam) * κ)

theorem softErr_nonneg {U lam κ s : ℝ} (hU : 0 ≤ U) (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (hκ : 0 < κ) (hs : 0 < s) : 0 ≤ softErr U lam κ s := by
  unfold softErr
  have : 0 < 1 - lam := by linarith
  positivity

theorem softErr_mono {U U' lam κ s : ℝ} (hUU' : U ≤ U') (hs : 0 < s) :
    softErr U lam κ s ≤ softErr U' lam κ s := by
  unfold softErr
  have h1 := Real.sqrt_le_sqrt (by linarith : U + lam / ((1 - lam) * κ * s ^ 2)
    ≤ U' + lam / ((1 - lam) * κ * s ^ 2))
  have h2 : s ^ 2 * U ≤ s ^ 2 * U' := mul_le_mul_of_nonneg_left hUU' (sq_nonneg s)
  have h3 : 2 * s * Real.sqrt (U + lam / ((1 - lam) * κ * s ^ 2))
      ≤ 2 * s * Real.sqrt (U' + lam / ((1 - lam) * κ * s ^ 2)) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  linarith

/-- The number of full boxes allowed by a range of at most `n` sites. -/
def fullBound (d n m : ℕ) (δ : ℝ) : ℕ := ⌊(n : ℝ) / ((1 - δ) * (m : ℝ) ^ d)⌋₊

open scoped Classical in
theorem outCount_cellsOver_fullBoxes {m : ℕ} [NeZero m] {δ : ℝ} {t : ℕ} {X : ℕ → Site d}
    (h0 : X 0 = 0) (hadj : ∀ k, (lattice d).Adj (X k) (X (k + 1))) :
    outCount (cellsOver m (fullBoxes m δ t X)) X t
      = ((Finset.range t).filter fun j => EndPorous m δ X t j).card := by
  unfold outCount
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjt : j ≤ t := (Finset.mem_range.mp hj).le
  have hbox := fullSplit_mem_boxFinset (m := m) h0 hadj hjt
  have hiff : X j ∈ cellsOver m (fullBoxes m δ t X) ↔ ¬ EndPorous m δ X t j := by
    rw [mem_cellsOver, fullBoxes, Finset.mem_filter, EndPorous, PorousFor, not_lt]
    exact and_iff_right hbox
  by_cases h : EndPorous m δ X t j
  · rw [ite_eq_right (fun hm => (hiff.mp hm) h), ite_eq_left h]
  · rw [ite_eq_left (hiff.mpr h), ite_eq_right h]

open scoped Classical in
/-- **The upper bound for the probability of a small range.** -/
theorem measureReal_rangeCard_le (hd : 1 ≤ d) {m : ℕ} [NeZero m] {δ p₀ κ s θ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hp₀ : 0 ≤ p₀)
    (hhit : ∀ (z y : Site d), y ∈ boxCell m z → ∀ A : Finset (Site d), A ⊆ boxCell m z →
      δ * (m : ℝ) ^ d ≤ A.card →
        p₀ ≤ (siteWalkLaw d y).real {Y | ∃ j, 1 ≤ j ∧ j ≤ 2 * m ^ 2 ∧ Y j ∈ A})
    (hκ : 0 < κ) (hs : 0 < s) {t : ℕ} (hℓt : 2 * m ^ 2 ≤ t) (n N : ℕ)
    (hΛ1 : dirichletRate d N < 1)
    (hN : ((fullBound d n m δ * (m + 1) ^ d : ℕ) : ℝ)
        + 2 ^ d * (dirichletRate d N / ((1 - dirichletRate d N) * κ * s ^ 2)) ≤ N)
    (herr : softErr (n / (1 - δ)) (dirichletRate d N) κ s < 1) :
    (siteWalkLaw d 0).real {X | LatticeProb.rangeCard X t ≤ n}
      ≤ 2 * Real.exp (n - (1 - Real.exp (-1)) * p₀
          * ((θ * t - 3 * (2 * m ^ 2 : ℕ)) / (2 * (2 * m ^ 2 : ℕ))))
        + (((fullBound d n m δ + 1) * ((2 * t + 1) ^ d) ^ fullBound d n m δ : ℕ) : ℝ)
          * (Real.exp (κ * (θ * t)) * ((1 - dirichletRate d N
            * (1 - softErr (n / (1 - δ)) (dirichletRate d N) κ s)) ^ t
              * Real.sqrt (Real.exp κ * (2 * t + 1) ^ d))) := by
  have : NeZero d := ⟨by omega⟩
  set Λ := dirichletRate d N with hΛ
  have hΛ0 : 0 ≤ Λ := dirichletRate_nonneg d N
  set K0 := fullBound d n m δ with hK0
  set err := softErr (n / (1 - δ)) Λ κ s with herrdef
  have hδ' : 0 < 1 - δ := by linarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_neZero m
  have herr0 : 0 ≤ err := softErr_nonneg (by positivity) hΛ0 hΛ1 hκ hs
  set ρ := 1 - Λ * (1 - err) with hρ
  have hρpos : 0 < ρ := by
    have : Λ * (1 - err) ≤ Λ := by nlinarith
    linarith
  set W : Set (ℕ → Site d) := {X | X 0 = 0 ∧ ∀ k, (lattice d).Adj (X k) (X (k + 1))} with hW
  have hWc : (siteWalkLaw d 0).real Wᶜ = 0 := by
    have h := ae_adj_siteWalkLaw (d := d) 0
    rw [ae_iff] at h
    rw [measureReal_def]
    have : Wᶜ = {X : ℕ → Site d | ¬ (X 0 = 0 ∧ ∀ k, (lattice d).Adj (X k) (X (k + 1)))} := by
      ext X; simp [hW]
    rw [this, h, ENNReal.toReal_zero]
  set Ebad : Set (ℕ → Site d) := {X | LatticeProb.rangeCard X t ≤ n ∧
      θ * t ≤ ((Finset.range t).filter fun j => EndPorous m δ X t j).card}
  set G : Finset (Site d) → Set (ℕ → Site d) :=
    fun F => {X | (outCount (cellsOver m F) X t : ℝ) ≤ θ * t}
  -- the inclusion
  have hsub : {X : ℕ → Site d | LatticeProb.rangeCard X t ≤ n}
      ⊆ (Ebad ∪ ⋃ F ∈ boxFamilies (d := d) t K0, G F) ∪ Wᶜ := by
    intro X hX
    by_cases hXW : X ∈ W
    · refine Or.inl ?_
      by_cases hbad : θ * t ≤ ((Finset.range t).filter fun j => EndPorous m δ X t j).card
      · exact Or.inl ⟨hX, hbad⟩
      · refine Or.inr (Set.mem_biUnion (x := fullBoxes m δ t X) ?_ ?_)
        · refine mem_boxFamilies (Finset.filter_subset _ _) ?_
          have h1 := card_fullBoxes_mul_le (m := m) (δ := δ) t X
          rw [card_rangeSet] at h1
          have h2 : (LatticeProb.rangeCard X t : ℝ) ≤ n := by exact_mod_cast hX
          rw [hK0, fullBound]
          refine Nat.le_floor ?_
          rw [le_div_iff₀ (by positivity)]
          linarith
        · show (outCount (cellsOver m (fullBoxes m δ t X)) X t : ℝ) ≤ θ * t
          rw [outCount_cellsOver_fullBoxes hXW.1 hXW.2]
          push Not at hbad
          exact hbad.le
    · exact Or.inr hXW
  -- the bound for each set of boxes
  have hG : ∀ F ∈ boxFamilies (d := d) t K0, (siteWalkLaw d 0).real (G F)
      ≤ Real.exp (κ * (θ * t)) * (ρ ^ t * Real.sqrt (Real.exp κ * (2 * t + 1) ^ d)) := by
    intro F hF
    obtain ⟨k, hk, hFk⟩ := Finset.mem_biUnion.mp hF
    have hFcard : F.card ≤ K0 := by
      rw [(Finset.mem_powersetCard.mp hFk).2]; exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    set U := cellsOver m F with hU
    have hUcard : (U.card : ℝ) ≤ n / (1 - δ) := by
      rw [hU, card_cellsOver]
      have h1 : (K0 : ℝ) ≤ n / ((1 - δ) * (m : ℝ) ^ d) := Nat.floor_le (by positivity)
      have h2 : (F.card : ℝ) ≤ K0 := by exact_mod_cast hFcard
      rw [le_div_iff₀ hδ']
      rw [le_div_iff₀ (by positivity)] at h1
      push_cast
      have h3 : (F.card : ℝ) * ((1 - δ) * (m : ℝ) ^ d) ≤ K0 * ((1 - δ) * (m : ℝ) ^ d) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      calc (F.card : ℝ) * (m : ℝ) ^ d * (1 - δ) = (F.card : ℝ) * ((1 - δ) * (m : ℝ) ^ d) := by
            ring
        _ ≤ n := h3.trans h1
    have hfat : ((fatten U).card : ℝ) + 2 ^ d * (Λ / ((1 - Λ) * κ * s ^ 2)) ≤ N := by
      refine le_trans ?_ hN
      have h1 := card_fatten_cellsOver_le' (d := d) m F
      have h2 : (fatten U).card ≤ K0 * (m + 1) ^ d :=
        h1.trans (Nat.mul_le_mul_right _ hFcard)
      have h3 : ((fatten U).card : ℝ) ≤ ((K0 * (m + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast h2
      linarith
    have herrU : softErr U.card Λ κ s ≤ err :=
      softErr_mono hUcard hs
    have hR0 := rayleigh_symOp_le hd U hκ hs hΛ1 hfat (by
      have := herrU.trans_lt herr
      simpa [softErr] using this)
    have hR : ∀ w : Site d → ℝ, FinSupp w → (∀ x, 0 ≤ w x) →
        ∑' x, w x * symOp U κ w x ≤ ρ * sqMass w := by
      intro w hw hw0
      refine (hR0 w hw hw0).trans (mul_le_mul_of_nonneg_right ?_ (sqMass_nonneg w))
      have : softErr U.card Λ κ s = 2 * s * Real.sqrt (U.card + Λ / ((1 - Λ) * κ * s ^ 2))
          + s ^ 2 * U.card + Λ / ((1 - Λ) * κ) := rfl
      rw [← this]
      nlinarith
    have hfk := fkMean_le hd U hκ.le hρpos hR t
    calc (siteWalkLaw d 0).real (G F) ≤ Real.exp (κ * (θ * t)) * fkMean U κ t 0 :=
          measureReal_outCount_le hd U hκ.le (θ * t) t
      _ ≤ Real.exp (κ * (θ * t)) * (ρ ^ t * Real.sqrt (Real.exp κ * (2 * t + 1) ^ d)) :=
          mul_le_mul_of_nonneg_left hfk (Real.exp_pos _).le
  have hbad := measureReal_endPorous_le hd hp₀ hhit hℓt n θ (δ := δ)
  have hfam := card_boxFamilies_le (d := d) t K0
  calc (siteWalkLaw d 0).real {X : ℕ → Site d | LatticeProb.rangeCard X t ≤ n}
      ≤ (siteWalkLaw d 0).real ((Ebad ∪ ⋃ F ∈ boxFamilies (d := d) t K0, G F) ∪ Wᶜ) :=
        measureReal_mono hsub
    _ ≤ (siteWalkLaw d 0).real (Ebad ∪ ⋃ F ∈ boxFamilies (d := d) t K0, G F)
          + (siteWalkLaw d 0).real Wᶜ := measureReal_union_le _ _
    _ ≤ (siteWalkLaw d 0).real Ebad
          + (siteWalkLaw d 0).real (⋃ F ∈ boxFamilies (d := d) t K0, G F) := by
        rw [hWc, add_zero]; exact measureReal_union_le _ _
    _ ≤ (siteWalkLaw d 0).real Ebad
          + ∑ F ∈ boxFamilies (d := d) t K0, (siteWalkLaw d 0).real (G F) := by
        gcongr; exact measureReal_biUnion_finset_le _ _
    _ ≤ (siteWalkLaw d 0).real Ebad + ∑ _F ∈ boxFamilies (d := d) t K0,
          Real.exp (κ * (θ * t)) * (ρ ^ t * Real.sqrt (Real.exp κ * (2 * t + 1) ^ d)) := by
        gcongr with F hF; exact hG F hF
    _ = (siteWalkLaw d 0).real Ebad + ((boxFamilies (d := d) t K0).card : ℝ) *
          (Real.exp (κ * (θ * t)) * (ρ ^ t * Real.sqrt (Real.exp κ * (2 * t + 1) ^ d))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        have hfam' : ((boxFamilies (d := d) t K0).card : ℝ)
            ≤ (((K0 + 1) * ((2 * t + 1) ^ d) ^ K0 : ℕ) : ℝ) := by exact_mod_cast hfam
        have hpos : 0 ≤ Real.exp (κ * (θ * t)) * (ρ ^ t * Real.sqrt (Real.exp κ * (2 * t + 1) ^ d)) :=
          mul_nonneg (Real.exp_pos _).le (mul_nonneg (pow_nonneg hρpos.le _) (Real.sqrt_nonneg _))
        have := mul_le_mul_of_nonneg_right hfam' hpos
        linarith

end Parking

end
