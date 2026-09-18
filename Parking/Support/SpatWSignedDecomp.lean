/-
The deterministic decomposition of the signed pair, `eq:signed-density-decomposition`
(`parking.tex:1750-1758`), and the conditional convergence it feeds: the part of `signedPair`'s
convergence that does NOT depend on the value side, plus the exact conditional statement that does.

`Parking.signed_count` (`Parking/Support/Transport.lean`) is the paper's pathwise
mass-balance identity `A_t(x)-H_t(x) = η(x) + ∑_y I_{y,x}(U_t(y)) - U_t(x)`.  Summing it against a
rescaled test function `φ_R(x) := φ(x/R)` and reindexing the arrivals term by the DEPARTING site
(rather than the receiving site) gives, PURELY ALGEBRAICALLY (no probability beyond
`signed_count` itself),
```
⟨ν_R,φ⟩ = ⟨η_R,φ⟩ + R^{-d/2}∑_y U_t(y)(P-I)φ_R(y) + M_R(φ)
```
exactly `eq:signed-density-decomposition`, with `M_R(φ) := R^{-d/2}∑_y∑_{j<U_t(y)}[φ_R(ρ_j(y)) -
(Pφ_R)(y)]` the paper's own formula (`ρ_{j+1}(y)` in the paper's one-indexed convention is
`ω.2.1 (y,j)` here, per `Parking/Frozen/Exposure.lean`'s docstring).  The reindexing uses
`arrivals_sum_eq_range` (`Parking.arrivals` is `LatticeProb.arrivals`, the raw departure-count
function `signed_count` is stated with): summing the arrival COUNT at `x` from `y`, weighted by a
test function of `x`, over all `x`, equals summing the test function over the actual destinations
of the individual departures `j < m`.  This is the fiber-counting identity behind `arrivals`
itself and needs no hypothesis on the data.  Everything outside a fixed finite box (one lattice
step wider than where `φ_R` itself is supported) contributes nothing, by
`Parking.nbrFinset_symm`/`Parking.nbrFinset_subset_box` (`Parking/Support/Odometer.lean` and
`Parking/Support/KernelBridge.lean`): the departures counted by `M_R` and `⟨(P-I)φ_R,U_t⟩`
only ever reach a neighbour of their own site, so a site whose every neighbour lies outside the
scaled support of `φ` contributes zero to either term.

`Parking.signedM`'s convergence to zero in probability needs Lemma 5.3 (`lem:exposure`,
`Parking.Frozen.exposure`, SEALED) to see the summands as martingale differences and Corollary
1.3 (`cor:growth`, `Parking.Frozen.growth`, SEALED) for the second-moment bound
`parking.tex:1758-1762` quotes; this is a genuine martingale construction (a reveal-in-read-order
array over the departures, analogous to `Parking/Support/WMartingale.lean`'s own construction for
a DIFFERENT martingale) and is NOT proved in this module.  The middle term's own convergence to
`⟨ℒ𝒰(1,·),φ⟩` needs the value side's own `Ū_R(1,·) → 𝒰(1,·)` convergence together with a Taylor
expansion of the discrete `(P-I)` against it, and is likewise not proved here.  Both are taken as
explicit hypotheses of `Parking.tendsto_signedPair_sub_scenePair_of_convergence` below, which
proves `signedPair`'s own convergence (relative to `scenePair`'s, established unconditionally by
`Parking.tendsto_scenePair_fdd`, `Parking/Support/SpatWSceneryFdd.lean`) from those two hypotheses
alone, by a standard convergence-in-probability-of-a-sum argument.
-/
import Parking.Support.SpatWSceneryFdd

open MeasureTheory LatticeProb Finset Filter Topology
open scoped ENNReal

noncomputable section
namespace Parking

variable {d : ℕ}

/-! ### A per-site value paired against a rescaled test function reduces to a finite box -/

/-- **A per-site value, paired against a rescaled test function, reduces to the box sum.**  The
general form of `Parking.scenePair_eq_sceneryBox_sum`, for an arbitrary per-site value `g`. -/
theorem tsum_mul_testFn_eq_sceneryBox_sum {g : Site d → ℝ} {φ : (Fin d → ℝ) → ℝ} {B : ℝ}
    (hB : 0 < B) (hbound : ∀ x : Fin d → ℝ, φ x ≠ 0 → ‖x‖ ≤ B) {R : ℝ} (hR : 1 ≤ R) :
    ∑' x : Site d, g x * φ (fun i => (x i : ℝ) / R)
      = ∑ x ∈ sceneryBox d B R, g x * φ (fun i => (x i : ℝ) / R) := by
  apply tsum_eq_sum
  intro x hx
  by_contra hne
  apply hx
  apply mem_sceneryBox_of_ne_zero hB hbound hR
  intro hz
  exact hne (by rw [hz, mul_zero])

/-! ### The arrivals fiber-sum identity -/

/-- **Summing the arrival count at `x` from `y`, weighted by a test function of `x`, over every
`x`, equals summing the test function over the actual destinations of the departures `j < m`.**
The fiber-counting identity underlying `arrivals` itself; no hypothesis on `stack` is needed. -/
theorem arrivals_sum_eq_range (stack : Site d × ℕ → Site d) (y : Site d) (φ : Site d → ℝ)
    (m : ℕ) :
    ∑' x : Site d, (arrivals stack y x m : ℝ) * φ x = ∑ j ∈ Finset.range m, φ (stack (y, j)) := by
  have hcard : ∀ x : Site d, arrivals stack y x m
      = ∑ j ∈ Finset.range m, if stack (y, j) = x then 1 else 0 := by
    intro x
    rw [arrivals, Finset.card_filter]
  have hfun : (fun x : Site d => (arrivals stack y x m : ℝ) * φ x)
      = fun x => ∑ j ∈ Finset.range m, (if stack (y, j) = x then φ x else 0) := by
    funext x
    rw [hcard x]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  rw [hfun]
  have hswap : ∑' x : Site d, ∑ j ∈ Finset.range m, (if stack (y, j) = x then φ x else 0)
      = ∑ j ∈ Finset.range m, ∑' x : Site d, (if stack (y, j) = x then φ x else 0) := by
    apply Summable.tsum_finsetSum
    intro j _
    apply summable_of_ne_finset_zero (s := {stack (y, j)})
    intro x hx
    simp only [Finset.mem_singleton] at hx
    rw [if_neg (fun h => hx h.symm)]
  rw [hswap]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tsum_eq_single (stack (y, j)) (fun x hx => if_neg (fun h => hx h.symm))]
  simp

theorem nbrFinset_subset_boxFinset_succ {B : ℕ} {x : Site d}
    (hx : x ∈ boxFinset (0 : Site d) B) :
    nbrFinset x ⊆ boxFinset (0 : Site d) (B + 1) := by
  intro z hz
  have hz1 : z ∈ boxFinset x 1 := nbrFinset_subset_box x hz
  rw [mem_boxFinset_iff] at hx hz1 ⊢
  intro i
  have h1 := hx i
  have h2 := hz1 i
  simp only [Pi.zero_apply] at h1 ⊢
  rw [abs_le] at h1 h2 ⊢
  omega

theorem arrivals_ne_zero_imp_mem_nbrFinset {ω : Data d}
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1) (y x : Site d) (m : ℕ)
    (h : arrivals ω.2.1 y x m ≠ 0) : y ∈ nbrFinset x := by
  unfold arrivals at h
  rw [Finset.card_ne_zero] at h
  obtain ⟨j, hj⟩ := h
  simp only [Finset.mem_filter, Finset.mem_range] at hj
  obtain ⟨_, hjeq⟩ := hj
  have hnbr := hstep (y, j)
  rw [hjeq] at hnbr
  exact nbrFinset_symm hnbr

/-- The arrivals-term of the signed decomposition, reindexed by the DEPARTING site. -/
theorem arrivals_term_eq (ω : Data d) (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1)
    {B : ℝ} (hB : 0 < B) {φ : (Fin d → ℝ) → ℝ}
    (hbound : ∀ x : Fin d → ℝ, φ x ≠ 0 → ‖x‖ ≤ B) {R : ℝ} (hR : 1 ≤ R) (t : ℕ) :
    ∑ x ∈ sceneryBox d B R,
        (∑ y ∈ nbrFinset x, (arrivals ω.2.1 y x (U ω t y) : ℝ)) * φ (fun i => (x i : ℝ) / R)
      = ∑ y ∈ boxFinset (0 : Site d) (⌈B * R⌉₊ + 1), ∑ j ∈ Finset.range (U ω t y),
          φ (fun i => ((ω.2.1 (y, j)) i : ℝ) / R) := by
  have hstep0 : ∀ x ∈ sceneryBox d B R,
      (∑ y ∈ nbrFinset x, (arrivals ω.2.1 y x (U ω t y) : ℝ))
        = ∑ y ∈ boxFinset (0 : Site d) (⌈B * R⌉₊ + 1), (arrivals ω.2.1 y x (U ω t y) : ℝ) := by
    intro x hx
    apply Finset.sum_subset (nbrFinset_subset_boxFinset_succ hx)
    intro y _ hy
    have hz : arrivals ω.2.1 y x (U ω t y) = 0 := by
      by_contra hne
      exact hy (arrivals_ne_zero_imp_mem_nbrFinset hstep y x _ hne)
    rw [hz]; norm_num
  rw [Finset.sum_congr rfl (fun x hx => by rw [hstep0 x hx])]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_mul _ _ _)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← tsum_mul_testFn_eq_sceneryBox_sum hB hbound hR]
  exact arrivals_sum_eq_range ω.2.1 y (fun x => φ (fun i => (x i : ℝ) / R)) (U ω t y)

/-! ### The decomposition -/

/-- The signed pair's middle term: `R^{-d/2}∑_y U_t(y)(P-I)φ_R(y)`. -/
def signedMiddle (ω : Data d) (R : ℝ) (φ : (Fin d → ℝ) → ℝ) : ℝ :=
  R ^ (-(d : ℝ) / 2) * ∑' y : Site d, (U ω ⌊R ^ 2⌋₊ y : ℝ) *
    (walkOp (fun x => φ (fun i => (x i : ℝ) / R)) y - φ (fun i => (y i : ℝ) / R))

/-- The signed pair's martingale remainder `M_R(φ)`, `eq:signed-density-decomposition`'s own
formula: `R^{-d/2}∑_y∑_{j<U_t(y)}[φ_R(ρ_j(y))-(Pφ_R)(y)]`. -/
def signedM (ω : Data d) (R : ℝ) (φ : (Fin d → ℝ) → ℝ) : ℝ :=
  R ^ (-(d : ℝ) / 2) * ∑' y : Site d, (∑ j ∈ Finset.range (U ω ⌊R ^ 2⌋₊ y),
      φ (fun i => ((ω.2.1 (y, j)) i : ℝ) / R)
    - (U ω ⌊R ^ 2⌋₊ y : ℝ) * walkOp (fun x => φ (fun i => (x i : ℝ) / R)) y)

/-- **The deterministic decomposition of the signed pair**, `eq:signed-density-decomposition`,
`parking.tex:1750-1758`: purely algebraic, from `Parking.signed_count`. -/
theorem signedPair_eq_decomposition {ω : Data d}
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1) {φ : (Fin d → ℝ) → ℝ}
    (hφ : IsTestFun φ) {R : ℝ} (hR : 1 ≤ R) :
    signedPair ω R φ = scenePair ω R φ + signedMiddle ω R φ + signedM ω R φ := by
  obtain ⟨B, hB, hbound⟩ := exists_norm_bound_of_hasCompactSupport hφ.2
  set box := sceneryBox d B R with hboxdef
  set box' := boxFinset (0 : Site d) (⌈B * R⌉₊ + 1) with hbox'def
  have hboxsub : box ⊆ box' := by
    intro x hx
    rw [hboxdef, sceneryBox, mem_boxFinset_iff] at hx
    rw [hbox'def, mem_boxFinset_iff]
    intro i
    have := hx i
    push_cast
    omega
  set t := ⌊R ^ 2⌋₊ with htdef
  set S1 : ℝ := ∑ x ∈ box, (ω.1 x : ℝ) * φ (fun i => (x i : ℝ) / R) with hS1def
  set S2 : ℝ := ∑ y ∈ box', ∑ j ∈ Finset.range (U ω t y),
      φ (fun i => ((ω.2.1 (y, j)) i : ℝ) / R) with hS2def
  set S3 : ℝ := ∑ y ∈ box', (U ω t y : ℝ) * φ (fun i => (y i : ℝ) / R) with hS3def
  set S4 : ℝ := ∑ y ∈ box', (U ω t y : ℝ) *
      walkOp (fun x => φ (fun i => (x i : ℝ) / R)) y with hS4def
  have hetaEq : ∑' x : Site d, (ω.1 x : ℝ) * φ (fun i => (x i : ℝ) / R) = S1 :=
    tsum_mul_testFn_eq_sceneryBox_sum hB hbound hR
  have hUEq : ∑' x : Site d, (U ω t x : ℝ) * φ (fun i => (x i : ℝ) / R)
      = ∑ x ∈ box, (U ω t x : ℝ) * φ (fun i => (x i : ℝ) / R) :=
    tsum_mul_testFn_eq_sceneryBox_sum hB hbound hR
  have hUboxEq : ∑ x ∈ box, (U ω t x : ℝ) * φ (fun i => (x i : ℝ) / R) = S3 := by
    rw [hS3def]
    apply Finset.sum_subset hboxsub
    intro y _ hy
    have hφ0 : φ (fun i => (y i : ℝ) / R) = 0 := by
      by_contra hne
      exact hy (by rw [hboxdef]; exact mem_sceneryBox_of_ne_zero hB hbound hR hne)
    rw [hφ0, mul_zero]
  have harr : ∑ x ∈ box, (∑ y ∈ nbrFinset x, (arrivals ω.2.1 y x (U ω t y) : ℝ))
      * φ (fun i => (x i : ℝ) / R) = S2 := by
    rw [hS2def]
    exact arrivals_term_eq ω hstep hB hbound hR t
  have hAH : ∑' x : Site d, ((A ω t x : ℝ) - (H ω t x : ℝ)) * φ (fun i => (x i : ℝ) / R)
      = ∑ x ∈ box, ((A ω t x : ℝ) - (H ω t x : ℝ)) * φ (fun i => (x i : ℝ) / R) :=
    tsum_mul_testFn_eq_sceneryBox_sum hB hbound hR
  have hpointwise : ∀ x ∈ box, ((A ω t x : ℝ) - (H ω t x : ℝ)) * φ (fun i => (x i : ℝ) / R)
      = ((ω.1 x : ℝ) + (∑ y ∈ nbrFinset x, (arrivals ω.2.1 y x (U ω t y) : ℝ))
          - (U ω t x : ℝ)) * φ (fun i => (x i : ℝ) / R) := by
    intro x _
    have hsc := signed_count (ω := ω) hstep t x
    have hcast : (A ω t x : ℝ) - (H ω t x : ℝ)
        = (ω.1 x : ℝ) + (∑ y ∈ nbrFinset x, (arrivals ω.2.1 y x (U ω t y) : ℝ))
          - (U ω t x : ℝ) := by
      have hcc := congrArg (fun z : ℤ => (z : ℝ)) hsc
      push_cast at hcc
      convert hcc using 2
    rw [hcast]
  have hAHexpand : ∑ x ∈ box, ((A ω t x : ℝ) - (H ω t x : ℝ)) * φ (fun i => (x i : ℝ) / R)
      = S1 + S2 - S3 := by
    rw [Finset.sum_congr rfl hpointwise]
    rw [Finset.sum_congr rfl (fun x (_ : x ∈ box) => by ring : ∀ x ∈ box,
        ((ω.1 x : ℝ) + (∑ y ∈ nbrFinset x, (arrivals ω.2.1 y x (U ω t y) : ℝ)) - (U ω t x : ℝ))
          * φ (fun i => (x i : ℝ) / R)
        = ((ω.1 x : ℝ) * φ (fun i => (x i : ℝ) / R))
          + ((∑ y ∈ nbrFinset x, (arrivals ω.2.1 y x (U ω t y) : ℝ)) * φ (fun i => (x i : ℝ) / R))
          - ((U ω t x : ℝ) * φ (fun i => (x i : ℝ) / R)))]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← hS1def, harr, hUboxEq]
  -- Everything outside `box'` vanishes: every neighbour of a point outside `box'` has `φ_R = 0`.
  have hnbrvanish : ∀ y : Site d, y ∉ box' → ∀ z ∈ nbrFinset y, φ (fun i => (z i : ℝ) / R) = 0 := by
    intro y hy z hz
    by_contra hne
    have hzbox : z ∈ box := by rw [hboxdef]; exact mem_sceneryBox_of_ne_zero hB hbound hR hne
    apply hy
    rw [hbox'def]
    exact nbrFinset_subset_boxFinset_succ hzbox (nbrFinset_symm hz)
  have hφvanish : ∀ y : Site d, y ∉ box' → φ (fun i => (y i : ℝ) / R) = 0 := by
    intro y hy
    by_contra hne
    exact hy (hboxsub (by rw [hboxdef]; exact mem_sceneryBox_of_ne_zero hB hbound hR hne))
  have hwalkvanish : ∀ y : Site d, y ∉ box' →
      walkOp (fun x => φ (fun i => (x i : ℝ) / R)) y = 0 := by
    intro y hy
    unfold walkOp nbrSum
    have hterm : ∀ i : Fin d, φ (fun j => ((y + unit i) j : ℝ) / R) = 0
        ∧ φ (fun j => ((y - unit i) j : ℝ) / R) = 0 :=
      fun i => ⟨hnbrvanish y hy _ (mem_nbrFinset_add y i), hnbrvanish y hy _ (mem_nbrFinset_sub y i)⟩
    have hsum0 : (∑ i : Fin d, (φ (fun j => ((y + unit i) j : ℝ) / R)
        + φ (fun j => ((y - unit i) j : ℝ) / R))) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [(hterm i).1, (hterm i).2]; ring
    rw [hsum0]; ring
  have hmiddleEq : signedMiddle ω R φ = R ^ (-(d : ℝ) / 2) * (S4 - S3) := by
    unfold signedMiddle
    rw [← htdef]
    congr 1
    have hts : ∑' y : Site d, (U ω t y : ℝ) *
        (walkOp (fun x => φ (fun i => (x i : ℝ) / R)) y - φ (fun i => (y i : ℝ) / R))
        = ∑ y ∈ box', (U ω t y : ℝ) *
            (walkOp (fun x => φ (fun i => (x i : ℝ) / R)) y - φ (fun i => (y i : ℝ) / R)) := by
      apply tsum_eq_sum
      intro y hy
      rw [hwalkvanish y hy, hφvanish y hy]
      ring
    rw [hts, hS4def, hS3def, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  have hMeq : signedM ω R φ = R ^ (-(d : ℝ) / 2) * (S2 - S4) := by
    unfold signedM
    rw [← htdef]
    congr 1
    have hts : ∑' y : Site d, (∑ j ∈ Finset.range (U ω t y),
          φ (fun i => ((ω.2.1 (y, j)) i : ℝ) / R)
        - (U ω t y : ℝ) * walkOp (fun x => φ (fun i => (x i : ℝ) / R)) y)
        = ∑ y ∈ box', (∑ j ∈ Finset.range (U ω t y), φ (fun i => ((ω.2.1 (y, j)) i : ℝ) / R)
            - (U ω t y : ℝ) * walkOp (fun x => φ (fun i => (x i : ℝ) / R)) y) := by
      apply tsum_eq_sum
      intro y hy
      have hall0 : ∀ j ∈ Finset.range (U ω t y), φ (fun i => ((ω.2.1 (y, j)) i : ℝ) / R) = 0 :=
        fun j _ => hnbrvanish y hy _ (hstep (y, j))
      rw [Finset.sum_congr rfl hall0, Finset.sum_const, hwalkvanish y hy]
      simp
    rw [hts, hS2def, hS4def, ← Finset.sum_sub_distrib]
  show R ^ (-(d : ℝ) / 2) * (∑' x : Site d, ((A ω t x : ℝ) - (H ω t x : ℝ))
        * φ (fun i => (x i : ℝ) / R))
      = R ^ (-(d : ℝ) / 2) * (∑' x : Site d, (ω.1 x : ℝ) * φ (fun i => (x i : ℝ) / R))
        + signedMiddle ω R φ + signedM ω R φ
  rw [hAH, hAHexpand, hetaEq, hmiddleEq, hMeq]
  ring

/-! ### Measurability -/

-- The measurability of `signedPair` is `Parking.measurable_signedPair`
-- (`Parking/Support/NearestEvents.lean`), which is unconditional in `R` and `φ`: it needs
-- no `IsTestFun` or `1 ≤ R` hypothesis, so no separate measurability statement for
-- `signedPair` is needed in this module.

/-- **`signedMiddle` reduces to the finite box sum**, purely deterministic (no `hstep` needed,
unlike `signedPair_eq_decomposition`): every site outside the box where `φ`'s rescaled support,
widened by one lattice step, lives contributes `0`, since both `φ_R` and `walkOp φ_R` vanish
there.  This is the same vanishing argument `signedPair_eq_decomposition`'s own local `hmiddleEq`
uses, extracted here as its own lemma because `signedMiddle`'s measurability needs it. -/
theorem signedMiddle_eq_sceneryBox_sum {φ : (Fin d → ℝ) → ℝ} {B : ℝ} (hB : 0 < B)
    (hbound : ∀ x : Fin d → ℝ, φ x ≠ 0 → ‖x‖ ≤ B) {R : ℝ} (hR : 1 ≤ R) (ω : Data d) :
    signedMiddle ω R φ
      = R ^ (-(d : ℝ) / 2) * ∑ y ∈ boxFinset (0 : Site d) (⌈B * R⌉₊ + 1),
          (U ω ⌊R ^ 2⌋₊ y : ℝ) *
            (walkOp (fun x => φ (fun i => (x i : ℝ) / R)) y - φ (fun i => (y i : ℝ) / R)) := by
  set box := sceneryBox d B R with hboxdef
  set box' := boxFinset (0 : Site d) (⌈B * R⌉₊ + 1) with hbox'def
  have hboxsub : box ⊆ box' := by
    intro x hx
    rw [hboxdef, sceneryBox, mem_boxFinset_iff] at hx
    rw [hbox'def, mem_boxFinset_iff]
    intro i
    have := hx i
    push_cast
    omega
  have hnbrvanish : ∀ y : Site d, y ∉ box' → ∀ z ∈ nbrFinset y, φ (fun i => (z i : ℝ) / R) = 0 := by
    intro y hy z hz
    by_contra hne
    have hzbox : z ∈ box := by rw [hboxdef]; exact mem_sceneryBox_of_ne_zero hB hbound hR hne
    apply hy
    rw [hbox'def]
    exact nbrFinset_subset_boxFinset_succ hzbox (nbrFinset_symm hz)
  have hφvanish : ∀ y : Site d, y ∉ box' → φ (fun i => (y i : ℝ) / R) = 0 := by
    intro y hy
    by_contra hne
    exact hy (hboxsub (by rw [hboxdef]; exact mem_sceneryBox_of_ne_zero hB hbound hR hne))
  have hwalkvanish : ∀ y : Site d, y ∉ box' →
      walkOp (fun x => φ (fun i => (x i : ℝ) / R)) y = 0 := by
    intro y hy
    unfold walkOp nbrSum
    have hterm : ∀ i : Fin d, φ (fun j => ((y + unit i) j : ℝ) / R) = 0
        ∧ φ (fun j => ((y - unit i) j : ℝ) / R) = 0 :=
      fun i => ⟨hnbrvanish y hy _ (mem_nbrFinset_add y i), hnbrvanish y hy _ (mem_nbrFinset_sub y i)⟩
    have hsum0 : (∑ i : Fin d, (φ (fun j => ((y + unit i) j : ℝ) / R)
        + φ (fun j => ((y - unit i) j : ℝ) / R))) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [(hterm i).1, (hterm i).2]; ring
    rw [hsum0]; ring
  unfold signedMiddle
  congr 1
  apply tsum_eq_sum
  intro y hy
  rw [hwalkvanish y hy, hφvanish y hy]
  ring

/-- **`signedMiddle` is measurable**, unconditional (no `IsTestFun` or `1 ≤ R` beyond the
compact-support bound), from the box reduction above: `(U ω ⌊R^2⌋₊ y : ℝ)` is measurable in `ω`
(`Parking.measurable_U`) and the rest of each summand is a constant. -/
theorem measurable_signedMiddle {φ : (Fin d → ℝ) → ℝ} {B : ℝ} (hB : 0 < B)
    (hbound : ∀ x : Fin d → ℝ, φ x ≠ 0 → ‖x‖ ≤ B) {R : ℝ} (hR : 1 ≤ R) :
    Measurable (fun ω : Data d => signedMiddle ω R φ) := by
  have heq : (fun ω : Data d => signedMiddle ω R φ) = fun ω =>
      R ^ (-(d : ℝ) / 2) * ∑ y ∈ boxFinset (0 : Site d) (⌈B * R⌉₊ + 1),
        (U ω ⌊R ^ 2⌋₊ y : ℝ) *
          (walkOp (fun x => φ (fun i => (x i : ℝ) / R)) y - φ (fun i => (y i : ℝ) / R)) :=
    funext fun ω => signedMiddle_eq_sceneryBox_sum hB hbound hR ω
  rw [heq]
  exact measurable_const.mul (Finset.measurable_sum _ fun y _ =>
    ((measurable_from_countable' fun m : ℕ => (m : ℝ)).comp
      (measurable_U ⌊R ^ 2⌋₊ y)).mul_const _)

/-! ### The conditional convergence -/

/-- **`signedPair`'s convergence in probability, relative to `scenePair`, conditional on the
martingale remainder vanishing and the value side's own convergence of the middle term.**  Given
(i) `signedM(φ) → 0` in `(law d ν)`-probability (needs `lem:exposure`+`cor:growth`; see the module
docstring) and (ii) `signedMiddle(φ) → L` in `(law d ν)`-probability for some
`L : Data d → ℝ` (the value side's own `Ū_R(1,·) → 𝒰(1,·)` convergence, packaged through the
Taylor expansion of `(P-I)φ_R` as the convergence of the actual quantity this decomposition
produces), `signedPair(φ) - scenePair(φ) → L` in `(law d ν)`-probability: exactly the discharge
`signedPair`'s coordinate of `hjoint` needs, once `L` is identified with
`ω ↦ ∫ x, Uc ω 1 x * contOp d φ x`. -/
theorem tendsto_signedPair_sub_scenePair_of_convergence (hd : 1 ≤ d) (ν : Measure ℤ)
    (hν : CriticalLaw ν) {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) (L : Data d → ℝ)
    (hM : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun R : ℝ => ((law d ν) {w | ε < |signedM w R φ|}).toReal) atTop (𝓝 0))
    (hMiddle : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun R : ℝ => ((law d ν) {w | ε < |signedMiddle w R φ - L w|}).toReal) atTop
        (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun R : ℝ =>
        ((law d ν) {w | ε < |signedPair w R φ - scenePair w R φ - L w|}).toReal) atTop
      (𝓝 0) := by
  intro ε hε
  haveI := hν.prob
  haveI hlaw : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  have hae := ae_stack_nbr_law hd ν
  have hbound : ∀ R : ℝ, 1 ≤ R →
      ((law d ν) {w | ε < |signedPair w R φ - scenePair w R φ - L w|}).toReal
        ≤ ((law d ν) {w | ε / 2 < |signedMiddle w R φ - L w|}).toReal
          + ((law d ν) {w | ε / 2 < |signedM w R φ|}).toReal := by
    intro R hR
    have hsub : {w : Data d | ε < |signedPair w R φ - scenePair w R φ - L w|}
        ⊆ {w | ¬ (∀ q : Site d × ℕ, w.2.1 q ∈ nbrFinset q.1)}
          ∪ {w | ε / 2 < |signedMiddle w R φ - L w|} ∪ {w | ε / 2 < |signedM w R φ|} := by
      intro w hw
      by_cases hstep : ∀ q : Site d × ℕ, w.2.1 q ∈ nbrFinset q.1
      · have hdecomp := signedPair_eq_decomposition hstep hφ hR
        have hbig : ε < |signedMiddle w R φ - L w| + |signedM w R φ| := by
          have heq : signedPair w R φ - scenePair w R φ - L w
              = (signedMiddle w R φ - L w) + signedM w R φ := by
            rw [hdecomp]; ring
          calc ε < |signedPair w R φ - scenePair w R φ - L w| := hw
            _ = |(signedMiddle w R φ - L w) + signedM w R φ| := by rw [heq]
            _ ≤ |signedMiddle w R φ - L w| + |signedM w R φ| := abs_add_le _ _
        rcases lt_or_ge (ε / 2) (|signedMiddle w R φ - L w|) with h1 | h1
        · exact Or.inl (Or.inr h1)
        · refine Or.inr (show ε / 2 < |signedM w R φ| from ?_)
          by_contra h2
          have h2' : |signedM w R φ| ≤ ε / 2 := not_lt.mp h2
          linarith
      · exact Or.inl (Or.inl hstep)
    have hmeas0 : (law d ν) {w : Data d | ¬ (∀ q : Site d × ℕ, w.2.1 q ∈ nbrFinset q.1)} = 0 :=
      MeasureTheory.mem_ae_iff.mp hae
    have hmono := measure_mono (μ := law d ν) hsub
    have hunion1 : (law d ν) ({w : Data d | ¬ (∀ q : Site d × ℕ, w.2.1 q ∈ nbrFinset q.1)}
          ∪ {w | ε / 2 < |signedMiddle w R φ - L w|})
        ≤ (law d ν) {w : Data d | ¬ (∀ q : Site d × ℕ, w.2.1 q ∈ nbrFinset q.1)}
          + (law d ν) {w | ε / 2 < |signedMiddle w R φ - L w|} :=
      measure_union_le _ _
    have hunion : (law d ν) ({w : Data d | ¬ (∀ q : Site d × ℕ, w.2.1 q ∈ nbrFinset q.1)}
          ∪ {w | ε / 2 < |signedMiddle w R φ - L w|} ∪ {w | ε / 2 < |signedM w R φ|})
        ≤ (law d ν) {w : Data d | ¬ (∀ q : Site d × ℕ, w.2.1 q ∈ nbrFinset q.1)}
          + (law d ν) {w | ε / 2 < |signedMiddle w R φ - L w|}
          + (law d ν) {w | ε / 2 < |signedM w R φ|} := by
      refine (measure_union_le _ _).trans ?_
      exact add_le_add hunion1 le_rfl
    have hle := hmono.trans hunion
    rw [hmeas0, zero_add] at hle
    have hfin1 : (law d ν) {w | ε / 2 < |signedMiddle w R φ - L w|} ≠ ⊤ :=
      (measure_lt_top (law d ν) _).ne
    have hfin2 : (law d ν) {w | ε / 2 < |signedM w R φ|} ≠ ⊤ :=
      (measure_lt_top (law d ν) _).ne
    calc ((law d ν) {w | ε < |signedPair w R φ - scenePair w R φ - L w|}).toReal
        ≤ ((law d ν) {w | ε / 2 < |signedMiddle w R φ - L w|}
            + (law d ν) {w | ε / 2 < |signedM w R φ|}).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin1, hfin2⟩) hle
      _ = ((law d ν) {w | ε / 2 < |signedMiddle w R φ - L w|}).toReal
            + ((law d ν) {w | ε / 2 < |signedM w R φ|}).toReal :=
          ENNReal.toReal_add hfin1 hfin2
  have hsqueeze : Tendsto (fun R : ℝ => ((law d ν) {w | ε / 2 < |signedMiddle w R φ - L w|}).toReal
      + ((law d ν) {w | ε / 2 < |signedM w R φ|}).toReal) atTop (𝓝 0) := by
    have := (hMiddle (ε / 2) (by linarith)).add (hM (ε / 2) (by linarith))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsqueeze ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact ENNReal.toReal_nonneg
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact hbound R hR

end Parking
end
