import Parking.External.UConcentration
import Parking.Support.SubGaussianMoment
import Parking.Support.FinsetReindex
import Parking.Support.LinBox
import LatticeProb.Prob.FiniteMarginal

/-!
# The U-concentration estimate, proved

Proves `Parking.External.uConcentration`, the concentration estimate for the solution of
`v_{n+1} = (η + K v_n)⁺` cited as an external input in `Parking/External/UConcentration.lean`
(`parking.tex:1402-1415`, label `lem:u-concentration`). The route is the coordinate-Lipschitz
bound on `v_n(0)`, through the Green function `kGreen r K n z`, combined with the library's
weighted exponential concentration `LatticeProb.weighted_exp_conc_tail`.
-/

open MeasureTheory

noncomputable section

namespace Parking.External

open Parking LatticeProb LatticeProb.Walk

theorem uconc_mem_box_symm {d : ℕ} {x y : Site d} {r : ℕ} :
    y ∈ boxFinset x r ↔ x ∈ boxFinset y r := by
  rw [mem_boxFinset_iff, mem_boxFinset_iff]
  constructor
  · intro h i
    simpa [Pi.sub_apply, abs_sub_comm] using h i
  · intro h i
    simpa [Pi.sub_apply, abs_sub_comm] using h i

def uconc_kIterFrom {d : ℕ} (r : ℕ) (K : Site d → Site d → ℝ) :
    ℕ → Site d → Site d → ℝ
  | 0, x, z => if z = x then 1 else 0
  | j + 1, x, z => ∑ y ∈ boxFinset x r, K x y * uconc_kIterFrom r K j y z

theorem uconc_kIterFrom_eq_kIter_sub {d : ℕ} {r : ℕ}
    {K : Site d → Site d → ℝ} (hK : IsLatticeKernel r K) (j : ℕ)
    (x z : Site d) :
    uconc_kIterFrom r K j x z = kIter r K j (z - x) := by
  induction j generalizing x z with
  | zero =>
      by_cases hzx : z = x <;> simp [uconc_kIterFrom, kIter, hzx,
        sub_eq_zero]
  | succ j ih =>
      simp only [uconc_kIterFrom, kIter]
      apply Finset.sum_bij' (fun y _ => z - y) (fun w _ => z - w) ?_ ?_ ?_ ?_ ?_
      · intro y hy
        rw [mem_boxFinset_iff] at hy ⊢
        intro i
        have hi := hy i
        change |z i - y i - (z i - x i)| ≤ (r : ℤ)
        rw [show z i - y i - (z i - x i) = x i - y i by ring]
        rw [abs_sub_comm]
        exact hi
      · intro w hw
        rw [mem_boxFinset_iff] at hw ⊢
        intro i
        have hi := hw i
        change |z i - w i - x i| ≤ (r : ℤ)
        rw [show z i - w i - x i = -(w i - (z i - x i)) by ring, abs_neg]
        exact hi
      · intro y hy
        simp
      · intro w hw
        simp
      · intro y hy
        rw [ih]
        have hshift := hK.2.2.2 (z - y - x) x y
        have hshift' : K x y = K (z - y) (z - x) := by
          rw [← hshift]
          congr 1 <;> funext i <;> dsimp <;> abel
        rw [hshift', mul_comm]

theorem uconc_kIterFrom_nonneg {d : ℕ} {r : ℕ}
    {K : Site d → Site d → ℝ} (hK : IsLatticeKernel r K) :
    ∀ j x z, 0 ≤ uconc_kIterFrom r K j x z := by
  intro j
  induction j with
  | zero =>
      intro x z
      by_cases hzx : z = x <;> simp [uconc_kIterFrom, hzx]
  | succ j ih =>
      intro x z
      simp only [uconc_kIterFrom]
      exact Finset.sum_nonneg fun y hy =>
        mul_nonneg (hK.1 x y) (ih y z)

theorem uconc_kIter_nonneg {d : ℕ} {r : ℕ}
    {K : Site d → Site d → ℝ} (hK : IsLatticeKernel r K) :
    ∀ j z, 0 ≤ kIter r K j z := by
  intro j z
  have h := uconc_kIterFrom_nonneg hK j 0 z
  calc
    0 ≤ uconc_kIterFrom r K j 0 z := h
    _ = kIter r K j (z - 0) := uconc_kIterFrom_eq_kIter_sub hK j 0 z
    _ = kIter r K j z := by simp

theorem uconc_kGreen_nonneg {d : ℕ} {r : ℕ}
    {K : Site d → Site d → ℝ} (hK : IsLatticeKernel r K) (n : ℕ) (z : Site d) :
    0 ≤ kGreen r K n z := by
  unfold kGreen
  exact Finset.sum_nonneg fun j hj => uconc_kIter_nonneg hK j z

theorem uconc_kIter_zero_of_not_mem {d : ℕ} {r : ℕ}
    {K : Site d → Site d → ℝ} (_hK : IsLatticeKernel r K) :
    ∀ j z, z ∉ boxFinset (0 : Site d) (r * j) → kIter r K j z = 0 := by
  intro j
  induction j with
  | zero =>
      intro z hz
      simp only [kIter]
      rw [if_neg]
      intro hz0
      subst z
      exact hz (mem_boxFinset_iff.mpr (fun i => by simp))
  | succ j ih =>
      intro z hz
      simp only [kIter]
      apply Finset.sum_eq_zero
      intro y hy
      by_cases hybox : y ∈ boxFinset (0 : Site d) (r * j)
      · exfalso
        apply hz
        have hzy : z ∈ boxFinset y r :=
          (uconc_mem_box_symm (x := z) (y := y) (r := r)).mp hy
        have h := mem_boxFinset_add hybox hzy
        simpa [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
      · rw [ih y hybox, zero_mul]

theorem uconc_kGreen_zero_of_not_mem {d : ℕ} {r : ℕ}
    {K : Site d → Site d → ℝ} (hK : IsLatticeKernel r K) (n : ℕ) (z : Site d)
    (hz : z ∉ boxFinset (0 : Site d) (r * n)) :
    kGreen r K n z = 0 := by
  unfold kGreen
  apply Finset.sum_eq_zero
  intro j hj
  apply uconc_kIter_zero_of_not_mem hK j z
  intro hzj
  apply hz
  exact boxFinset_mono (by
    have hj' := Finset.mem_range.mp hj
    exact Nat.mul_le_mul_left r (Nat.le_of_lt hj')) hzj

theorem uconc_kGreen_one_le {d : ℕ} {r : ℕ}
    {K : Site d → Site d → ℝ} (hK : IsLatticeKernel r K) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ kGreen r K n 0 := by
  unfold kGreen
  have hmem : 0 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have hsingle := Finset.single_le_sum
    (f := fun j : ℕ => kIter r K j 0)
    (fun j hj => uconc_kIter_nonneg hK j 0) hmem
  simpa [kIter] using hsingle

def uconc_kGreenFrom {d : ℕ} (r : ℕ) (K : Site d → Site d → ℝ)
    (n : ℕ) (x z : Site d) : ℝ :=
  ∑ j ∈ Finset.range n, uconc_kIterFrom r K j x z

theorem uconc_kGreenFrom_eq_kGreen_sub {d : ℕ} {r : ℕ}
    {K : Site d → Site d → ℝ} (hK : IsLatticeKernel r K) (n : ℕ)
    (x z : Site d) :
    uconc_kGreenFrom r K n x z = kGreen r K n (z - x) := by
  unfold uconc_kGreenFrom kGreen
  apply Finset.sum_congr rfl
  intro j hj
  exact uconc_kIterFrom_eq_kIter_sub hK j x z

theorem uconc_kGreenFrom_succ {d : ℕ} {r : ℕ}
    {K : Site d → Site d → ℝ} (n : ℕ) (x z : Site d) :
    uconc_kGreenFrom r K (n + 1) x z =
      (if z = x then 1 else 0) +
        ∑ y ∈ boxFinset x r, K x y * uconc_kGreenFrom r K n y z := by
  unfold uconc_kGreenFrom
  rw [Finset.sum_range_succ']
  simp only [uconc_kIterFrom]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

theorem uconc_kOp_abs_sub_le {d : ℕ} {r : ℕ}
    {K : Site d → Site d → ℝ} (hK : IsLatticeKernel r K)
    (f g : Site d → ℝ) (x : Site d) :
    |kOp r K f x - kOp r K g x| ≤
      ∑ y ∈ boxFinset x r, K x y * |f y - g y| := by
  unfold kOp
  have hsum : (∑ x_1 ∈ boxFinset x r, K x x_1 * f x_1) -
        ∑ x_1 ∈ boxFinset x r, K x x_1 * g x_1 =
      ∑ x_1 ∈ boxFinset x r, K x x_1 * (f x_1 - g x_1) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  rw [hsum]
  calc
    |∑ y ∈ boxFinset x r, K x y * (f y - g y)| ≤
        ∑ y ∈ boxFinset x r, |K x y * (f y - g y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y ∈ boxFinset x r, K x y * |f y - g y| := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [abs_mul, abs_of_nonneg (hK.1 x y)]

theorem uconc_kSol_update_le {d : ℕ} {r : ℕ}
    {K : Site d → Site d → ℝ} (hK : IsLatticeKernel r K)
    (η : Site d → ℝ) (z : Site d) (v : ℝ) :
    ∀ n x, |kSol r K η n x - kSol r K (Function.update η z v) n x| ≤
      |η z - v| * uconc_kGreenFrom r K n x z := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [kSol, uconc_kGreenFrom]
  | succ n ih =>
      intro x
      rw [kSol, kSol]
      have hmax := abs_max_sub_max_le_abs
        (η x + kOp r K (kSol r K η n) x)
        (Function.update η z v x + kOp r K (kSol r K (Function.update η z v) n) x) 0
      have hsum := uconc_kOp_abs_sub_le hK
        (kSol r K η n) (kSol r K (Function.update η z v) n) x
      have hδ : |η x - Function.update η z v x| ≤
          |η z - v| * (if z = x then 1 else 0) := by
        by_cases hzx : z = x
        · subst x
          simp
        · have hxz : ¬x = z := fun h => hzx h.symm
          simp [Function.update, hzx, hxz]
      have hgreen : ∀ y ∈ boxFinset x r,
          |kSol r K η n y - kSol r K (Function.update η z v) n y| ≤
            |η z - v| * uconc_kGreenFrom r K n y z := by
        intro y hy
        exact ih y
      have hsum' :
          (∑ y ∈ boxFinset x r, K x y *
              |kSol r K η n y - kSol r K (Function.update η z v) n y|) ≤
            ∑ y ∈ boxFinset x r, K x y *
              (|η z - v| * uconc_kGreenFrom r K n y z) := by
        apply Finset.sum_le_sum
        intro y hy
        exact mul_le_mul_of_nonneg_left (hgreen y hy) (hK.1 x y)
      calc
        |max 0 (η x + kOp r K (kSol r K η n) x) -
            max 0 (Function.update η z v x +
              kOp r K (kSol r K (Function.update η z v) n) x)| ≤
            |(η x + kOp r K (kSol r K η n) x) -
              (Function.update η z v x +
                kOp r K (kSol r K (Function.update η z v) n) x)| := by
          simpa only [max_comm] using hmax
        _ ≤ |η x - Function.update η z v x| +
            |kOp r K (kSol r K η n) x -
              kOp r K (kSol r K (Function.update η z v) n) x| := by
          rw [show (η x + kOp r K (kSol r K η n) x) -
              (Function.update η z v x +
                kOp r K (kSol r K (Function.update η z v) n) x) =
              (η x - Function.update η z v x) +
                (kOp r K (kSol r K η n) x -
                  kOp r K (kSol r K (Function.update η z v) n) x) by ring]
          exact abs_add_le _ _
        _ ≤ |η z - v| * (if z = x then 1 else 0) +
            ∑ y ∈ boxFinset x r, K x y *
              |kSol r K η n y - kSol r K (Function.update η z v) n y| :=
          add_le_add hδ (uconc_kOp_abs_sub_le hK _ _ _)
        _ ≤ |η z - v| * (if z = x then 1 else 0) +
            ∑ y ∈ boxFinset x r, K x y *
              (|η z - v| * uconc_kGreenFrom r K n y z) :=
          add_le_add (le_refl _) hsum'
        _ = |η z - v| * uconc_kGreenFrom r K (n + 1) x z := by
          rw [uconc_kGreenFrom_succ]
          rw [mul_add]
          simp_rw [Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro y hy
          ring

theorem uconc_kSol_update_lipschitz {d : ℕ} {r : ℕ}
    {K : Site d → Site d → ℝ} (hK : IsLatticeKernel r K)
    (η : Site d → ℝ) (z : Site d) (v : ℝ) (n : ℕ) :
    |kSol r K η n 0 - kSol r K (Function.update η z v) n 0| ≤
      kGreen r K n z * |η z - v| := by
  have h := uconc_kSol_update_le hK η z v n 0
  rw [uconc_kGreenFrom_eq_kGreen_sub hK n 0 z] at h
  simpa [mul_comm] using h

theorem uconc_kSol_eq_of_eqOn_box {d : ℕ} {r : ℕ}
    {K : Site d → Site d → ℝ} (_hK : IsLatticeKernel r K)
    {η ξ : Site d → ℝ} (n : ℕ) (x : Site d)
    (heq : ∀ y ∈ boxFinset x (r * n), η y = ξ y) :
    kSol r K η n x = kSol r K ξ n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      have hx : x ∈ boxFinset x (r * (n + 1)) :=
        mem_boxFinset_iff.mpr (fun i => by simp)
      have hηx : η x = ξ x := heq x hx
      have hop : kOp r K (kSol r K η n) x = kOp r K (kSol r K ξ n) x := by
        unfold kOp
        apply Finset.sum_congr rfl
        intro y hy
        rw [ih y]
        intro z hz
        apply heq z
        have h := mem_boxFinset_add hy hz
        simpa [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
      change max 0 (η x + kOp r K (kSol r K η n) x) =
        max 0 (ξ x + kOp r K (kSol r K ξ n) x)
      rw [hηx, hop]

theorem uconc_measurable_kSol_extend {d : ℕ} {r : ℕ}
    {K : Site d → Site d → ℝ} (s : Finset (Site d)) (n : ℕ) (x : Site d) :
    Measurable (fun η : s → ℝ => kSol r K (extendField s η) n x) := by
  induction n generalizing x with
  | zero => exact measurable_const
  | succ n ih =>
      have hcoord : Measurable (fun η : s → ℝ => extendField s η x) := by
        by_cases hx : x ∈ s
        · simpa [extendField, hx] using
            (measurable_pi_apply (⟨x, hx⟩ : s) : Measurable (fun η : s → ℝ => η ⟨x, hx⟩))
        · simp [extendField, hx]
      have hop : Measurable (fun η : s → ℝ =>
          kOp r K (kSol r K (extendField s η) n) x) := by
        unfold kOp
        apply Finset.measurable_sum
        intro y hy
        exact measurable_const.mul (ih y)
      change Measurable (fun η : s → ℝ =>
        max 0 (extendField s η x + kOp r K (kSol r K (extendField s η) n) x))
      exact measurable_const.max (hcoord.add hop)



end Parking.External

-- FROZEN-STATEMENT-BEGIN
/-- Rosenthal-type `L^q` concentration for the lattice recursion, proved rather than assumed. -/
theorem Parking.External.uConcentration : Parking.External.UConcentration
-- FROZEN-STATEMENT-END
:= by
  intro d hd r K hK ν hν θ hθ hexp
  letI : IsProbabilityMeasure ν := hν
  obtain ⟨C, hC, hmain⟩ := Parking.weighted_exp_conc_Lq
    θ (∫ z, Real.exp (θ * |z|) ∂ν) hθ
  refine ⟨C, hC, ?_⟩
  intro n hn q hq
  have hq1 : 1 ≤ q := by linarith
  set s : Finset (Parking.Site d) :=
    LatticeProb.boxFinset (0 : Parking.Site d) (r * n) with hsdef
  have hzero_mem : (0 : Parking.Site d) ∈ s := by
    rw [hsdef, LatticeProb.mem_boxFinset_iff]
    intro i
    simp
    positivity
  have hgreen0 : 1 ≤ Parking.kGreen r K n 0 :=
    Parking.External.uconc_kGreen_one_le hK hn
  have hmeasR : Measurable
      (s.restrict : (Parking.Site d → ℝ) → (s → ℝ)) :=
    measurable_pi_lambda _ fun k => measurable_pi_apply (k : Parking.Site d)
  have hF0 : Measurable
      (fun ζ : s → ℝ => Parking.kSol r K (Parking.extendField s ζ) n 0) :=
    Parking.External.uconc_measurable_kSol_extend s n 0
  set F0 : (s → ℝ) → ℝ :=
    fun ζ => Parking.kSol r K (Parking.extendField s ζ) n 0 with hF0def
  have hF0m : Measurable F0 := by
    simpa only [F0] using hF0
  have hrestrict : ∀ η : Parking.Site d → ℝ,
      Parking.kSol r K η n 0 = F0 (s.restrict η) := by
    intro η
    rw [hF0def]
    symm
    apply Parking.External.uconc_kSol_eq_of_eqOn_box
      hK (K := K) n 0
    intro z hz
    rw [Parking.extendField_restrict s η hz]
  set mu : ℝ := ∫ ζ, F0 ζ ∂(Measure.pi fun _ : s => ν) with hmudef
  have hmean :
      (∫ η, Parking.kSol r K η n 0 ∂(LatticeProb.iidLaw d ν)) = mu := by
    have hcongr :
        (∫ η, Parking.kSol r K η n 0 ∂(LatticeProb.iidLaw d ν)) =
          ∫ η, F0 (s.restrict η) ∂(LatticeProb.iidLaw d ν) :=
      integral_congr_ae (Filter.Eventually.of_forall hrestrict)
    rw [hcongr, hmudef, ← LatticeProb.iidLaw_map_restrict d ν s,
      integral_map hmeasR.aemeasurable hF0m.aestronglyMeasurable]
  set N := Fintype.card s with hNdef
  set e : (Fin N → ℝ) ≃ (s → ℝ) := finEquivIndex s with hedef
  set F' : (Fin N → ℝ) → ℝ := F0 ∘ e with hF'def
  set ℓ' : Fin N → ℝ := fun j =>
    Parking.kGreen r K n ((Fintype.equivFin s).symm j) with hℓ'def
  have hF'm : Measurable F' := by
    rw [hF'def]
    exact hF0m.comp measurable_finEquivIndex
  have hℓ'nonneg : ∀ j, 0 ≤ ℓ' j := by
    intro j
    rw [hℓ'def]
    exact Parking.External.uconc_kGreen_nonneg hK n _
  have hℓ'ne : ∃ j, ℓ' j ≠ 0 := by
    refine ⟨Fintype.equivFin s ⟨0, hzero_mem⟩, ?_⟩
    simp only [hℓ'def, Equiv.symm_apply_apply]
    have hpos : 0 < Parking.kGreen r K n 0 := lt_of_lt_of_le zero_lt_one hgreen0
    exact ne_of_gt hpos
  have hLip' : ∀ (ξ : Fin N → ℝ) (j : Fin N) (v : ℝ),
      |F' ξ - F' (Function.update ξ j v)| ≤ ℓ' j * |ξ j - v| := by
    intro ξ j v
    let i : s := (Fintype.equivFin s).symm j
    have heval : e ξ i = ξ j := by
      rw [hedef, finEquivIndex_apply, Equiv.apply_symm_apply]
    have hupd : e (Function.update ξ j v) =
        Function.update (e ξ) i v := by
      rw [hedef]
      exact finEquivIndex_update ξ j v
    have hbase := Parking.External.uconc_kSol_update_lipschitz
      hK (Parking.extendField s (e ξ)) (i : Parking.Site d) v n
    rw [← Parking.extendField_update (e ξ) i v] at hbase
    rw [hF'def]
    change |F0 (e ξ) - F0 (e (Function.update ξ j v))| ≤ _
    rw [hupd]
    have hi : Parking.extendField s (e ξ) (i : Parking.Site d) = ξ j := by
      rw [Parking.extendField, dif_pos i.property]
      exact heval
    rw [hi] at hbase
    simpa [i, hℓ'def, heval, mul_comm] using hbase
  have hbound := hmain N ν inferInstance hexp le_rfl F' hF'm ℓ'
    hℓ'nonneg hℓ'ne hLip' q hq1
  set μ : Measure (s → ℝ) := Measure.pi (fun _ : s => ν)
  have hmean' : (∫ ξ, F' ξ ∂(Measure.pi fun _ : Fin N => ν)) = mu := by
    rw [hF'def]
    simpa [N, e, μ, hmudef] using
      (integral_finEquivIndex_comp ν F0)
  rw [hmean'] at hbound
  have hpowm : Measurable (fun ζ : s → ℝ => |F0 ζ - mu| ^ q) := by
    exact ((hF0m.sub measurable_const).abs.pow_const q)
  have htarget :
      (∫ η, |Parking.kSol r K η n 0 -
          ∫ η', Parking.kSol r K η' n 0 ∂(LatticeProb.iidLaw d ν)| ^ q
        ∂(LatticeProb.iidLaw d ν)) =
        ∫ ζ, |F0 ζ - mu| ^ q ∂(Measure.pi fun _ : s => ν) := by
    have hcongr :
        (∫ η, |Parking.kSol r K η n 0 -
            ∫ η', Parking.kSol r K η' n 0 ∂(LatticeProb.iidLaw d ν)| ^ q
          ∂(LatticeProb.iidLaw d ν)) =
          ∫ η, |F0 (s.restrict η) - mu| ^ q
            ∂(LatticeProb.iidLaw d ν) := by
      apply integral_congr_ae
      filter_upwards with η
      rw [hrestrict η, hmean]
    rw [hcongr, ← LatticeProb.iidLaw_map_restrict d ν s,
      integral_map hmeasR.aemeasurable hpowm.aestronglyMeasurable]
  have hreindex :
      (∫ ζ, |F0 ζ - mu| ^ q ∂(Measure.pi fun _ : s => ν)) =
        ∫ ξ, |F' ξ - mu| ^ q ∂(Measure.pi fun _ : Fin N => ν) := by
    rw [hF'def]
    exact (integral_finEquivIndex_comp ν
      (fun ζ : s → ℝ => |F0 ζ - mu| ^ q)).symm
  have hnorm2 : Parking.l2Norm (Parking.kGreen r K n) =
      LatticeProb.lTwoNorm ℓ' := by
    unfold Parking.l2Norm LatticeProb.lTwoNorm
    congr 1
    have hzero : ∀ z ∉ s, (Parking.kGreen r K n z) ^ 2 = 0 := by
      intro z hz
      rw [hsdef] at hz
      rw [Parking.External.uconc_kGreen_zero_of_not_mem hK n z hz, zero_pow]
      norm_num
    rw [tsum_eq_sum hzero,
      ← Finset.sum_coe_sort s (fun z => (Parking.kGreen r K n z) ^ 2)]
    refine Fintype.sum_equiv (Fintype.equivFin s)
      (fun i : s => Parking.kGreen r K n (i : Parking.Site d) ^ 2)
      (fun j => ℓ' j ^ 2) (fun i => ?_)
    simp only [hℓ'def, Equiv.symm_apply_apply]
  have hnormInf : Parking.supAbs (Parking.kGreen r K n) =
      LatticeProb.lInfNorm ℓ' := by
    letI : Nonempty s := ⟨⟨0, hzero_mem⟩⟩
    have hNpos : 0 < N := by
      rw [hNdef]
      exact Fintype.card_pos_iff.mpr (by infer_instance)
    letI : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
    letI : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
    unfold Parking.supAbs LatticeProb.lInfNorm
    have hfnn : ∀ z : Parking.Site d, 0 ≤ |Parking.kGreen r K n z| :=
      fun z => abs_nonneg _
    have hfz : ∀ z ∉ s, |Parking.kGreen r K n z| = 0 := by
      intro z hz
      rw [hsdef] at hz
      rw [Parking.External.uconc_kGreen_zero_of_not_mem hK n z hz, abs_zero]
    rw [ciSup_eq_ciSup_subtype_of_forall_not_mem_eq_zero
      hfnn hfz ⟨0, hzero_mem⟩]
    have hbdd1 : BddAbove (Set.range ℓ') := Finite.bddAbove_range _
    have hbdd2 : BddAbove (Set.range (fun i : s =>
        |Parking.kGreen r K n (i : Parking.Site d)|)) := Finite.bddAbove_range _
    refine le_antisymm ?_ ?_
    · refine ciSup_le ?_
      intro i
      have hi : |Parking.kGreen r K n (i : Parking.Site d)| =
          ℓ' (Fintype.equivFin s i) := by
        simp only [hℓ'def, Equiv.symm_apply_apply]
        rw [abs_of_nonneg]
        exact Parking.External.uconc_kGreen_nonneg hK n _
      rw [hi]
      exact le_ciSup hbdd1 _
    · refine ciSup_le ?_
      intro j
      have hj : ℓ' j =
          |Parking.kGreen r K n ((Fintype.equivFin s).symm j : Parking.Site d)| := by
        rw [hℓ'def]
        exact (abs_of_nonneg (Parking.External.uconc_kGreen_nonneg hK n _)).symm
      rw [hj]
      exact le_ciSup hbdd2 _
  rw [htarget, hreindex, hnorm2, hnormInf]
  exact hbound
