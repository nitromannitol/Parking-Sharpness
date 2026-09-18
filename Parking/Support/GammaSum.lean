/-
The sum of `lem:gamma-sum`: what `Γ_m` contributes site by site, and why the
sum over the lattice is finite in every dimension.

Three facts organize it.  The truncated Green function vanishes at distance
`m` from the origin, so `Γ_m` vanishes outside the ball of radius `m` and the
whole sum is a finite sum over the ball of radius `n`.  Inside the ball the
size of `Γ_m(y)` is the square of the gradient of `g_m` across `y`, which is
`C(1+|y|)^{1-d}` in dimension two and above and is computed exactly in
dimension one.  Summing the resulting radial bound against the number of sites
in a shell is what produces `κ_d(n)`.
-/
import Parking.Support.HeatMoments
import Parking.Support.Odometer
import LatticeProb.Graph.Zd
import Parking.Support.Shells
import Parking.External.GreenGradient

noncomputable section

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-! ### The supremum over a bounded set of times -/

theorem iSup_mem_le {n : ℕ} {f : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B) (h : ∀ m ≤ n, f m ≤ B) (m : ℕ) :
    (⨆ _ : m ∈ Set.Iic n, f m) ≤ B := by
  by_cases hm : m ∈ Set.Iic n
  · rw [ciSup_pos hm]
    exact h m hm
  · rw [ciSup_neg hm, Real.sSup_empty]
    exact hB

theorem iSup_Iic_le {n : ℕ} {f : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B) (h : ∀ m ≤ n, f m ≤ B) :
    (⨆ m ∈ Set.Iic n, f m) ≤ B :=
  ciSup_le fun m => iSup_mem_le hB h m

theorem iSup_Iic_nonneg {n : ℕ} {f : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B) (h : ∀ m ≤ n, f m ≤ B) :
    0 ≤ ⨆ m ∈ Set.Iic n, f m := by
  have hbdd : BddAbove (Set.range fun m : ℕ => ⨆ _ : m ∈ Set.Iic n, f m) := by
    refine ⟨B, ?_⟩
    rintro x ⟨m, rfl⟩
    exact iSup_mem_le hB h m
  have hzero : (⨆ _ : n + 1 ∈ Set.Iic n, f (n + 1)) = 0 := by
    rw [ciSup_neg (by simp), Real.sSup_empty]
  calc (0 : ℝ) = ⨆ _ : n + 1 ∈ Set.Iic n, f (n + 1) := hzero.symm
    _ ≤ ⨆ m ∈ Set.Iic n, f m := le_ciSup hbdd (n + 1)

/-! ### Where the truncated Green function lives -/

theorem graphNorm_eq_srw (x : Site d) : graphNorm x = LatticeProb.graphNorm x := rfl

theorem green_eq_zero_of_le {m : ℕ} {x : Site d} (h : m ≤ graphNorm x) : green d m x = 0 := by
  rw [green_eq_srwGreen, LatticeProb.srwGreen]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Finset.mem_range] at hj
  refine LatticeProb.srwHeat_eq_zero_of_lt ?_
  rw [← graphNorm_eq_srw]
  omega

theorem gamma_nonneg (d m : ℕ) (y : Site d) : 0 ≤ gamma d m y := by
  unfold gamma
  refine Finset.sum_nonneg fun z hz => ?_
  have : 0 ≤ kern d y z := by
    unfold kern
    split <;> positivity
  positivity

theorem gamma_eq_zero_of_lt {m : ℕ} {y : Site d} (h : m < graphNorm y) : gamma d m y = 0 := by
  have hz : ∀ z ∈ nbrFinset y, green d m z = 0 := by
    intro z hz
    refine green_eq_zero_of_le ?_
    have hgn : graphNorm y ≤ graphNorm z + 1 := by
      obtain ⟨i, hi | hi⟩ := mem_nbrFinset_iff.mp hz
      · have := LatticeProb.graphNorm_le_succ_of_add_dirVec y ((i, true) : LatticeProb.Dir d)
        rw [LatticeProb.dirVec_eq_unit, ← hi] at this
        exact this
      · have := LatticeProb.graphNorm_le_succ_of_add_dirVec y ((i, false) : LatticeProb.Dir d)
        rw [LatticeProb.dirVec_eq_neg_unit, ← sub_eq_add_neg, ← hi] at this
        exact this
    omega
  have hw : LatticeProb.walkOp (green d m) y = 0 := by
    unfold LatticeProb.walkOp LatticeProb.nbrSum
    have : ∀ i : Fin d, green d m (y + unit i) + green d m (y - unit i) = 0 := by
      intro i
      rw [hz _ (mem_nbrFinset_iff.mpr ⟨i, Or.inl rfl⟩),
        hz _ (mem_nbrFinset_iff.mpr ⟨i, Or.inr rfl⟩)]
      ring
    rw [Finset.sum_congr rfl fun i _ => this i]
    simp
  unfold gamma
  refine Finset.sum_eq_zero fun z hzmem => ?_
  rw [hz z hzmem, hw]
  ring

/-! ### The sum is a finite sum over the ball, read shell by shell -/

theorem sum_gamma_le (n : ℕ) (b : ℕ → ℝ) (hbnn : ∀ k, 0 ≤ b k)
    (hb : ∀ y : Site d, supNorm y ≤ n → ∀ m ≤ n, gamma d m y ≤ b (supNorm y)) :
    Summable (fun y : Site d => ⨆ m ∈ Set.Iic n, gamma d m y) ∧
      ∑' y : Site d, (⨆ m ∈ Set.Iic n, gamma d m y)
        ≤ b 0 + ∑ k ∈ Finset.Icc 1 n, (shellCard d k : ℝ) * b k := by
  have hzero : ∀ y : Site d, y ∉ boxFinset (0 : Site d) n →
      (⨆ m ∈ Set.Iic n, gamma d m y) = 0 := by
    intro y hy
    rw [mem_boxFinset_zero_iff] at hy
    have hgn : n < graphNorm y := lt_of_lt_of_le (by omega) (supNorm_le_graphNorm y)
    have hvanish : ∀ m ≤ n, gamma d m y = 0 := fun m hm =>
      gamma_eq_zero_of_lt (lt_of_le_of_lt hm hgn)
    refine le_antisymm (iSup_Iic_le le_rfl fun m hm => (hvanish m hm).le)
      (iSup_Iic_nonneg (f := fun m => gamma d m y) (B := 0) le_rfl
        fun m hm => (hvanish m hm).le)
  have hsummable : Summable (fun y : Site d => ⨆ m ∈ Set.Iic n, gamma d m y) :=
    summable_of_ne_finset_zero hzero
  refine ⟨hsummable, ?_⟩
  rw [tsum_eq_sum hzero]
  refine le_trans (Finset.sum_le_sum (g := fun y : Site d => b (supNorm y)) ?_) ?_
  · intro y hy
    rw [mem_boxFinset_zero_iff] at hy
    exact iSup_Iic_le (hbnn _) fun m hm => hb y hy m hm
  · exact le_of_eq (sum_box_radial (d := d) b n)

/-! ### The pointwise bound from the gradient, in dimension two and above -/

theorem sum_kern_eq_one (hd : 1 ≤ d) (y : Site d) :
    ∑ z ∈ nbrFinset y, kern d y z = 1 := by
  have hval : ∀ z ∈ nbrFinset y, kern d y z = (2 * (d : ℝ))⁻¹ := by
    intro z hz
    rw [kern, if_pos hz]
  rw [Finset.sum_congr rfl hval, Finset.sum_const, LatticeProb.Graph.Zd.card_nbrFinset,
    nsmul_eq_mul]
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  push_cast
  field_simp

theorem gamma_le_of_gradient (hd : 1 ≤ d) {C : ℝ} (hC : 0 < C) {m : ℕ} {y : Site d}
    (hgrad : ∀ z : Site d, z ∈ nbrFinset y →
      |green d m y - green d m z| ≤ C * (1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ))) :
    gamma d m y ≤ 4 * C ^ 2 * ((1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ))) ^ 2 := by
  set A : ℝ := C * (1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ)) with hA
  have hApos : 0 ≤ A := by
    have : (0 : ℝ) < (1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ)) := by
      refine Real.rpow_pos_of_pos ?_ _
      positivity
    positivity
  have hterm : ∀ z ∈ nbrFinset y,
      kern d y z * (green d m z - LatticeProb.walkOp (green d m) y) ^ 2
        ≤ kern d y z * (2 * A) ^ 2 := by
    intro z hz
    have hdiff : |green d m z - LatticeProb.walkOp (green d m) y| ≤ 2 * A := by
      have hdpos : (0 : ℝ) < 2 * (d : ℝ) := by
        have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
        linarith
      have hgz : |green d m y - green d m z| ≤ A := hgrad z hz
      have hnum : green d m z - LatticeProb.walkOp (green d m) y
          = (∑ i : Fin d, ((green d m z - green d m (y + unit i))
              + (green d m z - green d m (y - unit i)))) / (2 * (d : ℝ)) := by
        have hw : LatticeProb.walkOp (green d m) y
            = (∑ i : Fin d, (green d m (y + unit i) + green d m (y - unit i)))
              / (2 * (d : ℝ)) := rfl
        have hstep : ∑ i : Fin d, ((green d m z - green d m (y + unit i))
              + (green d m z - green d m (y - unit i)))
            = (∑ _i : Fin d, 2 * green d m z)
              - ∑ i : Fin d, (green d m (y + unit i) + green d m (y - unit i)) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        have hconst : (∑ _i : Fin d, 2 * green d m z) = 2 * (d : ℝ) * green d m z := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp
          ring
        rw [hw, hstep, hconst]
        field_simp
      have hbound : |∑ i : Fin d, ((green d m z - green d m (y + unit i))
          + (green d m z - green d m (y - unit i)))| ≤ 2 * (d : ℝ) * (2 * A) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        have hterm : ∀ i : Fin d, |(green d m z - green d m (y + unit i))
            + (green d m z - green d m (y - unit i))| ≤ 2 * (2 * A) := by
          intro i
          have h1 : |green d m y - green d m (y + unit i)| ≤ A :=
            hgrad _ (mem_nbrFinset_iff.mpr ⟨i, Or.inl rfl⟩)
          have h2 : |green d m y - green d m (y - unit i)| ≤ A :=
            hgrad _ (mem_nbrFinset_iff.mpr ⟨i, Or.inr rfl⟩)
          have e1 : |green d m z - green d m (y + unit i)| ≤ 2 * A := by
            calc |green d m z - green d m (y + unit i)|
                ≤ |green d m z - green d m y| + |green d m y - green d m (y + unit i)| :=
                  abs_sub_le _ _ _
              _ ≤ A + A := by
                  rw [abs_sub_comm (green d m z)] at *
                  linarith
              _ = 2 * A := by ring
          have e2 : |green d m z - green d m (y - unit i)| ≤ 2 * A := by
            calc |green d m z - green d m (y - unit i)|
                ≤ |green d m z - green d m y| + |green d m y - green d m (y - unit i)| :=
                  abs_sub_le _ _ _
              _ ≤ A + A := by
                  rw [abs_sub_comm (green d m z)] at *
                  linarith
              _ = 2 * A := by ring
          calc |(green d m z - green d m (y + unit i))
                + (green d m z - green d m (y - unit i))|
              ≤ |green d m z - green d m (y + unit i)|
                + |green d m z - green d m (y - unit i)| := abs_add_le _ _
            _ ≤ 2 * A + 2 * A := by linarith
            _ = 2 * (2 * A) := by ring
        calc ∑ i : Fin d, |(green d m z - green d m (y + unit i))
              + (green d m z - green d m (y - unit i))|
            ≤ ∑ _i : Fin d, 2 * (2 * A) := Finset.sum_le_sum fun i _ => hterm i
          _ = (d : ℝ) * (2 * (2 * A)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
              simp
          _ = 2 * (d : ℝ) * (2 * A) := by ring
      rw [hnum, abs_div, abs_of_pos hdpos]
      rw [div_le_iff₀ hdpos]
      calc |∑ i : Fin d, ((green d m z - green d m (y + unit i))
            + (green d m z - green d m (y - unit i)))| ≤ 2 * (d : ℝ) * (2 * A) := hbound
        _ = 2 * A * (2 * (d : ℝ)) := by ring
    have hsq : (green d m z - LatticeProb.walkOp (green d m) y) ^ 2 ≤ (2 * A) ^ 2 := by
      have h0 : 0 ≤ 2 * A := by linarith
      nlinarith [abs_nonneg (green d m z - LatticeProb.walkOp (green d m) y),
        sq_abs (green d m z - LatticeProb.walkOp (green d m) y)]
    have hk : 0 ≤ kern d y z := by
      unfold kern
      split <;> positivity
    exact mul_le_mul_of_nonneg_left hsq hk
  calc gamma d m y ≤ ∑ z ∈ nbrFinset y, kern d y z * (2 * A) ^ 2 :=
        Finset.sum_le_sum hterm
    _ = (∑ z ∈ nbrFinset y, kern d y z) * (2 * A) ^ 2 := by rw [Finset.sum_mul]
    _ = (2 * A) ^ 2 := by rw [sum_kern_eq_one hd, one_mul]
    _ = 4 * C ^ 2 * ((1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ))) ^ 2 := by rw [hA]; ring

/-! ### Dimension one: the gradient is the tail of the kernel -/

theorem green_zero (d : ℕ) (x : Site d) : green d 0 x = 0 := by
  simp [green]

theorem gamma_zero (d : ℕ) (y : Site d) : gamma d 0 y = 0 := by
  have hw : LatticeProb.walkOp (green d 0) y = 0 := by
    unfold LatticeProb.walkOp LatticeProb.nbrSum
    simp [green_zero]
  unfold gamma
  refine Finset.sum_eq_zero fun z _ => ?_
  rw [green_zero, hw]
  ring

theorem site_one_eq (y : Site 1) : y = ![y 0] := by
  funext i
  fin_cases i
  rfl

theorem supNorm_one (c : ℤ) : supNorm (![c] : Site 1) = c.natAbs := by
  unfold supNorm
  rw [show (Finset.univ : Finset (Fin 1)) = {0} from rfl]
  simp

theorem site_one_add_unit (c : ℤ) : (![c] : Site 1) + unit 0 = ![c + 1] := by
  funext i
  fin_cases i
  simp [LatticeProb.unit]

theorem site_one_sub_unit (c : ℤ) : (![c] : Site 1) - unit 0 = ![c - 1] := by
  funext i
  fin_cases i
  simp [LatticeProb.unit, sub_eq_add_neg]

theorem green_one_sub' (m : ℕ) {c : ℤ} (hc : 0 ≤ c) :
    green 1 m ![c] - green 1 m ![c + 1] = 2 * LatticeProb.srwTail m c := by
  rw [green_eq_srwGreen, green_eq_srwGreen]
  exact LatticeProb.srwGreen_one_sub m hc

/-- In dimension one `Γ_m(y)` is the square of the sum of the two tails of the
kernel across `y`. -/
theorem gamma_one_eq_tail (m : ℕ) {c : ℤ} (hc : 1 ≤ c) :
    gamma 1 m ![c] = (LatticeProb.srwTail m (c - 1) + LatticeProb.srwTail m c) ^ 2 := by
  have h1 : green 1 m ![c - 1] - green 1 m ![c] = 2 * LatticeProb.srwTail m (c - 1) := by
    have := green_one_sub' m (c := c - 1) (by omega)
    rwa [show c - 1 + 1 = c by ring] at this
  have h2 : green 1 m ![c] - green 1 m ![c + 1] = 2 * LatticeProb.srwTail m c :=
    green_one_sub' m (by omega)
  rw [gamma_one, site_one_add_unit, site_one_sub_unit]
  have : green 1 m ![c + 1] - green 1 m ![c - 1]
      = -(2 * LatticeProb.srwTail m (c - 1) + 2 * LatticeProb.srwTail m c) := by
    linarith
  rw [this]
  ring

/-- The pointwise bound of Step 3 of `lem:gamma-sum`. -/
theorem gamma_one_le {m n : ℕ} (hm : m ≤ n) (c : ℤ) :
    gamma 1 m ![c] ≤ 4 * (min 1 ((n : ℝ) / ((c.natAbs : ℝ)) ^ 2)) ^ 2 := by
  have hmain : ∀ e : ℤ, 1 ≤ e →
      gamma 1 m ![e] ≤ 4 * (min 1 ((n : ℝ) / ((e.natAbs : ℝ)) ^ 2)) ^ 2 := by
    intro e he
    have hcast : ((e.natAbs : ℕ) : ℝ) = (e : ℝ) := by
      have : e.natAbs = e.toNat := by omega
      rw [this]
      have : ((e.toNat : ℕ) : ℤ) = e := by omega
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
    have hepos : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
    have hbound : ∀ a : ℤ, 0 ≤ a → (e : ℝ) ≤ (a : ℝ) + 1 →
        LatticeProb.srwTail m a ≤ min 1 ((n : ℝ) / ((e.natAbs : ℝ)) ^ 2) := by
      intro a ha hae
      refine le_min (Parking.srwTail_le_one m a) ?_
      refine le_trans (Parking.srwTail_le_sq m ha) ?_
      rw [hcast]
      have hden : (0 : ℝ) < (e : ℝ) ^ 2 := by nlinarith
      have hden' : (0 : ℝ) < ((a : ℝ) + 1) ^ 2 := by nlinarith
      rw [div_le_div_iff₀ hden' hden]
      have hmn : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm
      have hmnn : (0 : ℝ) ≤ (m : ℝ) := by positivity
      have hea : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
      have he2 : (e : ℝ) ^ 2 ≤ ((a : ℝ) + 1) ^ 2 := by nlinarith
      have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
      exact mul_le_mul hmn he2 (by positivity) hnn
    have hA : LatticeProb.srwTail m (e - 1) ≤ min 1 ((n : ℝ) / ((e.natAbs : ℝ)) ^ 2) := by
      refine hbound (e - 1) (by omega) ?_
      push_cast
      linarith
    have hB : LatticeProb.srwTail m e ≤ min 1 ((n : ℝ) / ((e.natAbs : ℝ)) ^ 2) := by
      refine hbound e (by omega) ?_
      linarith
    have hAnn : 0 ≤ LatticeProb.srwTail m (e - 1) := by
      rw [LatticeProb.srwTail]
      exact Finset.sum_nonneg fun k _ => LatticeProb.srwHeat_nonneg _ _
    have hBnn : 0 ≤ LatticeProb.srwTail m e := by
      rw [LatticeProb.srwTail]
      exact Finset.sum_nonneg fun k _ => LatticeProb.srwHeat_nonneg _ _
    rw [gamma_one_eq_tail m he]
    nlinarith [hA, hB, hAnn, hBnn]
  rcases lt_trichotomy c 0 with hc | hc | hc
  · have hneg : gamma 1 m ![c] = gamma 1 m ![-c] := by
      rw [gamma_one, gamma_one, site_one_add_unit, site_one_sub_unit, site_one_add_unit,
        site_one_sub_unit]
      have e1 : green 1 m ![-c + 1] = green 1 m ![c - 1] := by
        rw [show (![-c + 1] : Site 1) = -(![c - 1] : Site 1) by
          funext i; fin_cases i; simp; ring]
        exact green_neg 1 m _
      have e2 : green 1 m ![-c - 1] = green 1 m ![c + 1] := by
        rw [show (![-c - 1] : Site 1) = -(![c + 1] : Site 1) by
          funext i; fin_cases i; simp; ring]
        exact green_neg 1 m _
      rw [e1, e2]
      ring
    have hnat : (-c).natAbs = c.natAbs := by omega
    rw [hneg, ← hnat]
    exact hmain (-c) (by omega)
  · subst hc
    have : (![(0 : ℤ)] : Site 1) = 0 := by
      funext i
      fin_cases i
      rfl
    rw [this, gamma_one_zero]
    positivity
  · exact hmain c (by omega)

/-! ### The radial bound is antitone, and the shell arithmetic -/

theorem rpow_radial_antitone (hd : 1 ≤ d) {s g : ℕ} (h : s ≤ g) :
    (1 + (g : ℝ)) ^ (1 - (d : ℝ)) ≤ (1 + (s : ℝ)) ^ (1 - (d : ℝ)) := by
  have hs : (0 : ℝ) < 1 + (s : ℝ) := by positivity
  have hg : (0 : ℝ) < 1 + (g : ℝ) := by positivity
  have hsg : (1 : ℝ) + (s : ℝ) ≤ 1 + (g : ℝ) := by
    have : (s : ℝ) ≤ (g : ℝ) := by exact_mod_cast h
    linarith
  have hexp : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hpow : (1 + (s : ℝ)) ^ ((d : ℝ) - 1) ≤ (1 + (g : ℝ)) ^ ((d : ℝ) - 1) :=
    Real.rpow_le_rpow (le_of_lt hs) hsg hexp
  have hneg : ∀ x : ℝ, 0 < x → x ^ (1 - (d : ℝ)) = (x ^ ((d : ℝ) - 1))⁻¹ := by
    intro x hx
    rw [show (1 : ℝ) - (d : ℝ) = -((d : ℝ) - 1) by ring, Real.rpow_neg (le_of_lt hx)]
  rw [hneg _ hg, hneg _ hs]
  exact inv_anti₀ (Real.rpow_pos_of_pos hs _) hpow

theorem rpow_shell_combine (hd : 1 ≤ d) (k : ℕ) :
    ((1 + (k : ℝ)) ^ (d - 1)) * (((1 + (k : ℝ)) ^ (1 - (d : ℝ))) ^ 2)
      = (1 + (k : ℝ)) ^ (1 - (d : ℝ)) := by
  have hx : (0 : ℝ) < 1 + (k : ℝ) := by positivity
  have h1 : ((1 + (k : ℝ)) ^ (d - 1)) = (1 + (k : ℝ)) ^ ((d : ℝ) - 1) := by
    rw [← Real.rpow_natCast (1 + (k : ℝ)) (d - 1)]
    congr 1
    have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      have : (d - 1 : ℕ) + 1 = d := by omega
      have := congrArg (fun m : ℕ => (m : ℝ)) this
      push_cast at this
      linarith
    exact this
  have h2 : (((1 + (k : ℝ)) ^ (1 - (d : ℝ))) ^ 2) = (1 + (k : ℝ)) ^ ((1 - (d : ℝ)) * 2) := by
    rw [← Real.rpow_natCast ((1 + (k : ℝ)) ^ (1 - (d : ℝ))) 2, ← Real.rpow_mul (le_of_lt hx)]
    norm_num
  rw [h1, h2, ← Real.rpow_add hx]
  congr 1
  ring

theorem shellCard_one (k : ℕ) (hk : 1 ≤ k) : shellCard 1 k = 2 := by
  rw [shellCard]
  simp only [pow_one]
  omega

/-! ### The lemma -/

theorem gamma_sum_of_gradient (d : ℕ) (hd : 1 ≤ d)
    (hgrad : 2 ≤ d → Parking.External.GreenGradient d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      Summable (fun y : Site d => ⨆ m ∈ Set.Iic n, gamma d m y) ∧
        ∑' y : Site d, (⨆ m ∈ Set.Iic n, gamma d m y) ≤ C * kappa d n := by
  rcases Nat.lt_or_ge d 2 with hlt | hge
  · -- dimension one
    have hd1 : d = 1 := by omega
    subst hd1
    refine ⟨40, by norm_num, fun n hn => ?_⟩
    set b : ℕ → ℝ := fun k => 4 * (min 1 ((n : ℝ) / (k : ℝ) ^ 2)) ^ 2 with hbdef
    have hbnn : ∀ k, 0 ≤ b k := by
      intro k
      have : 0 ≤ min 1 ((n : ℝ) / (k : ℝ) ^ 2) := le_min (by norm_num) (by positivity)
      rw [hbdef]
      positivity
    have hb : ∀ y : Site 1, supNorm y ≤ n → ∀ m ≤ n, gamma 1 m y ≤ b (supNorm y) := by
      intro y _ m hm
      have hy : y = ![y 0] := site_one_eq y
      rw [hy, supNorm_one, hbdef]
      exact gamma_one_le hm (y 0)
    obtain ⟨hsum, hle⟩ := sum_gamma_le (d := 1) n b hbnn hb
    refine ⟨hsum, le_trans hle ?_⟩
    have hb0 : b 0 = 0 := by
      rw [hbdef]
      norm_num
    have hshell : ∑ k ∈ Finset.Icc 1 n, (shellCard 1 k : ℝ) * b k
        = 8 * ∑ k ∈ Finset.Icc 1 n, (min 1 ((n : ℝ) / (k : ℝ) ^ 2)) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_Icc] at hk
      rw [shellCard_one k hk.1, hbdef]
      push_cast
      ring
    rw [hb0, hshell, zero_add]
    have hkappa : kappa 1 n = Real.sqrt (n : ℝ) := by
      rw [kappa, if_pos rfl, Real.sqrt_eq_rpow]
    rw [hkappa]
    have := sum_min_le_sqrt hn
    linarith
  · -- dimension two and above
    obtain ⟨C₀, hC₀pos, hC₀⟩ := hgrad hge
    set K : ℝ := 8 * C₀ ^ 2 * (d : ℝ) * 2 ^ (d - 1) with hK
    have hKnn : 0 ≤ K := by
      rw [hK]
      positivity
    refine ⟨4 * C₀ ^ 2 + K + 1, by positivity, fun n hn => ?_⟩
    set b : ℕ → ℝ := fun k => 4 * C₀ ^ 2 * ((1 + (k : ℝ)) ^ (1 - (d : ℝ))) ^ 2 with hbdef
    have hbnn : ∀ k, 0 ≤ b k := by
      intro k
      rw [hbdef]
      positivity
    have hb : ∀ y : Site d, supNorm y ≤ n → ∀ m ≤ n, gamma d m y ≤ b (supNorm y) := by
      intro y _ m _
      rcases Nat.eq_zero_or_pos m with rfl | hm1
      · rw [gamma_zero]
        exact hbnn _
      · have hgy := gamma_le_of_gradient (d := d) hd hC₀pos
          (m := m) (y := y) (fun z hz => hC₀ m hm1 y z hz)
        refine le_trans hgy ?_
        have hmono : (1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ))
            ≤ (1 + (supNorm y : ℝ)) ^ (1 - (d : ℝ)) :=
          rpow_radial_antitone hd (supNorm_le_graphNorm y)
        have hpos : (0 : ℝ) ≤ (1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ)) :=
          le_of_lt (Real.rpow_pos_of_pos (by positivity) _)
        rw [hbdef]
        have hsq : ((1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ))) ^ 2
            ≤ ((1 + (supNorm y : ℝ)) ^ (1 - (d : ℝ))) ^ 2 := by
          nlinarith
        nlinarith [sq_nonneg C₀]
    obtain ⟨hsum, hle⟩ := sum_gamma_le (d := d) n b hbnn hb
    refine ⟨hsum, le_trans hle ?_⟩
    have hb0 : b 0 = 4 * C₀ ^ 2 := by
      rw [hbdef]
      norm_num
    have hterm : ∀ k ∈ Finset.Icc 1 n,
        (shellCard d k : ℝ) * b k ≤ K * (1 + (k : ℝ)) ^ (1 - (d : ℝ)) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have h1 : (shellCard d k : ℝ) * b k ≤ (2 * (d : ℝ) * (2 * (k : ℝ) + 1) ^ (d - 1)) * b k :=
        mul_le_mul_of_nonneg_right (shellCard_le d hk.1) (hbnn k)
      have h2 : (2 * (k : ℝ) + 1) ^ (d - 1) ≤ 2 ^ (d - 1) * (1 + (k : ℝ)) ^ (d - 1) := by
        rw [← mul_pow]
        refine pow_le_pow_left₀ (by positivity) ?_ _
        linarith
      have hbk : 0 ≤ b k := hbnn k
      have h3 : (2 * (d : ℝ) * (2 * (k : ℝ) + 1) ^ (d - 1)) * b k
          ≤ (2 * (d : ℝ) * (2 ^ (d - 1) * (1 + (k : ℝ)) ^ (d - 1))) * b k := by
        refine mul_le_mul_of_nonneg_right ?_ hbk
        have hdnn : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left h2 hdnn
      have h4 : (2 * (d : ℝ) * (2 ^ (d - 1) * (1 + (k : ℝ)) ^ (d - 1))) * b k
          = K * (1 + (k : ℝ)) ^ (1 - (d : ℝ)) := by
        rw [hbdef, hK, ← rpow_shell_combine hd k]
        ring
      linarith
    have hsum_shell : ∑ k ∈ Finset.Icc 1 n, (shellCard d k : ℝ) * b k
        ≤ ∑ k ∈ Finset.Icc 1 n, K * (1 + (k : ℝ)) ^ (1 - (d : ℝ)) :=
      Finset.sum_le_sum hterm
    rcases eq_or_lt_of_le hge with hd2 | hd3
    · -- dimension two
      have hdval : d = 2 := hd2.symm
      subst hdval
      have hpow : ∀ k : ℕ, (1 + (k : ℝ)) ^ (1 - ((2 : ℕ) : ℝ)) = 1 / ((k : ℝ) + 1) := by
        intro k
        have hx : (0 : ℝ) < 1 + (k : ℝ) := by positivity
        rw [show (1 : ℝ) - ((2 : ℕ) : ℝ) = -1 by push_cast; ring, Real.rpow_neg_one]
        rw [one_div]
        congr 1
        ring
      have hlog : ∑ k ∈ Finset.Icc 1 n, K * (1 + (k : ℝ)) ^ (1 - ((2 : ℕ) : ℝ))
          ≤ K * Real.log ((n : ℝ) + 1) := by
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ hKnn
        refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => hpow k)) ?_
        exact sum_inv_succ_le_log n
      have hkappa : kappa 2 n = Real.log ((n : ℝ) + 2) := by
        rw [kappa]
        norm_num
      have hlogmono : Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      have hlogone : (1 : ℝ) ≤ Real.log ((n : ℝ) + 2) := by
        have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        refine (Real.le_log_iff_exp_le (by linarith)).mpr ?_
        have := Real.exp_one_lt_d9
        linarith
      rw [hkappa, hb0]
      have hC0nn : (0 : ℝ) ≤ 4 * C₀ ^ 2 := by positivity
      nlinarith [hsum_shell, hlog, hlogmono, hlogone, hKnn]
    · -- dimension three and above
      have hpow : ∀ k : ℕ, (1 + (k : ℝ)) ^ (1 - (d : ℝ)) ≤ 1 / ((k : ℝ) + 1) ^ 2 := by
        intro k
        have hx : (1 : ℝ) ≤ 1 + (k : ℝ) := by
          have : (0 : ℝ) ≤ (k : ℝ) := by positivity
          linarith
        have hexp : (1 : ℝ) - (d : ℝ) ≤ -2 := by
          have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd3
          linarith
        have hle : (1 + (k : ℝ)) ^ (1 - (d : ℝ)) ≤ (1 + (k : ℝ)) ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx hexp
        have hval : (1 + (k : ℝ)) ^ (-2 : ℝ) = 1 / ((k : ℝ) + 1) ^ 2 := by
          rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
            Real.rpow_neg (by positivity), Real.rpow_natCast, one_div]
          congr 2
          ring
        rw [hval] at hle
        exact hle
      have hone : ∑ k ∈ Finset.Icc 1 n, K * (1 + (k : ℝ)) ^ (1 - (d : ℝ)) ≤ K := by
        rw [← Finset.mul_sum]
        calc K * ∑ k ∈ Finset.Icc 1 n, (1 + (k : ℝ)) ^ (1 - (d : ℝ))
            ≤ K * ∑ k ∈ Finset.Icc 1 n, 1 / ((k : ℝ) + 1) ^ 2 :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hpow k) hKnn
          _ ≤ K * 1 := mul_le_mul_of_nonneg_left (sum_inv_sq_succ_le_one n) hKnn
          _ = K := by ring
      have hkappa : kappa d n = 1 := by
        rw [kappa, if_neg (by omega), if_neg (by omega)]
      rw [hkappa, hb0, mul_one]
      linarith

end Parking

end
