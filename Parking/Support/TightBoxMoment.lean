/-
The `p`-th moment of the rescaled oriented reward field, UNIFORM over every
point of the box (not just the lower corner `(0, -2A)`), and over the scale
`n ≥ 1`.

`Parking.Support.TightEquicont.exists_orientedBoxReward_single_moment` proves
this bound only at the corner `![0, -(2 * A)]`; its own proof never uses the
corner's SPATIAL coordinate (`Parking.exists_orientedGridReward_single_moment`
is independent of the spatial grid index `j`, and
`Parking.exists_orientedBoxReward_cell_moment` is independent of the box
point's spatial coordinate too), only the fact that the TIME coordinate is
nonnegative.  So the identical proof, read at an arbitrary `u` with
`0 ≤ u 0` in place of the corner, gives the moment bound at EVERY point of
the box, with the SAME constant (no dependence on the cutoff level `A` at
all, since the corner's own bound never depended on it).

This is what lets `happ` (`parking.tex:3199-3203`) bound the box-clamped
reward `G_n` at a single RANDOM point (the walk's own clamped position at
a stopping time) via Cauchy–Schwarz against this uniform second moment,
rather than against the supremum of `G_n` over the whole box: for a FIXED
random point `z` of the walk (independent of the scenery `η`), Tonelli gives
`E_η[G_n(z)^2] ≤ M` directly from this lemma, since the bound holds at
EVERY `z` in the box uniformly.
-/
import Parking.Support.TightEquicont

open MeasureTheory LatticeProb

noncomputable section
namespace Parking

/-- **The `p`-th moment of the box reward is uniform over every point of the
box**, not just the lower corner: the same constant bounds `E|G_n(u)|^p` for
every `u` with `0 ≤ u 0`, and every scale `n ≥ 1`. -/
theorem exists_orientedBoxReward_moment (ν : Measure ℤ) (hν : CriticalLaw ν)
    (p : ℝ) (hp : 2 ≤ p) (T : ℝ) (hT : 0 ≤ T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : ℕ) (_hn : 1 ≤ n) (u : Fin 2 → ℝ), 0 ≤ u 0 →
      Integrable (fun η : Site 2 → ℝ => |orientedBoxReward T n η u| ^ p)
        (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, |orientedBoxReward T n η u| ^ p
          ∂(iidLaw 2 (realLaw ν))) ≤
        M := by
  obtain ⟨C₂, hC₂, hsingle⟩ := exists_orientedGridReward_single_moment ν hν p hp
  obtain ⟨C₃, hC₃, hcell⟩ := exists_orientedBoxReward_cell_moment ν hν p hp
  have hp1 : (1 : ℝ) ≤ p := le_trans (by norm_num) hp
  have hp2 : (0 : ℝ) ≤ p / 2 := by linarith
  have hC2X : (0 : ℝ) ≤ C₂ * (Real.sqrt T + 1 / 2) :=
    mul_nonneg hC₂.le (add_nonneg (Real.sqrt_nonneg _) (by norm_num))
  refine ⟨2 ^ p * (4 ^ (p + 1) * (C₃ * 5) ^ (p / 2) + (C₂ * (Real.sqrt T + 1 / 2)) ^ (p / 2)),
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (add_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.rpow_nonneg (mul_nonneg hC₃.le (by norm_num)) _))
        (Real.rpow_nonneg hC2X _)),
    fun n hn u hu0 => ?_⟩
  obtain ⟨hcellInt, hcellBound⟩ := hcell T n u hu0
  obtain ⟨hsingleInt, hsingleBound⟩ := hsingle n ⌊(n : ℝ) * T⌋₊ ⌊(n : ℝ) * u 0⌋
    ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋
  have hn1ℝ : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsn : (1 : ℝ) ≤ Real.sqrt n := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt hn1ℝ
  have hNT : ((⌊(n : ℝ) * T⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) * T :=
    toNat_floor_le (mul_nonneg (Nat.cast_nonneg n) hT)
  have hbrack : Real.sqrt ((⌊(n : ℝ) * T⌋₊ : ℕ) : ℝ) + 1 / 2 ≤
      Real.sqrt n * (Real.sqrt T + 1 / 2) := by
    have h1 : Real.sqrt ((⌊(n : ℝ) * T⌋₊ : ℕ) : ℝ) ≤ Real.sqrt n * Real.sqrt T := by
      calc Real.sqrt ((⌊(n : ℝ) * T⌋₊ : ℕ) : ℝ) ≤ Real.sqrt ((n : ℝ) * T) :=
            Real.sqrt_le_sqrt hNT
        _ = Real.sqrt n * Real.sqrt T := Real.sqrt_mul (Nat.cast_nonneg n) _
    have h2 : (1 / 2 : ℝ) ≤ Real.sqrt n * (1 / 2) := by
      calc (1 / 2 : ℝ) = 1 * (1 / 2) := (one_mul _).symm
        _ ≤ Real.sqrt n * (1 / 2) := mul_le_mul_of_nonneg_right hsn (by norm_num)
    have e : Real.sqrt n * (Real.sqrt T + 1 / 2) =
        Real.sqrt n * Real.sqrt T + Real.sqrt n * (1 / 2) := by ring
    rw [e]
    exact add_le_add h1 h2
  have hsqrtN : Real.sqrt (((⌊(n : ℝ) * T⌋₊ - ⌊(n : ℝ) * u 0⌋.toNat : ℕ) : ℝ)) ≤
      Real.sqrt ((⌊(n : ℝ) * T⌋₊ : ℕ) : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le _ _)
  have hsqrtnpow : (Real.sqrt n) ^ (p / 2) = (n : ℝ) ^ (p / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg n),
      show (1 : ℝ) / 2 * (p / 2) = p / 4 by ring]
  have hVb : (∫ η : Site 2 → ℝ, |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
        ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋| ^ p ∂(iidLaw 2 (realLaw ν))) ≤
      (C₂ * (Real.sqrt T + 1 / 2)) ^ (p / 2) := by
    have hb0 : (0 : ℝ) ≤ C₂ * (Real.sqrt
        (((⌊(n : ℝ) * T⌋₊ - ⌊(n : ℝ) * u 0⌋.toNat : ℕ) : ℝ)) + 1 / 2) :=
      mul_nonneg hC₂.le (add_nonneg (Real.sqrt_nonneg _) (by norm_num))
    calc (∫ η : Site 2 → ℝ, |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
          ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋| ^ p ∂(iidLaw 2 (realLaw ν)))
        ≤ (C₂ * (Real.sqrt (((⌊(n : ℝ) * T⌋₊ - ⌊(n : ℝ) * u 0⌋.toNat : ℕ) : ℝ)) + 1 / 2)) ^
            (p / 2) * (n : ℝ) ^ (-(p / 4)) := hsingleBound
      _ ≤ (C₂ * (Real.sqrt n * (Real.sqrt T + 1 / 2))) ^ (p / 2) *
            (n : ℝ) ^ (-(p / 4)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          exact Real.rpow_le_rpow hb0
            (mul_le_mul_of_nonneg_left (by linarith [hsqrtN, hbrack]) hC₂.le) hp2
      _ = (C₂ * (Real.sqrt T + 1 / 2)) ^ (p / 2) := by
          have e : C₂ * (Real.sqrt n * (Real.sqrt T + 1 / 2)) =
              (C₂ * (Real.sqrt T + 1 / 2)) * Real.sqrt n := by ring
          rw [e, Real.mul_rpow hC2X (Real.sqrt_nonneg _), mul_assoc, hsqrtnpow,
            rpow_quarter_mul_rpow_neg_quarter n hn p, mul_one]
  have hpoint : ∀ η : Site 2 → ℝ, |orientedBoxReward T n η u| ^ p ≤
      2 ^ p * (|orientedBoxReward T n η u - orientedGridReward n ⌊(n : ℝ) * T⌋₊ η
          ⌊(n : ℝ) * u 0⌋ ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋| ^ p +
        |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
          ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋| ^ p) := by
    intro η
    have e : orientedBoxReward T n η u = (orientedBoxReward T n η u -
        orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
          ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋) +
      orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
        ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ := (sub_add_cancel _ _).symm
    conv_lhs => rw [e]
    exact abs_add_rpow_le _ _ _ hp1
  have hgInt : Integrable (fun η : Site 2 → ℝ =>
      2 ^ p * (|orientedBoxReward T n η u - orientedGridReward n ⌊(n : ℝ) * T⌋₊ η
          ⌊(n : ℝ) * u 0⌋ ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋| ^ p +
        |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
          ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋| ^ p)) (iidLaw 2 (realLaw ν)) :=
    (hcellInt.add hsingleInt).const_mul _
  have hfMeas : Measurable fun η : Site 2 → ℝ => |orientedBoxReward T n η u| ^ p :=
    measurable_abs_rpow (measurable_orientedBoxReward T n u) p
  have hfInt : Integrable (fun η : Site 2 → ℝ => |orientedBoxReward T n η u| ^ p)
      (iidLaw 2 (realLaw ν)) :=
    hgInt.mono' hfMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun η => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact hpoint η)
  have hnp : (n : ℝ) ^ (-(p / 4)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1ℝ (by linarith)
  have hcellBound2 : (∫ η : Site 2 → ℝ, |orientedBoxReward T n η u -
        orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
          ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋| ^ p ∂(iidLaw 2 (realLaw ν))) ≤
      4 ^ (p + 1) * (C₃ * 5) ^ (p / 2) := by
    refine le_trans hcellBound ?_
    have h0 : (0 : ℝ) ≤ 4 ^ (p + 1) * (C₃ * 5) ^ (p / 2) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.rpow_nonneg (mul_nonneg hC₃.le (by norm_num)) _)
    calc 4 ^ (p + 1) * ((C₃ * 5) ^ (p / 2) * (n : ℝ) ^ (-(p / 4)))
        = (4 ^ (p + 1) * (C₃ * 5) ^ (p / 2)) * (n : ℝ) ^ (-(p / 4)) := by ring
      _ ≤ (4 ^ (p + 1) * (C₃ * 5) ^ (p / 2)) * 1 :=
          mul_le_mul_of_nonneg_left hnp h0
      _ = 4 ^ (p + 1) * (C₃ * 5) ^ (p / 2) := mul_one _
  refine ⟨hfInt, ?_⟩
  calc ∫ η : Site 2 → ℝ, |orientedBoxReward T n η u| ^ p ∂(iidLaw 2 (realLaw ν))
      ≤ ∫ η : Site 2 → ℝ, 2 ^ p * (|orientedBoxReward T n η u -
            orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
              ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋| ^ p +
          |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
            ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋| ^ p) ∂(iidLaw 2 (realLaw ν)) :=
        integral_mono_ae hfInt hgInt (Filter.Eventually.of_forall hpoint)
    _ = 2 ^ p * ((∫ η : Site 2 → ℝ, |orientedBoxReward T n η u -
            orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
              ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋| ^ p ∂(iidLaw 2 (realLaw ν))) +
          (∫ η : Site 2 → ℝ, |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
              ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋| ^ p ∂(iidLaw 2 (realLaw ν)))) := by
        rw [integral_const_mul, integral_add]
        · exact hcellInt
        · exact hsingleInt
    _ ≤ 2 ^ p * (4 ^ (p + 1) * (C₃ * 5) ^ (p / 2) +
          (C₂ * (Real.sqrt T + 1 / 2)) ^ (p / 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add hcellBound2 hVb)
          (Real.rpow_nonneg (by norm_num) _)


end Parking
end
