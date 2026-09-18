/-
Equicontinuity in probability and uniform boundedness of the rescaled
oriented reward field on the box (`parking.tex:3192-3203`).

The uniform Kolmogorov moment bound of `Parking.Support.TightKolmogorov`,

  `E|G_n(u) - G_n(u')|^p ≤ M (dist u u')^{p/4}`,   `p/4 > 2`,

feeds the box form of the Kolmogorov–Chentsov theorem
(`LatticeProb.kolmogorovModulusPi`, `LatticeProb.kolmogorovBoundPi`) and gives,
uniformly in the scale `n`:

- a common modulus of continuity in probability: for every `ε η > 0` there is
  `δ > 0` such that with probability at least `1 - ε` the field `G_n` varies
  by at most `η` between any two points of the box at distance less than `δ`;
- a common bound in probability: for every `ε > 0` there is `B` such that
  with probability at least `1 - ε` the field `G_n` is bounded by `B` on the
  box.  This second clause also needs the single-point moment of `G_n` at the
  lower corner `(0, -2A)`, which the remaining-horizon single-point bound
  supplies.
-/
import Parking.Support.TightKolmogorov
import LatticeProb.Prob.KolmogorovBound

open MeasureTheory LatticeProb

noncomputable section
namespace Parking

/-- **The `p`-th power of a two-term sum.** -/
theorem abs_add_rpow_le (a b p : ℝ) (hp : 1 ≤ p) :
    |a + b| ^ p ≤ 2 ^ p * (|a| ^ p + |b| ^ p) := by
  have hp0 : (0 : ℝ) ≤ p := le_trans zero_le_one hp
  set M := max |a| |b| with hM
  have hM0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (le_max_left _ _)
  have h1 : |a + b| ≤ 2 * M := by
    calc |a + b| ≤ |a| + |b| := abs_add_le _ _
      _ ≤ M + M := add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = 2 * M := (two_mul M).symm
  have h2 : M ^ p ≤ |a| ^ p + |b| ^ p := by
    rcases le_total |a| |b| with h | h
    · rw [hM, max_eq_right h]
      exact le_add_of_nonneg_left (Real.rpow_nonneg (abs_nonneg _) _)
    · rw [hM, max_eq_left h]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)
  calc |a + b| ^ p ≤ (2 * M) ^ p := Real.rpow_le_rpow (abs_nonneg _) h1 hp0
    _ = 2 ^ p * M ^ p := Real.mul_rpow (by norm_num) hM0
    _ ≤ 2 ^ p * (|a| ^ p + |b| ^ p) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (by norm_num) _)

/-- **The natural clamp of the floor is below the argument.** -/
theorem toNat_floor_le {x : ℝ} (hx : 0 ≤ x) : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx

/-- **The single-point moment of the box reward at the lower corner**
`(0, -2A)`: the interpolation is within one cell of the grid value, whose
remaining horizon is below `nT`. -/
theorem exists_orientedBoxReward_single_moment (ν : Measure ℤ) (hν : CriticalLaw ν)
    (p : ℝ) (hp : 2 ≤ p) (T A : ℝ) (hT : 0 ≤ T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : ℕ) (_hn : 1 ≤ n),
      Integrable (fun η : Site 2 → ℝ => |orientedBoxReward T n η ![0, -(2 * A)]| ^ p)
        (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, |orientedBoxReward T n η ![0, -(2 * A)]| ^ p
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
    fun n hn => ?_⟩
  set a : Fin 2 → ℝ := ![0, -(2 * A)] with ha
  have ha0 : (0 : ℝ) ≤ a 0 := by rw [ha, Matrix.cons_val_zero]
  obtain ⟨hcellInt, hcellBound⟩ := hcell T n a ha0
  obtain ⟨hsingleInt, hsingleBound⟩ := hsingle n ⌊(n : ℝ) * T⌋₊ ⌊(n : ℝ) * a 0⌋
    ⌊Real.sqrt n * a 1 + (n : ℝ) * a 0 / 2⌋
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
  have hsqrtN : Real.sqrt (((⌊(n : ℝ) * T⌋₊ - ⌊(n : ℝ) * a 0⌋.toNat : ℕ) : ℝ)) ≤
      Real.sqrt ((⌊(n : ℝ) * T⌋₊ : ℕ) : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le _ _)
  have hsqrtnpow : (Real.sqrt n) ^ (p / 2) = (n : ℝ) ^ (p / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg n),
      show (1 : ℝ) / 2 * (p / 2) = p / 4 by ring]
  have hVb : (∫ η : Site 2 → ℝ, |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * a 0⌋
        ⌊Real.sqrt n * a 1 + (n : ℝ) * a 0 / 2⌋| ^ p ∂(iidLaw 2 (realLaw ν))) ≤
      (C₂ * (Real.sqrt T + 1 / 2)) ^ (p / 2) := by
    have hb0 : (0 : ℝ) ≤ C₂ * (Real.sqrt
        (((⌊(n : ℝ) * T⌋₊ - ⌊(n : ℝ) * a 0⌋.toNat : ℕ) : ℝ)) + 1 / 2) :=
      mul_nonneg hC₂.le (add_nonneg (Real.sqrt_nonneg _) (by norm_num))
    calc (∫ η : Site 2 → ℝ, |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * a 0⌋
          ⌊Real.sqrt n * a 1 + (n : ℝ) * a 0 / 2⌋| ^ p ∂(iidLaw 2 (realLaw ν)))
        ≤ (C₂ * (Real.sqrt (((⌊(n : ℝ) * T⌋₊ - ⌊(n : ℝ) * a 0⌋.toNat : ℕ) : ℝ)) + 1 / 2)) ^
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
  have hpoint : ∀ η : Site 2 → ℝ, |orientedBoxReward T n η a| ^ p ≤
      2 ^ p * (|orientedBoxReward T n η a - orientedGridReward n ⌊(n : ℝ) * T⌋₊ η
          ⌊(n : ℝ) * a 0⌋ ⌊Real.sqrt n * a 1 + (n : ℝ) * a 0 / 2⌋| ^ p +
        |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * a 0⌋
          ⌊Real.sqrt n * a 1 + (n : ℝ) * a 0 / 2⌋| ^ p) := by
    intro η
    have e : orientedBoxReward T n η a = (orientedBoxReward T n η a -
        orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * a 0⌋
          ⌊Real.sqrt n * a 1 + (n : ℝ) * a 0 / 2⌋) +
      orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * a 0⌋
        ⌊Real.sqrt n * a 1 + (n : ℝ) * a 0 / 2⌋ := (sub_add_cancel _ _).symm
    conv_lhs => rw [e]
    exact abs_add_rpow_le _ _ _ hp1
  have hgInt : Integrable (fun η : Site 2 → ℝ =>
      2 ^ p * (|orientedBoxReward T n η a - orientedGridReward n ⌊(n : ℝ) * T⌋₊ η
          ⌊(n : ℝ) * a 0⌋ ⌊Real.sqrt n * a 1 + (n : ℝ) * a 0 / 2⌋| ^ p +
        |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * a 0⌋
          ⌊Real.sqrt n * a 1 + (n : ℝ) * a 0 / 2⌋| ^ p)) (iidLaw 2 (realLaw ν)) :=
    (hcellInt.add hsingleInt).const_mul _
  have hfMeas : Measurable fun η : Site 2 → ℝ => |orientedBoxReward T n η a| ^ p :=
    measurable_abs_rpow (measurable_orientedBoxReward T n a) p
  have hfInt : Integrable (fun η : Site 2 → ℝ => |orientedBoxReward T n η a| ^ p)
      (iidLaw 2 (realLaw ν)) :=
    hgInt.mono' hfMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun η => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact hpoint η)
  have hnp : (n : ℝ) ^ (-(p / 4)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1ℝ (by linarith)
  have hcellBound2 : (∫ η : Site 2 → ℝ, |orientedBoxReward T n η a -
        orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * a 0⌋
          ⌊Real.sqrt n * a 1 + (n : ℝ) * a 0 / 2⌋| ^ p ∂(iidLaw 2 (realLaw ν))) ≤
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
  calc ∫ η : Site 2 → ℝ, |orientedBoxReward T n η a| ^ p ∂(iidLaw 2 (realLaw ν))
      ≤ ∫ η : Site 2 → ℝ, 2 ^ p * (|orientedBoxReward T n η a -
            orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * a 0⌋
              ⌊Real.sqrt n * a 1 + (n : ℝ) * a 0 / 2⌋| ^ p +
          |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * a 0⌋
            ⌊Real.sqrt n * a 1 + (n : ℝ) * a 0 / 2⌋| ^ p) ∂(iidLaw 2 (realLaw ν)) :=
        integral_mono_ae hfInt hgInt (Filter.Eventually.of_forall hpoint)
    _ = 2 ^ p * ((∫ η : Site 2 → ℝ, |orientedBoxReward T n η a -
            orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * a 0⌋
              ⌊Real.sqrt n * a 1 + (n : ℝ) * a 0 / 2⌋| ^ p ∂(iidLaw 2 (realLaw ν))) +
          (∫ η : Site 2 → ℝ, |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * a 0⌋
              ⌊Real.sqrt n * a 1 + (n : ℝ) * a 0 / 2⌋| ^ p ∂(iidLaw 2 (realLaw ν)))) := by
        rw [integral_const_mul, integral_add]
        · exact hcellInt
        · exact hsingleInt
    _ ≤ 2 ^ p * (4 ^ (p + 1) * (C₃ * 5) ^ (p / 2) +
          (C₂ * (Real.sqrt T + 1 / 2)) ^ (p / 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add hcellBound2 hVb)
          (Real.rpow_nonneg (by norm_num) _)

/-- **Equicontinuity in probability of the rescaled reward field**, uniformly
in the scale: the Kolmogorov modulus theorem applied to the uniform moment
bound with `q = p/4 > 2`. -/
theorem orientedBoxReward_modulusInProbability (ν : Measure ℤ) (hν : CriticalLaw ν)
    (p : ℝ) (hp : 8 < p) (T A : ℝ) (hT : 0 ≤ T) (hA : 0 ≤ A) (ε η : ℝ)
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, 1 ≤ n →
      iidLaw 2 (realLaw ν) {ω : Site 2 → ℝ | ∃ u ∈ orientedBox T A,
        ∃ v ∈ orientedBox T A, dist u v < δ ∧
          η < |orientedBoxReward T n ω u - orientedBoxReward T n ω v|} ≤
      ENNReal.ofReal ε := by
  obtain ⟨K₀, hK₀0, hK₀all⟩ := exists_orientedBoxReward_kolmogorov ν hν p (by linarith) T hT
  obtain ⟨M, hM0, _hMbd, hK⟩ := hK₀all A hA
  obtain ⟨δ, hδ0, hδ⟩ := kolmogorovModulusPi 2 ![0, -(2 * A)] ![T, 2 * A] p (p / 4) M
    (by linarith) (by linarith) ε η hε hη
  refine ⟨δ, hδ0, fun n hn => ?_⟩
  haveI : IsProbabilityMeasure ν := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI : IsProbabilityMeasure (iidLaw 2 (realLaw ν)) := by unfold iidLaw; infer_instance
  exact hδ (iidLaw 2 (realLaw ν)) inferInstance (fun u ω => orientedBoxReward T n ω u)
    (fun u => measurable_orientedBoxReward T n u)
    (fun u hu v hv => (hK n hn u v hu hv).1)
    (fun u hu v hv => (hK n hn u v hu hv).2)
    (fun ω => (continuous_orientedBoxReward T n ω).continuousOn)

/-- **Uniform boundedness in probability of the rescaled reward field**: the
Kolmogorov boundedness theorem applied to the uniform moment bound and the
single-point moment at the lower corner. -/
theorem orientedBoxReward_boundedInProbability (ν : Measure ℤ) (hν : CriticalLaw ν)
    (p : ℝ) (hp : 8 < p) (T A : ℝ) (hT : 0 ≤ T) (hA : 0 ≤ A) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, ∀ n : ℕ, 1 ≤ n →
      iidLaw 2 (realLaw ν) {ω : Site 2 → ℝ | ∃ u ∈ orientedBox T A,
        B < |orientedBoxReward T n ω u|} ≤ ENNReal.ofReal ε := by
  obtain ⟨K₀, hK₀0, hK₀all⟩ := exists_orientedBoxReward_kolmogorov ν hν p (by linarith) T hT
  obtain ⟨M, hM0, _hMbd, hK⟩ := hK₀all A hA
  obtain ⟨M₀, hM₀0, hS⟩ := exists_orientedBoxReward_single_moment ν hν p (by linarith) T A hT
  obtain ⟨B, hB⟩ := kolmogorovBoundPi 2 ![0, -(2 * A)] ![T, 2 * A] p (p / 4) (max M M₀)
    (by linarith) (by linarith) ε hε
  refine ⟨B, fun n hn => ?_⟩
  haveI : IsProbabilityMeasure ν := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI : IsProbabilityMeasure (iidLaw 2 (realLaw ν)) := by unfold iidLaw; infer_instance
  have hbase : ![0, -(2 * A)] ∈ orientedBox T A := by
    rw [orientedBox]
    refine Set.left_mem_Icc.mpr fun i => ?_
    fin_cases i
    · show (0 : ℝ) ≤ T
      exact hT
    · show -(2 * A) ≤ 2 * A
      linarith
  exact hB (iidLaw 2 (realLaw ν)) inferInstance (fun u ω => orientedBoxReward T n ω u)
    (fun u => measurable_orientedBoxReward T n u)
    (fun u hu v hv => (hK n hn u v hu hv).1)
    (fun u hu v hv => le_trans (hK n hn u v hu hv).2
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _)))
    (hS n hn).1
    (le_trans (hS n hn).2 (le_max_right _ _))
    (fun ω => (continuous_orientedBoxReward T n ω).continuousOn)

end Parking
end
