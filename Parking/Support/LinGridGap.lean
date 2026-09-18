/-
**Item (B) of `prop:spatial-scaling`'s Step 1: the grid gap**
`linHatInterp(confReal w) R (s,x) − barPotential w R s x → 0` in probability.

The proof runs as follows.  The deterministic corner reduction
`Parking.hatInterpD_eq_corners`/`Parking.abs_hatInterpD_sub_le_of_forall` reduces the gap to a
union bound, over the fixed-cardinality (`2·2^d`) corner box, of one-corner tail events; each
corner tail is bounded via `Parking.Generic.Chebyshev.measure_gt_le_integral_sq_div_sq` with
the second moment from `Parking.exists_linPotential_increment_moment` (`q := 2`) and the
mean-zero and integrability facts of `Parking.Support.LinMeanMoment`; the Green two-point,
two-time difference is bounded via
`Parking.exists_green_joint_l2_bound`/`exists_green_joint_sup_bound`; the resulting bound is
UNIFORM over every corner (it depends only on the fixed cardinality data `graphNorm(c-z0) ≤ d`
and `m - n0 ≤ 1`, not on which particular corner), so the union bound needs no reindexing of the
`R`-dependent corner Finsets, only `Finset.sum_le_card_nsmul` at their (`R`-independent)
cardinalities; the bound's own vanishing is `Parking.tendsto_rpow_spatialStepRate_sq_zero`, the
three-way dimension asymptotic of `Parking/Support/SpatialStepRateAsymptotic.lean`.
-/
import Parking.Support.LinMeanMoment
import Parking.Support.LinIncrementMoment
import Parking.Support.SpatGreenJoint
import Parking.Support.SpatialStepRateAsymptotic
import Parking.Support.BarPotential
import Parking.Support.HatInterpD
import Parking.Support.LinInterp
import Parking.Generic.Chebyshev

noncomputable section

namespace Parking

open MeasureTheory Filter Topology LatticeProb Finset

variable {d : ℕ}

/-! ### The deterministic corner reduction, contrapositive form -/

/-- **A violation of the interpolation bound forces a violation at some corner.**  The
contrapositive of `Parking.abs_hatInterpD_sub_le_of_forall`. -/
theorem exists_corner_lt_of_lt_abs_hatInterpD_sub {d : ℕ} (V : ℤ → Site d → ℝ)
    (u : ℝ × (Fin d → ℝ)) (v0 ε : ℝ) (h : ε < |hatInterpD V u - v0|) :
    ∃ m ∈ ({⌊u.1⌋, ⌊u.1⌋ + 1} : Finset ℤ),
      ∃ c ∈ Fintype.piFinset fun i : Fin d => ({⌊u.2 i⌋, ⌊u.2 i⌋ + 1} : Finset ℤ),
        ε < |V m c - v0| := by
  by_contra hc
  push Not at hc
  exact absurd (abs_hatInterpD_sub_le_of_forall V u v0 ε hc) (not_le.mpr h)

/-! ### `⌊sR²⌋₊ → ∞` -/

theorem tendsto_natFloor_mul_sq_atTop {s : ℝ} (hs : 0 < s) :
    Tendsto (fun R : ℝ => (⌊s * R ^ 2⌋₊ : ℕ)) atTop atTop :=
  tendsto_nat_floor_atTop.comp
    ((tendsto_pow_atTop (two_ne_zero)).const_mul_atTop hs)

/-! ### `l2Norm` and `supAbs` are nonnegative -/

theorem l2Norm_nonneg {d : ℕ} (f : Site d → ℝ) : 0 ≤ l2Norm f := by
  unfold l2Norm; positivity

theorem supAbs_nonneg {d : ℕ} (f : Site d → ℝ) : 0 ≤ supAbs f := by
  unfold supAbs
  by_cases hbdd : BddAbove (Set.range fun x : Site d => |f x|)
  · exact le_trans (abs_nonneg (f 0)) (le_ciSup hbdd (0 : Site d))
  · rw [Real.iSup_of_not_bddAbove hbdd]

/-! ### The one-corner tail bound, uniform over the corner box -/

/-- **The one-corner tail bound.**  For a fixed `R > 0` with `n0 R ≥ 1`, every pair `(m, c)`
with `n0 ≤ m ≤ n0 + 1` and `graphNorm (c - z0) ≤ d` has the SAME upper bound on its tail
measure: a constant (depending on `d, ε` and the moment and Green-function data) times
`R^{d-4}·spatialStepRate(d, n0+1)²`. -/
theorem exists_corner_tail_bound (hd1 : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ) (hν : CriticalLaw ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (R : ℝ), 0 < R → ∀ n0 : ℕ, 1 ≤ n0 → ∀ m : ℕ, n0 ≤ m → m ≤ n0 + 1 →
        ∀ z0 c : Site d, graphNorm (c - z0) ≤ d →
          ((iidLaw d (realLaw ν))
              {η | ε < |R ^ ((d:ℝ)/2 - 2) * (linPotential η m c - linPotential η n0 z0)|}).toReal
            ≤ K * (R ^ ((d:ℝ) - 4) * (spatialStepRate d (n0 + 1)) ^ 2) := by
  haveI := hν.prob
  haveI hν0P : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI hμP : IsProbabilityMeasure (iidLaw d (realLaw ν)) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : Site d => realLaw ν))
  obtain ⟨θ, hθ, hexpabs⟩ := realLaw_expMoment ν hν
  have hint1 : Integrable (fun z : ℝ => z) (realLaw ν) :=
    (realLaw_memLp_two ν hν).integrable one_le_two
  have hsq1 : Integrable (fun z : ℝ => z ^ 2) (realLaw ν) := (realLaw_memLp_two ν hν).integrable_sq
  obtain ⟨Cmom, hCmom, hmom⟩ := exists_linPotential_increment_moment hd1 (realLaw ν) θ hθ hexpabs
  obtain ⟨KL2, hKL2, hL2⟩ := exists_green_joint_l2_bound hd1 hd3 (d := d)
  obtain ⟨KSup, hKSup, hSup⟩ := exists_green_joint_sup_bound hd1 hd3 (d := d)
  set D1 : ℝ := Real.sqrt (LatticeProb.diagConst d / Real.sqrt 2 ^ d) with hD1def
  set D2 : ℝ := LatticeProb.diagConst d with hD2def
  set A : ℝ := Real.sqrt 2 * KL2 * (d : ℝ) with hAdef
  set B : ℝ := Real.sqrt 2 * D1 + 2 * KSup * (d : ℝ) + 2 * D2 with hBdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hBpos : 0 < B := by
    rw [hBdef]
    have hD2pos : 0 < D2 := by rw [hD2def]; exact LatticeProb.diagConst_pos d
    have hD1nonneg : 0 ≤ D1 := by rw [hD1def]; positivity
    have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd1
    positivity
  refine ⟨Cmom ^ 2 * (A + B) ^ 2 / ε ^ 2, by positivity, ?_⟩
  intro R hR n0 hn0 m hn0m hmn0 z0 c hcz0
  set f : (Site d → ℝ) → ℝ :=
      fun η => R ^ ((d:ℝ)/2 - 2) * (linPotential η m c - linPotential η n0 z0) with hfdef
  set diff : (Site d → ℝ) → ℝ := fun η => linPotential η m c - linPotential η n0 z0 with hdiffdef
  have hmeandiff : (∫ η, diff η ∂(iidLaw d (realLaw ν))) = 0 := by
    rw [hdiffdef]
    have h1 := integral_linPotential_eq_zero_critical ν hν m c
    have h2 := integral_linPotential_eq_zero_critical ν hν n0 z0
    have hi1 := integrable_linPotential_critical ν hν m c
    have hi2 := integrable_linPotential_critical ν hν n0 z0
    rw [integral_sub hi1 hi2, h1, h2, sub_zero]
  have hsq2 : Integrable (fun η => (diff η) ^ 2) (iidLaw d (realLaw ν)) := by
    rw [hdiffdef]; exact integrable_linPotential_diff_sq_critical ν hν m n0 c z0
  have hbound := hmom m n0 c z0 (2:ℝ) (by norm_num)
  rw [hmeandiff] at hbound
  have hbound2 : (∫ η, (diff η) ^ 2 ∂(iidLaw d (realLaw ν)))
      ≤ (Cmom * (Real.sqrt 2 * l2Norm (fun z => green d m (c - z) - green d n0 (z0 - z))
          + 2 * supAbs (fun z => green d m (c - z) - green d n0 (z0 - z)))) ^ 2 := by
    have hlhs_eq : (∫ η, |diff η - 0| ^ (2:ℝ) ∂(iidLaw d (realLaw ν)))
        = ∫ η, (diff η) ^ 2 ∂(iidLaw d (realLaw ν)) := by
      have hpt : ∀ η, |diff η - 0| ^ (2:ℝ) = (diff η) ^ 2 := by
        intro η
        rw [sub_zero, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs]
      simp_rw [hpt]
    rw [hlhs_eq] at hbound
    have hnn : (0:ℝ) ≤ ∫ η, (diff η) ^ 2 ∂(iidLaw d (realLaw ν)) := integral_nonneg fun η => sq_nonneg _
    have heqpow : (∫ η, (diff η) ^ 2 ∂(iidLaw d (realLaw ν)))
        = ((∫ η, (diff η) ^ 2 ∂(iidLaw d (realLaw ν))) ^ ((2:ℕ)⁻¹ : ℝ)) ^ (2:ℕ) := by
      rw [Real.rpow_inv_natCast_pow hnn (by norm_num)]
    rw [heqpow]
    have hexp : (1:ℝ) / 2 = ((2:ℕ):ℝ)⁻¹ := by norm_num
    rw [hexp] at hbound
    exact pow_le_pow_left₀ (Real.rpow_nonneg hnn _) hbound 2
  have hl2b := hL2 m n0 hn0 hn0m c z0
  have hsupb := hSup m n0 hn0 hn0m c z0
  have hn0R : (1:ℝ) ≤ (n0:ℝ) := by exact_mod_cast hn0
  have hgraph : ((graphNorm (c - z0) : ℕ):ℝ) ≤ (d:ℝ) := by exact_mod_cast hcz0
  have hmn0R : ((m:ℝ) - n0) ≤ 1 := by
    have : m ≤ n0 + 1 := hmn0
    have : (m:ℝ) ≤ (n0:ℝ) + 1 := by exact_mod_cast this
    linarith
  have hrateM : spatialStepRate d m ≤ spatialStepRate d (n0 + 1) :=
    spatialStepRate_mono hd1 hd3 hmn0
  have hD1b : Real.sqrt (LatticeProb.diagConst d / Real.sqrt (2 * (n0:ℝ)) ^ d) ≤ D1 := by
    rw [hD1def]
    have hpow_pos : (0:ℝ) < Real.sqrt 2 ^ d := by positivity
    have hle : Real.sqrt 2 ^ d ≤ Real.sqrt (2 * (n0:ℝ)) ^ d :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (by nlinarith)) d
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (LatticeProb.diagConst_pos d).le hpow_pos hle)
  have hD2b : LatticeProb.diagConst d / Real.sqrt (n0:ℝ) ^ d ≤ D2 := by
    rw [hD2def]
    have hpow_pos : (0:ℝ) < Real.sqrt (n0:ℝ) ^ d := by positivity
    have hone_pos : (0:ℝ) < Real.sqrt 1 ^ d := by positivity
    have hle : Real.sqrt 1 ^ d ≤ Real.sqrt (n0:ℝ) ^ d :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (by linarith)) d
    have := div_le_div_of_nonneg_left (LatticeProb.diagConst_pos d).le hone_pos hle
    simpa using this
  have hl2 : l2Norm (fun z => green d m (c - z) - green d n0 (z0 - z))
      ≤ KL2 * (d:ℝ) * spatialStepRate d (n0 + 1) + D1 := by
    refine hl2b.trans ?_
    have h1 : KL2 * spatialStepRate d m * (graphNorm (c - z0) : ℝ) ≤ KL2 * (d:ℝ) * spatialStepRate d (n0 + 1) := by
      have hrateNonneg : 0 ≤ spatialStepRate d m := by
        have := one_le_spatialStepRate hd1 hd3 m; linarith
      calc KL2 * spatialStepRate d m * (graphNorm (c - z0) : ℝ)
          ≤ KL2 * spatialStepRate d m * (d:ℝ) := by
            apply mul_le_mul_of_nonneg_left hgraph
            exact mul_nonneg hKL2.le hrateNonneg
        _ = KL2 * (d:ℝ) * spatialStepRate d m := by ring
        _ ≤ KL2 * (d:ℝ) * spatialStepRate d (n0 + 1) :=
            mul_le_mul_of_nonneg_left hrateM (by positivity)
    have h2 : ((m:ℝ) - n0) * Real.sqrt (LatticeProb.diagConst d / Real.sqrt (2 * n0) ^ d) ≤ D1 := by
      have hnn2 : (0:ℝ) ≤ Real.sqrt (LatticeProb.diagConst d / Real.sqrt (2 * (n0:ℝ)) ^ d) :=
        Real.sqrt_nonneg _
      calc ((m:ℝ) - n0) * Real.sqrt (LatticeProb.diagConst d / Real.sqrt (2 * n0) ^ d)
          ≤ 1 * Real.sqrt (LatticeProb.diagConst d / Real.sqrt (2 * n0) ^ d) :=
            mul_le_mul_of_nonneg_right hmn0R hnn2
        _ = Real.sqrt (LatticeProb.diagConst d / Real.sqrt (2 * n0) ^ d) := one_mul _
        _ ≤ D1 := hD1b
    linarith
  have hsup : supAbs (fun z => green d m (c - z) - green d n0 (z0 - z))
      ≤ KSup * (d:ℝ) + D2 := by
    refine hsupb.trans ?_
    have h1 : KSup * (graphNorm (c - z0) : ℝ) ≤ KSup * (d:ℝ) :=
      mul_le_mul_of_nonneg_left hgraph hKSup.le
    have h2 : ((m:ℝ) - n0) * (LatticeProb.diagConst d / Real.sqrt n0 ^ d) ≤ D2 := by
      have hnn2 : (0:ℝ) ≤ LatticeProb.diagConst d / Real.sqrt (n0:ℝ) ^ d :=
        div_nonneg (LatticeProb.diagConst_pos d).le (by positivity)
      calc ((m:ℝ) - n0) * (LatticeProb.diagConst d / Real.sqrt n0 ^ d)
          ≤ 1 * (LatticeProb.diagConst d / Real.sqrt n0 ^ d) :=
            mul_le_mul_of_nonneg_right hmn0R hnn2
        _ = LatticeProb.diagConst d / Real.sqrt n0 ^ d := one_mul _
        _ ≤ D2 := hD2b
    linarith
  have hrateOne : (1:ℝ) ≤ spatialStepRate d (n0 + 1) := one_le_spatialStepRate hd1 hd3 (n0+1)
  have hcombine : Real.sqrt 2 * l2Norm (fun z => green d m (c - z) - green d n0 (z0 - z))
      + 2 * supAbs (fun z => green d m (c - z) - green d n0 (z0 - z))
        ≤ (A + B) * spatialStepRate d (n0 + 1) := by
    have hstep : Real.sqrt 2 * l2Norm (fun z => green d m (c - z) - green d n0 (z0 - z))
        + 2 * supAbs (fun z => green d m (c - z) - green d n0 (z0 - z))
          ≤ A * spatialStepRate d (n0 + 1) + B := by
      have e1 : Real.sqrt 2 * l2Norm (fun z => green d m (c - z) - green d n0 (z0 - z))
          ≤ Real.sqrt 2 * (KL2 * (d:ℝ) * spatialStepRate d (n0 + 1) + D1) :=
        mul_le_mul_of_nonneg_left hl2 (Real.sqrt_nonneg _)
      have e2 : 2 * supAbs (fun z => green d m (c - z) - green d n0 (z0 - z))
          ≤ 2 * (KSup * (d:ℝ) + D2) := mul_le_mul_of_nonneg_left hsup (by norm_num)
      rw [hAdef, hBdef]; nlinarith [e1, e2]
    have hfinal : A * spatialStepRate d (n0 + 1) + B ≤ (A + B) * spatialStepRate d (n0 + 1) := by
      nlinarith [hrateOne, hBpos.le]
    linarith
  have hsqfinal : (Cmom * (Real.sqrt 2 * l2Norm (fun z => green d m (c - z) - green d n0 (z0 - z))
      + 2 * supAbs (fun z => green d m (c - z) - green d n0 (z0 - z)))) ^ 2
        ≤ Cmom ^ 2 * (A + B) ^ 2 * (spatialStepRate d (n0 + 1)) ^ 2 := by
    have hcombine_nonneg : 0 ≤ Real.sqrt 2 * l2Norm (fun z => green d m (c - z) - green d n0 (z0 - z))
        + 2 * supAbs (fun z => green d m (c - z) - green d n0 (z0 - z)) :=
      add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (l2Norm_nonneg _))
        (mul_nonneg (by norm_num) (supAbs_nonneg _))
    have h1 : (Cmom * (Real.sqrt 2 * l2Norm (fun z => green d m (c - z) - green d n0 (z0 - z))
        + 2 * supAbs (fun z => green d m (c - z) - green d n0 (z0 - z)))) ^ 2
          ≤ (Cmom * ((A + B) * spatialStepRate d (n0 + 1))) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hCmom.le hcombine_nonneg)
        (mul_le_mul_of_nonneg_left hcombine hCmom.le) 2
    calc (Cmom * (Real.sqrt 2 * l2Norm (fun z => green d m (c - z) - green d n0 (z0 - z))
        + 2 * supAbs (fun z => green d m (c - z) - green d n0 (z0 - z)))) ^ 2
        ≤ (Cmom * ((A + B) * spatialStepRate d (n0 + 1))) ^ 2 := h1
      _ = Cmom ^ 2 * (A + B) ^ 2 * (spatialStepRate d (n0 + 1)) ^ 2 := by ring
  have hint2 : (∫ η, (diff η) ^ 2 ∂(iidLaw d (realLaw ν)))
      ≤ Cmom ^ 2 * (A + B) ^ 2 * (spatialStepRate d (n0 + 1)) ^ 2 := hbound2.trans hsqfinal
  have hcheb := Parking.Generic.Chebyshev.measure_gt_le_integral_sq_div_sq
    (iidLaw d (realLaw ν)) f hε (by
      have heq : (fun η => (f η) ^ 2)
          = fun η => (R ^ ((d:ℝ)/2 - 2)) ^ 2 * (diff η) ^ 2 := by
        funext η; rw [hfdef]; ring
      rw [heq]
      exact hsq2.const_mul _)
  have hfeq : (fun η => (f η) ^ 2) = fun η => (R ^ ((d:ℝ)/2 - 2)) ^ 2 * (diff η) ^ 2 := by
    funext η; rw [hfdef]; ring
  rw [show {ω | ε < |f ω|} = {η | ε < |f η|} from rfl] at hcheb
  have hintstep : (∫ η, (f η) ^ 2 ∂(iidLaw d (realLaw ν)))
      = (R ^ ((d:ℝ)/2 - 2)) ^ 2 * (∫ η, (diff η) ^ 2 ∂(iidLaw d (realLaw ν))) := by
    rw [hfeq]; exact integral_const_mul _ _
  have hRpow : (R ^ ((d:ℝ)/2 - 2)) ^ 2 = R ^ ((d:ℝ) - 4) := by
    rw [← Real.rpow_natCast (R ^ ((d:ℝ)/2 - 2)) 2, ← Real.rpow_mul hR.le]
    congr 1; ring
  rw [hintstep, hRpow] at hcheb
  refine hcheb.trans ?_
  rw [div_le_iff₀ (by positivity)]
  have hbig : R ^ ((d:ℝ) - 4) * (∫ η, (diff η) ^ 2 ∂(iidLaw d (realLaw ν)))
      ≤ R ^ ((d:ℝ) - 4) * (Cmom ^ 2 * (A + B) ^ 2 * (spatialStepRate d (n0 + 1)) ^ 2) :=
    mul_le_mul_of_nonneg_left hint2 (Real.rpow_nonneg hR.le _)
  calc R ^ ((d:ℝ) - 4) * (∫ η, (diff η) ^ 2 ∂(iidLaw d (realLaw ν)))
      ≤ R ^ ((d:ℝ) - 4) * (Cmom ^ 2 * (A + B) ^ 2 * (spatialStepRate d (n0 + 1)) ^ 2) := hbig
    _ = Cmom ^ 2 * (A + B) ^ 2 / ε ^ 2 * (R ^ ((d:ℝ) - 4) * (spatialStepRate d (n0 + 1)) ^ 2) * ε ^ 2 := by
        have hεne : ε ≠ 0 := ne_of_gt hε
        field_simp

/-! ### The combinatorics of a corner box -/

/-- **A time corner's `toNat` is within `1` of the base time.** -/
theorem toNat_mem_bounds {n0 : ℕ} {m : ℤ} (h : m ∈ ({(n0:ℤ), (n0:ℤ) + 1} : Finset ℤ)) :
    n0 ≤ m.toNat ∧ m.toNat ≤ n0 + 1 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl <;> constructor <;> omega

/-- **A space corner's `graphNorm` distance from the base point is at most `d`.** -/
theorem graphNorm_le_of_forall_mem_pair {d : ℕ} (z0 c : Site d)
    (h : ∀ i, c i = z0 i ∨ c i = z0 i + 1) : graphNorm (c - z0) ≤ d := by
  unfold graphNorm
  have hterm : ∀ i, ((c - z0) i).natAbs ≤ 1 := by
    intro i
    rw [Pi.sub_apply]
    rcases h i with h1 | h1 <;> rw [h1] <;> simp
  calc ∑ i, ((c - z0) i).natAbs ≤ ∑ _i : Fin d, 1 := Finset.sum_le_sum fun i _ => hterm i
    _ = d := by simp

/-! ### The grid gap, assembled -/

/-- **The grid gap of `prop:spatial-scaling`'s Step 1, item (B), assembled.**  The interpolated,
rescaled linear membrane field and the field read at its own base grid point converge together,
in probability, as `R → ∞`. -/
theorem tendsto_measure_linHatInterp_sub_barPotential_zero
    (hd1 : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (s : ℝ) (hs : 0 < s) (x : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R : ℝ => ((iidLaw d (realLaw ν))
        {η | ε < |linHatInterp η R (s, x) - barPotential η R s x|}).toReal) atTop (𝓝 0) := by
  haveI := hν.prob
  haveI hν0P : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI hμP : IsProbabilityMeasure (iidLaw d (realLaw ν)) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : Site d => realLaw ν))
  obtain ⟨K, hK, hKbound⟩ := exists_corner_tail_bound (d := d) hd1 hd3 ν hν hε
  set N : ℝ := 2 * 2 ^ d with hNdef
  have hNpos : 0 < N := by rw [hNdef]; positivity
  set g : ℝ → ℝ := fun R => K * (R ^ ((d:ℝ) - 4) * (spatialStepRate d (⌊s * R ^ 2⌋₊ + 1)) ^ 2)
    with hgdef
  have hgzero : Tendsto g atTop (𝓝 0) := by
    rw [hgdef]
    simpa using (tendsto_rpow_spatialStepRate_sq_zero hd1 hd3 hs).const_mul K
  have hNgzero : Tendsto (fun R => N * g R) atTop (𝓝 0) := by
    simpa using hgzero.const_mul N
  refine squeeze_zero' (Filter.Eventually.of_forall fun R => ENNReal.toReal_nonneg) ?_ hNgzero
  filter_upwards [Filter.eventually_gt_atTop (0:ℝ),
    (tendsto_natFloor_mul_sq_atTop hs).eventually_ge_atTop 1] with R hR hn0
  set n0 : ℕ := ⌊s * R ^ 2⌋₊ with hn0def
  set z0 : Site d := latticePoint R x with hz0def
  set u : ℝ × (Fin d → ℝ) := (R ^ 2 * s, fun i => R * x i) with hudef
  have hS1card : (({⌊u.1⌋, ⌊u.1⌋ + 1} : Finset ℤ)).card = 2 := Finset.card_pair (by omega)
  have hS2card : (Fintype.piFinset fun i : Fin d =>
      ({⌊u.2 i⌋, ⌊u.2 i⌋ + 1} : Finset ℤ)).card = 2 ^ d := by
    rw [Fintype.card_piFinset]
    have hEach : ∀ i : Fin d, (({⌊u.2 i⌋, ⌊u.2 i⌋ + 1} : Finset ℤ)).card = 2 :=
      fun i => Finset.card_pair (by omega)
    simp [hEach]
  have hu1floor : ⌊u.1⌋ = (n0 : ℤ) := by
    rw [hudef, hn0def]
    show ⌊R ^ 2 * s⌋ = (⌊s * R ^ 2⌋₊ : ℤ)
    rw [Int.natCast_floor_eq_floor (by positivity), mul_comm]
  have hEsub : {η : Site d → ℝ | ε < |linHatInterp η R (s, x) - barPotential η R s x|}
      ⊆ ⋃ m ∈ ({⌊u.1⌋, ⌊u.1⌋ + 1} : Finset ℤ),
          ⋃ c ∈ Fintype.piFinset fun i : Fin d => ({⌊u.2 i⌋, ⌊u.2 i⌋ + 1} : Finset ℤ),
            {η : Site d → ℝ |
              ε < |R ^ ((d:ℝ)/2 - 2) * linPotential η m.toNat c - barPotential η R s x|} := by
    intro η hη
    have hη' : ε < |hatInterpD (fun m c => R ^ ((d:ℝ)/2 - 2) * linPotential η m.toNat c) u
        - barPotential η R s x| := hη
    obtain ⟨m, hm, c, hc, hmc⟩ := exists_corner_lt_of_lt_abs_hatInterpD_sub _ u _ ε hη'
    exact Set.mem_biUnion hm (Set.mem_biUnion hc hmc)
  have hcorner_bound : ∀ m ∈ ({⌊u.1⌋, ⌊u.1⌋ + 1} : Finset ℤ),
      ∀ c ∈ Fintype.piFinset fun i : Fin d => ({⌊u.2 i⌋, ⌊u.2 i⌋ + 1} : Finset ℤ),
        ((iidLaw d (realLaw ν)) {η : Site d → ℝ |
            ε < |R ^ ((d:ℝ)/2 - 2) * linPotential η m.toNat c - barPotential η R s x|}).toReal
          ≤ g R := by
    intro m hm c hc
    have hmbounds : n0 ≤ m.toNat ∧ m.toNat ≤ n0 + 1 := toNat_mem_bounds (hu1floor ▸ hm)
    have hcbounds : ∀ i, c i = z0 i ∨ c i = z0 i + 1 := by
      intro i
      have := (Fintype.mem_piFinset).mp hc i
      simpa [hz0def, hudef, latticePoint] using this
    have hgraphle : graphNorm (c - z0) ≤ d := graphNorm_le_of_forall_mem_pair z0 c hcbounds
    have heq : (fun η : Site d → ℝ =>
        R ^ ((d:ℝ)/2 - 2) * linPotential η m.toNat c - barPotential η R s x)
        = fun η => R ^ ((d:ℝ)/2 - 2) * (linPotential η m.toNat c - linPotential η n0 z0) := by
      funext η
      show R ^ ((d:ℝ)/2 - 2) * linPotential η m.toNat c
          - R ^ ((d:ℝ)/2 - 2) * linPotential η n0 z0
        = R ^ ((d:ℝ)/2 - 2) * (linPotential η m.toNat c - linPotential η n0 z0)
      ring
    have hsetEq : {η : Site d → ℝ |
        ε < |R ^ ((d:ℝ)/2 - 2) * linPotential η m.toNat c - barPotential η R s x|}
        = {η : Site d → ℝ |
            ε < |R ^ ((d:ℝ)/2 - 2) * (linPotential η m.toNat c - linPotential η n0 z0)|} := by
      ext η
      simp only [Set.mem_setOf_eq]
      rw [congrFun heq η]
    rw [hsetEq]
    exact hKbound R hR n0 hn0 m.toNat hmbounds.1 hmbounds.2 z0 c hgraphle
  have hmeas_sub : ((iidLaw d (realLaw ν))
      {η : Site d → ℝ | ε < |linHatInterp η R (s, x) - barPotential η R s x|}).toReal
        ≤ N * g R := by
    rw [← measureReal_def]
    set S₁ : Finset ℤ := {⌊u.1⌋, ⌊u.1⌋ + 1} with hS₁def
    set S₂ : Finset (Fin d → ℤ) := Fintype.piFinset fun i : Fin d =>
        ({⌊u.2 i⌋, ⌊u.2 i⌋ + 1} : Finset ℤ) with hS₂def
    set F : ℤ → (Fin d → ℤ) → Set (Site d → ℝ) := fun m c => {η : Site d → ℝ |
        ε < |R ^ ((d:ℝ)/2 - 2) * linPotential η m.toNat c - barPotential η R s x|} with hFdef
    have hstep1 : (iidLaw d (realLaw ν)).real
        {η : Site d → ℝ | ε < |linHatInterp η R (s, x) - barPotential η R s x|}
        ≤ (iidLaw d (realLaw ν)).real (⋃ m ∈ S₁, ⋃ c ∈ S₂, F m c) :=
      measureReal_mono hEsub (measure_ne_top _ _)
    have hstep2 : (iidLaw d (realLaw ν)).real (⋃ m ∈ S₁, ⋃ c ∈ S₂, F m c)
        ≤ ∑ m ∈ S₁, (iidLaw d (realLaw ν)).real (⋃ c ∈ S₂, F m c) :=
      measureReal_biUnion_finset_le _ _
    have hstep3 : ∀ m ∈ S₁, (iidLaw d (realLaw ν)).real (⋃ c ∈ S₂, F m c)
        ≤ ∑ c ∈ S₂, (iidLaw d (realLaw ν)).real (F m c) :=
      fun m _ => measureReal_biUnion_finset_le _ _
    have hstep4 : ∀ m ∈ S₁, ∀ c ∈ S₂, (iidLaw d (realLaw ν)).real (F m c) ≤ g R :=
      fun m hm c hc => by rw [measureReal_def]; exact hcorner_bound m hm c hc
    have hstep5 : ∑ m ∈ S₁, ∑ c ∈ S₂, (iidLaw d (realLaw ν)).real (F m c)
        ≤ ∑ m ∈ S₁, ∑ _c ∈ S₂, g R :=
      Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun c hc => hstep4 m hm c hc
    have hstep6 : ∑ m ∈ S₁, ∑ _c ∈ S₂, g R = N * g R := by
      rw [Finset.sum_const, Finset.sum_const, hS1card, hS2card, hNdef]
      ring
    have hstep2' : (iidLaw d (realLaw ν)).real (⋃ m ∈ S₁, ⋃ c ∈ S₂, F m c)
        ≤ ∑ m ∈ S₁, ∑ c ∈ S₂, (iidLaw d (realLaw ν)).real (F m c) :=
      hstep2.trans (Finset.sum_le_sum hstep3)
    calc (iidLaw d (realLaw ν)).real
          {η : Site d → ℝ | ε < |linHatInterp η R (s, x) - barPotential η R s x|}
        ≤ (iidLaw d (realLaw ν)).real (⋃ m ∈ S₁, ⋃ c ∈ S₂, F m c) := hstep1
      _ ≤ ∑ m ∈ S₁, ∑ c ∈ S₂, (iidLaw d (realLaw ν)).real (F m c) := hstep2'
      _ ≤ ∑ m ∈ S₁, ∑ _c ∈ S₂, g R := hstep5
      _ = N * g R := hstep6
  simpa using hmeas_sub

end Parking

end
