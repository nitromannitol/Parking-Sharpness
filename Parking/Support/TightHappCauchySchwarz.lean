/-
The reward-field-side moment bound `happ` needs, in `L¹`: `E_η[‖Parking.boxRewardMap ...‖]`,
uniform in the scale `n`, growing only POLYNOMIALLY in the cutoff radius `A` (in fact with
exponent `2/p` for any `p > 12`, via `Parking.rNorm_mono_exponent` from `Parking.
exists_yfieldSup3_L2_moment`'s `L²` bound).  The box's own points, read through `Parking.
boxToFin`, always lie in a fixed-radius box of `Parking.Yfield`'s own kind
(`Parking.boxToFin_mem_orientedBox`), so `Parking.ae_abs_Yfield_le_yfieldSup3` applies directly.
-/
import Parking.Support.TightBoxSupL2
import Parking.Support.TightBoxLaw
import Parking.Support.MomentLimits

open MeasureTheory Filter Topology LatticeProb

noncomputable section

namespace Parking

local instance instMeasurableSpaceRewardBoxTightHappCS (T A : ℝ) :
    MeasurableSpace C(rewardBox T A, ℝ) := borel _
local instance instBorelSpaceRewardBoxTightHappCS (T A : ℝ) :
    BorelSpace C(rewardBox T A, ℝ) := ⟨rfl⟩

/-- **A radius covering the cutoff box**, as a natural number, at least `1` and at least
`2A`. -/
def happBoxRadius (A : ℝ) : ℕ := ⌈2 * A⌉₊ + 1

theorem one_le_happBoxRadius (A : ℝ) : (1 : ℝ) ≤ (happBoxRadius A : ℝ) := by
  unfold happBoxRadius
  push_cast
  linarith [Nat.cast_nonneg (α := ℝ) ⌈2 * A⌉₊]

theorem two_mul_le_happBoxRadius {A : ℝ} (_hA : 0 ≤ A) : 2 * A ≤ (happBoxRadius A : ℝ) := by
  unfold happBoxRadius
  have h := Nat.le_ceil (2 * A)
  push_cast
  linarith

/-- **Every point `Parking.boxToFin` reads lies in the fixed-radius box `Parking.
happBoxRadius`.** -/
theorem abs_boxToFin_le_happBoxRadius {A : ℝ} (hA : 0 ≤ A) (p : rewardBox 1 A) (i : Fin 2) :
    |boxToFin 1 A p i| ≤ (happBoxRadius A : ℝ) := by
  have hmem := boxToFin_mem_orientedBox 1 (zero_le_one) A hA p
  rw [orientedBox, Set.mem_Icc] at hmem
  obtain ⟨hlo, hhi⟩ := hmem
  have hloi := hlo i
  have hhii := hhi i
  fin_cases i
  · show |boxToFin 1 A p 0| ≤ _
    simp only [Matrix.cons_val_zero, Fin.zero_eta, Fin.isValue] at hloi hhii
    rw [abs_le]
    exact ⟨by linarith [one_le_happBoxRadius A], by linarith [one_le_happBoxRadius A]⟩
  · show |boxToFin 1 A p 1| ≤ _
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Fin.mk_one, Fin.isValue] at hloi hhii
    rw [abs_le]
    exact ⟨by linarith [two_mul_le_happBoxRadius hA], by linarith [two_mul_le_happBoxRadius hA]⟩

/-- **`‖Parking.boxRewardMap‖` is bounded by `Parking.yfieldSup3` at `Parking.
happBoxRadius`, for a.e. scenery, uniform in the scale.** -/
theorem ae_norm_boxRewardMap_le_yfieldSup3 (ν : Measure ℤ) (hν : CriticalLaw ν) {A : ℝ}
    (hA : 0 ≤ A) (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ η ∂(iidLaw 2 (realLaw ν)),
      ‖boxRewardMap 1 (zero_le_one) A hA n η‖ ≤ yfieldSup3 A hA (happBoxRadius A) n η := by
  filter_upwards [ae_abs_Yfield_le_yfieldSup3 ν hν hA n hn (happBoxRadius A)] with η hη
  refine (ContinuousMap.norm_le _ (yfieldSup3_nonneg A hA (happBoxRadius A) n η)).2 fun p => ?_
  show |orientedBoxReward 1 n η (boxToFin 1 A p)| ≤ _
  have hmem := boxToFin_mem_orientedBox 1 (zero_le_one) A hA p
  rw [← Yfield_eq_of_mem hA n η hmem]
  exact hη (boxToFin 1 A p) (abs_boxToFin_le_happBoxRadius hA p)

/-- **`E_η[‖Parking.boxRewardMap‖]` is bounded, UNIFORM IN the cutoff level `A` and the scale
`n`: `E_η[‖G_n‖] ≤ K * (1 + A) ^ (1/2 + 2/p)` for a SINGLE constant `K`, chosen before `A` and
independent of it.**  Obtained from `Parking.exists_yfieldSup3_L2_moment`'s explicit
`K₀ * (1 + A) ^ (p / 2)` bound on `D`, combined with `Parking.happBoxRadius A ≤ 3 (1 + A) - 1`
and the exponent identity `(p / 2 + 2) / p = 1/2 + 2/p`. -/
theorem exists_integral_norm_boxRewardMap_le (ν : Measure ℤ) (hν : CriticalLaw ν) (p : ℝ)
    (hp : 12 < p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ℝ) (hA : 0 ≤ A) (n : ℕ), 1 ≤ n →
      Integrable (fun η : Site 2 → ℝ => ‖boxRewardMap 1 (zero_le_one) A hA n η‖)
        (iidLaw 2 (realLaw ν)) ∧
      (∫ η, ‖boxRewardMap 1 (zero_le_one) A hA n η‖ ∂(iidLaw 2 (realLaw ν))) ≤
        K * (1 + A) ^ (1 / 2 + 2 / p) := by
  haveI : IsProbabilityMeasure ν := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI : IsProbabilityMeasure (iidLaw 2 (realLaw ν)) := by unfold iidLaw; infer_instance
  have hp0 : (0:ℝ) < p := by linarith
  obtain ⟨K0, hK0nn, hK0all⟩ := exists_yfieldSup3_L2_moment ν hν p hp
  refine ⟨(9 * K0) ^ (1 / p), by positivity, fun A hA n hn => ?_⟩
  obtain ⟨D, hDnn, hDbd, hbound⟩ := hK0all A hA
  set R : ℕ := happBoxRadius A with hRdef
  obtain ⟨hYsqint, hYsqbound⟩ := hbound R n hn
  set Y : (Site 2 → ℝ) → ℝ := fun η => yfieldSup3 A hA R n η with hYdef
  set Gn : (Site 2 → ℝ) → ℝ := fun η => ‖boxRewardMap 1 (zero_le_one) A hA n η‖ with hGndef
  have hGnnn : ∀ η, 0 ≤ Gn η := fun η => norm_nonneg _
  have hYnn : ∀ η, 0 ≤ Y η := fun η => yfieldSup3_nonneg A hA R n η
  have hGnleY : ∀ᵐ η ∂(iidLaw 2 (realLaw ν)), Gn η ≤ Y η :=
    ae_norm_boxRewardMap_le_yfieldSup3 ν hν hA n hn
  have hGnaesm : AEStronglyMeasurable Gn (iidLaw 2 (realLaw ν)) :=
    (measurable_boxRewardMap 1 (zero_le_one) A hA n).norm.aestronglyMeasurable
  have hYaesm : AEStronglyMeasurable Y (iidLaw 2 (realLaw ν)) :=
    aestronglyMeasurable_yfieldSup3 ν hν hA R n hn
  have hYint : Integrable Y (iidLaw 2 (realLaw ν)) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hYsqint) hYaesm ?_
    filter_upwards with η
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (hYnn η)]
    nlinarith [sq_nonneg (Y η - 1)]
  have hGnint : Integrable Gn (iidLaw 2 (realLaw ν)) :=
    Integrable.mono' hYint hGnaesm (by
      filter_upwards [hGnleY] with η hη
      rw [Real.norm_eq_abs, abs_of_nonneg (hGnnn η)]
      exact hη)
  have hGnsqle : ∀ᵐ η ∂(iidLaw 2 (realLaw ν)), (Gn η) ^ 2 ≤ (Y η) ^ 2 := by
    filter_upwards [hGnleY] with η hη
    exact pow_le_pow_left₀ (hGnnn η) hη 2
  have hGnsqint : Integrable (fun η => (Gn η) ^ 2) (iidLaw 2 (realLaw ν)) := by
    refine Integrable.mono' hYsqint ((continuous_pow 2).comp_aestronglyMeasurable hGnaesm) ?_
    filter_upwards [hGnsqle] with η hη
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hη
  refine ⟨hGnint, ?_⟩
  have hGnrpow1eq : (fun η => |Gn η| ^ (1 : ℝ)) = Gn := by
    funext η; rw [abs_of_nonneg (hGnnn η), Real.rpow_one]
  have hGnrpow1int : Integrable (fun η => |Gn η| ^ (1 : ℝ)) (iidLaw 2 (realLaw ν)) := by
    rw [hGnrpow1eq]; exact hGnint
  have hGnrpow2eq : (fun η => |Gn η| ^ (2 : ℝ)) = fun η => (Gn η) ^ 2 := by
    funext η
    rw [abs_of_nonneg (hGnnn η), ← Real.rpow_natCast (Gn η) 2]
    norm_num
  have hGnrpow2int : Integrable (fun η => |Gn η| ^ (2 : ℝ)) (iidLaw 2 (realLaw ν)) := by
    rw [hGnrpow2eq]; exact hGnsqint
  have hmono1 := rNorm_mono_exponent (iidLaw 2 (realLaw ν)) (le_refl (1 : ℝ)) (by norm_num : (1:ℝ) ≤ 2)
    Gn hGnaesm hGnrpow1int hGnrpow2int
  have hrnorm1eq : rNorm (iidLaw 2 (realLaw ν)) 1 Gn = ∫ η, Gn η ∂(iidLaw 2 (realLaw ν)) := by
    unfold rNorm
    rw [hGnrpow1eq]
    simp
  have hmono2 : rNorm (iidLaw 2 (realLaw ν)) 2 Gn ≤ rNorm (iidLaw 2 (realLaw ν)) 2 Y :=
    rNorm_mono (iidLaw 2 (realLaw ν)) (by norm_num : (0:ℝ) < 2)
      (Filter.Eventually.mono hGnleY fun η hη => by
        rw [abs_of_nonneg (hGnnn η), abs_of_nonneg (hYnn η)]; exact hη)
      (by
        have heq : (fun η => |Y η| ^ (2:ℝ)) = fun η => (Y η) ^ 2 := by
          funext η
          rw [abs_of_nonneg (hYnn η), ← Real.rpow_natCast (Y η) 2]; norm_num
        rw [heq]; exact hYsqint)
  have hrnorm2Yeq : rNorm (iidLaw 2 (realLaw ν)) 2 Y = (∫ η, (Y η) ^ 2 ∂(iidLaw 2 (realLaw ν))) ^ ((1:ℝ)/2) := by
    unfold rNorm
    congr 1
    apply integral_congr_ae
    filter_upwards with η
    rw [abs_of_nonneg (hYnn η), ← Real.rpow_natCast (Y η) 2]
    norm_num
  have hYsqbound2 : (∫ η, (Y η) ^ 2 ∂(iidLaw 2 (realLaw ν))) ≤ (D * (((R:ℝ)+1)^2)) ^ (2/p) := hYsqbound
  have hfin : ((∫ η, (Y η) ^ 2 ∂(iidLaw 2 (realLaw ν))) ) ^ ((1:ℝ)/2)
      ≤ ((D * (((R:ℝ)+1)^2)) ^ (2/p)) ^ ((1:ℝ)/2) :=
    Real.rpow_le_rpow (integral_nonneg fun η => sq_nonneg _) hYsqbound2 (by norm_num)
  have hDR2nn : (0:ℝ) ≤ D * (((R:ℝ)+1)^2) := by positivity
  have hpow_eq : ((D * (((R:ℝ)+1)^2)) ^ (2/p)) ^ ((1:ℝ)/2) = (D * (((R:ℝ)+1)^2)) ^ (1/p) := by
    rw [← Real.rpow_mul hDR2nn]
    congr 1
    field_simp
  rw [hpow_eq] at hfin
  have hcore : (∫ η, Gn η ∂(iidLaw 2 (realLaw ν))) ≤ (D * (((R:ℝ)+1)^2)) ^ (1/p) := by
    calc (∫ η, Gn η ∂(iidLaw 2 (realLaw ν)))
        = rNorm (iidLaw 2 (realLaw ν)) 1 Gn := hrnorm1eq.symm
      _ ≤ rNorm (iidLaw 2 (realLaw ν)) 2 Gn := hmono1
      _ ≤ rNorm (iidLaw 2 (realLaw ν)) 2 Y := hmono2
      _ = (∫ η, (Y η) ^ 2 ∂(iidLaw 2 (realLaw ν))) ^ ((1:ℝ)/2) := hrnorm2Yeq
      _ ≤ (D * (((R:ℝ)+1)^2)) ^ (1/p) := hfin
  -- Convert the `(D · (R+1)²)^(1/p)` bound into `K · (1 + A) ^ (1/2 + 2/p)`, using
  -- `D ≤ K0 · (1+A)^(p/2)` and `R + 1 ≤ 3 (1+A)`.
  have hRbound : ((R:ℝ) + 1) ≤ 3 * (1 + A) := by
    rw [hRdef]
    unfold happBoxRadius
    have h1 : ((⌈2 * A⌉₊ : ℕ) : ℝ) ≤ 2 * A + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    push_cast
    linarith [h1]
  have hR2 : ((R:ℝ) + 1) ^ 2 ≤ (3 * (1 + A)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hRbound 2
  have hcast2 : (1 + A) ^ (2:ℕ) = (1 + A) ^ ((2:ℝ)) := by
    rw [← Real.rpow_natCast (1 + A) 2]; norm_num
  have hcombine : (1 + A) ^ (p / 2) * (1 + A) ^ (2:ℕ) = (1 + A) ^ (p / 2 + 2) := by
    rw [hcast2, ← Real.rpow_add (by linarith : (0:ℝ) < 1 + A)]
  have hDR2bound : D * (((R:ℝ)+1)^2) ≤ (9 * K0) * (1 + A) ^ (p / 2 + 2) := by
    calc D * (((R:ℝ)+1)^2)
        ≤ (K0 * (1 + A) ^ (p / 2)) * (3 * (1 + A)) ^ 2 :=
          mul_le_mul hDbd hR2 (by positivity) (by positivity)
      _ = K0 * 9 * ((1 + A) ^ (p / 2) * (1 + A) ^ (2:ℕ)) := by ring
      _ = K0 * 9 * (1 + A) ^ (p / 2 + 2) := by rw [hcombine]
      _ = (9 * K0) * (1 + A) ^ (p / 2 + 2) := by ring
  have hfinal2 : (D * (((R:ℝ)+1)^2)) ^ (1/p) ≤ ((9 * K0) * (1 + A) ^ (p / 2 + 2)) ^ (1/p) :=
    Real.rpow_le_rpow hDR2nn hDR2bound (by positivity)
  have heqfinal : ((9 * K0) * (1 + A) ^ (p / 2 + 2)) ^ (1/p) =
      (9 * K0) ^ (1/p) * (1 + A) ^ (1 / 2 + 2 / p) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by linarith : (0:ℝ) ≤ 1 + A)]
    congr 2
    field_simp
  rw [heqfinal] at hfinal2
  exact hcore.trans hfinal2

end Parking

end
