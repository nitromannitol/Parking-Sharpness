import Parking.Support.LinInterp
import Parking.Support.SandpileNoiseBridge
import Parking.Support.SpatWSceneryFdd
import Parking.Support.LinHatMeasurable
import Parking.Support.UConcBridge
import Parking.Support.CriticalLawReal
import Parking.Support.LinCovariance
import Parking.External.CriticalScaleLowerTailProved
import LatticeProb.Prob.FiniteMarginal
import Sandpile.Support.HeatPotentialDefs
import Sandpile.Support.ContVectorCLT
import Sandpile.Support.ContContinuumMCT
import Sandpile.Support.ContGreenFubini
import Sandpile.Support.ContHeatPotentialFD
import Sandpile.Support.ContInterpSmall
import Sandpile.Support.ContBMGreenIdentity
import Sandpile.Support.ContBMSquare
import Sandpile.Support.ContSeqCLT
import Sandpile.External.LocalCLTProved

/-!
# The interpolated linear field and its finite-dimensional limit

`linHatInterpBridge` identifies the interpolated rescaled linear field `Parking.linHatInterp`
with the interpolated field `Sandpile.Frozen.HeatPotentialInvariance.linInterp` of the
divisible sandpile at nonnegative times: the grid values agree because the linear membrane
field `Parking.linPotential` is the Green-function sum `∑ y, g_n(x, y) ζ(y)`, and the
piecewise multilinear interpolation `Parking.hatInterpD` reads off, at every space-time point,
the same corner values with the same weights as `linInterp`.

`jointLinearFdd_of_sceneryCovarianceLimit` derives the joint finite-dimensional convergence of
the scenery pairings `⟨η_R, φ_i⟩` and the interpolated linear field at finitely many space-time
points from the two scenery covariance limits. Both families are finite linear functionals of
the scenery over one common box, so the vector Lindeberg-Feller step
`Sandpile.Support.tendstoInDistribution_vector_pick_mass` applies once the coefficient pairings
converge: the scenery-scenery and scenery-field pairings by the covariance limits and the
orthogonality identity of the i.i.d. scenery, the field-field pairings by the lattice double time
sums of the divisible sandpile, which converge to the `L²` pairings of the Brownian Green
kernels. The limit is then transported from the sandpile mass law to `Parking.law`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Parking.Support

open Parking

variable {d : ℕ}

/-- The hat weight of the lower floor corner is one minus the fractional part. -/
theorem hat1_sub_floor (t : ℝ) : hat1 (t - (⌊t⌋ : ℝ)) = 1 - (t - ⌊t⌋) := by
  unfold hat1
  rw [abs_of_nonneg (by linarith [Int.floor_le t] : (0 : ℝ) ≤ t - ⌊t⌋)]
  exact max_eq_right (by linarith [Int.lt_floor_add_one t])

/-- The hat weight of the upper floor corner is the fractional part. -/
theorem hat1_sub_floor_add_one (t : ℝ) : hat1 (t - ((⌊t⌋ + 1 : ℤ) : ℝ)) = t - ⌊t⌋ := by
  have hc : ((⌊t⌋ + 1 : ℤ) : ℝ) = (⌊t⌋ : ℝ) + 1 := by push_cast; ring
  rw [hc]
  unfold hat1
  rw [abs_of_nonpos (by linarith [Int.lt_floor_add_one t] : t - ((⌊t⌋ : ℝ) + 1) ≤ 0)]
  rw [max_eq_right (by linarith [Int.floor_le t] : (0 : ℝ) ≤ 1 - -(t - ((⌊t⌋ : ℝ) + 1)))]
  ring

/-- The joint interpolation written over the `2 ^ d` space corners, indexed by `Fin d → Bool`,
with the two time corners combined by their fractional weights. -/
theorem hatInterpD_eq_sum_bool (V : ℤ → Site d → ℝ) (u : ℝ × (Fin d → ℝ)) :
    hatInterpD V u = ∑ ε : Fin d → Bool,
      (∏ i : Fin d, if ε i then u.2 i - (⌊u.2 i⌋ : ℝ) else 1 - (u.2 i - (⌊u.2 i⌋ : ℝ))) *
        ((1 - (u.1 - (⌊u.1⌋ : ℝ))) * V ⌊u.1⌋ (fun i => ⌊u.2 i⌋ + if ε i then 1 else 0) +
          (u.1 - (⌊u.1⌋ : ℝ)) * V (⌊u.1⌋ + 1) (fun i => ⌊u.2 i⌋ + if ε i then 1 else 0)) := by
  classical
  set c : (Fin d → Bool) → Site d := fun ε i => ⌊u.2 i⌋ + if ε i then 1 else 0 with hc
  have hinj : Function.Injective c := by
    intro ε ε' h
    funext i
    have hi := congrFun h i
    simp only [hc] at hi
    cases hε : ε i <;> cases hε' : ε' i <;> simp_all
  have h₂ : ∀ c' : Site d, hatProd u.2 c' ≠ 0 → c' ∈ Finset.univ.image c := by
    intro c' hc'
    refine Finset.mem_image.mpr ⟨fun i => decide (c' i = ⌊u.2 i⌋ + 1), Finset.mem_univ _, ?_⟩
    funext i
    rcases hatProd_ne_zero_mem_box hc' i with h | h
    · simp [hc, h]
    · simp [hc, h]
  rw [hatInterpD_eq_sum V u {⌊u.1⌋, ⌊u.1⌋ + 1} (Finset.univ.image c)
    (fun m hm => by
      rcases hat1_ne_zero_mem_floor_pair hm with h | h <;> simp [h]) h₂]
  rw [Finset.sum_pair (by omega : (⌊u.1⌋ : ℤ) ≠ ⌊u.1⌋ + 1),
    Finset.sum_image (fun ε _ ε' _ h => hinj h), Finset.sum_image (fun ε _ ε' _ h => hinj h),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ε _ => ?_
  have hP : hatProd u.2 (c ε) =
      ∏ i : Fin d, if ε i then u.2 i - (⌊u.2 i⌋ : ℝ) else 1 - (u.2 i - (⌊u.2 i⌋ : ℝ)) := by
    unfold hatProd
    refine Finset.prod_congr rfl fun i _ => ?_
    cases hε : ε i
    · simp only [hc, hε, Bool.false_eq_true, ite_false, add_zero]
      exact hat1_sub_floor (u.2 i)
    · simp only [hc, hε, ite_true]
      exact hat1_sub_floor_add_one (u.2 i)
  rw [hP, hat1_sub_floor, hat1_sub_floor_add_one]
  ring

/-- The linear membrane field and the floor-free linear evolution are the same recursion. -/
theorem linPotential_eq_cslt_linear (η : Site d → ℝ) :
    ∀ n : ℕ, linPotential η n = Parking.External.cslt_linear η n
  | 0 => rfl
  | n + 1 => by
      funext x
      rw [linPotential_succ, linPotential_eq_cslt_linear η n]
      rfl

/-- The linear membrane field is the Green-function sum of the source. -/
theorem linPotential_eq_tsum_greenTime (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    linPotential η n x = ∑' y, Sandpile.greenTime d n x y * η y := by
  rw [linPotential_eq_cslt_linear]
  exact Parking.External.cslt_linear_green η n x

/-- **The Parking interpolated linear field is the sandpile one at nonnegative times.** -/
theorem linHatInterpBridge :
    ∀ (d : ℕ) (ζ : Sandpile.Site d → ℝ) (R : ℝ), 1 ≤ R → ∀ p : ℝ × (Fin d → ℝ), 0 ≤ p.1 →
      Parking.linHatInterp ζ R p =
        Sandpile.Frozen.HeatPotentialInvariance.linInterp d R ζ p.1 (WithLp.toLp 2 p.2) := by
  intro d ζ R _ p hp
  have hu : 0 ≤ R ^ 2 * p.1 := mul_nonneg (sq_nonneg R) hp
  rw [linHatInterp, hatInterpD_eq_sum_bool]
  simp only [Sandpile.Frozen.HeatPotentialInvariance.linInterp,
    Sandpile.Frozen.HeatPotentialInvariance.meshValue]
  rw [← Int.natCast_floor_eq_floor hu]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [show ((⌊R ^ 2 * p.1⌋₊ : ℤ) + 1).toNat = ⌊R ^ 2 * p.1⌋₊ + 1 by omega,
    Int.toNat_natCast, linPotential_eq_tsum_greenTime, linPotential_eq_tsum_greenTime]
  push_cast
  ring

/-! ### Laws and covariances of finite linear functionals of the scenery -/

/-- The affine change from scenery to mass is measurable. -/
theorem measurable_massField :
    Measurable (fun w : Data d => fun y : Site d => 1 + 2 * (d : ℝ) * (w.1 y : ℝ)) :=
  Measurable.of_eval fun y =>
    measurable_const.add (measurable_const.mul ((measurable_pi_apply y).comp measurable_confReal))

/-- The mass field induced by the parking law has the centred sandpile mass law. -/
theorem law_map_massField (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    (law d ν).map (fun w : Data d => fun y : Site d => 1 + 2 * (d : ℝ) * (w.1 y : ℝ)) =
      Sandpile.centeredMassLaw d (ν.map (fun k : ℤ => (k : ℝ))) := by
  have hF : Measurable (fun (η : Site d → ℝ) (y : Site d) => 1 + 2 * (d : ℝ) * η y) :=
    Measurable.of_eval fun y => measurable_const.add (measurable_const.mul (measurable_pi_apply y))
  change (law d ν).map ((fun (η : Site d → ℝ) (y : Site d) => 1 + 2 * (d : ℝ) * η y) ∘
    (fun w : Data d => confReal w)) = _
  rw [← Measure.map_map hF measurable_confReal, law_map_confReal hd ν]
  unfold Sandpile.centeredMassLaw Sandpile.massLaw LatticeProb.iidLaw
  exact Measure.infinitePi_map_pi _
    (fun _ => measurable_const.add (measurable_const.mul measurable_id))

/-- The scenery of the mass field `1 + 2dη` is `η`. -/
theorem scenery_massField (hd : 1 ≤ d) (η : Site d → ℝ) :
    Sandpile.scenery d (fun y => 1 + 2 * (d : ℝ) * η y) = η := by
  have hd0 : (2 * (d : ℝ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (by omega))
  funext y
  simp only [Sandpile.scenery]
  field_simp
  ring

/-- **The orthogonality identity under the parking law.**  Two finite linear functionals of
the scenery at distinct sites have covariance the variance of the one-site law times the sum of
the coefficient products. -/
theorem integral_pick_mul_pick (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν) {N : ℕ}
    (e : Fin N → Site d) (he : Function.Injective e) (α β : Fin N → ℝ) :
    ∫ w, (∑ k, α k * (w.1 (e k) : ℝ)) * (∑ k, β k * (w.1 (e k) : ℝ)) ∂(law d ν)
      = (∑ k, α k * β k) * ∫ x, x ^ 2 ∂(ν.map (fun k : ℤ => (k : ℝ))) := by
  have := hν.prob
  have : IsProbabilityMeasure (ν.map (fun k : ℤ => (k : ℝ))) := realLaw_isProbability ν
  have hsq : MemLp (id : ℝ → ℝ) 2 (ν.map (fun k : ℤ => (k : ℝ))) := realLaw_memLp_two ν hν
  have hpick : Measurable (fun (σ : Site d → ℝ) (k : Fin N) => σ (e k)) :=
    Measurable.of_eval fun k => measurable_pi_apply (e k)
  have hPm : Measurable (fun (w : Data d) (k : Fin N) => (w.1 (e k) : ℝ)) :=
    hpick.comp measurable_confReal
  have hmap : (law d ν).map (fun (w : Data d) (k : Fin N) => (w.1 (e k) : ℝ)) =
      Measure.pi fun _ : Fin N => ν.map (fun k : ℤ => (k : ℝ)) := by
    change (law d ν).map ((fun (σ : Site d → ℝ) (k : Fin N) => σ (e k)) ∘
      (fun w : Data d => confReal w)) = _
    rw [← Measure.map_map hpick measurable_confReal, law_map_confReal hd ν]
    exact LatticeProb.infinitePi_map_comp _ e he
  have hf : Measurable (fun ξ : Fin N → ℝ => (∑ k, α k * ξ k) * (∑ k, β k * ξ k)) := by
    fun_prop
  calc ∫ w, (∑ k, α k * (w.1 (e k) : ℝ)) * (∑ k, β k * (w.1 (e k) : ℝ)) ∂(law d ν)
      = ∫ ξ, (∑ k, α k * ξ k) * (∑ k, β k * ξ k)
          ∂((law d ν).map (fun (w : Data d) (k : Fin N) => (w.1 (e k) : ℝ))) :=
        (integral_map hPm.aemeasurable hf.aestronglyMeasurable).symm
    _ = (∑ k, α k * β k) * ∫ x, x ^ 2 ∂(ν.map (fun k : ℤ => (k : ℝ))) := by
        rw [hmap]
        exact integral_sum_mul_sum_pi α β _ (realLaw_mean ν hν) (hsq.integrable one_le_two)
          hsq.integrable_sq

/-- Convergence in distribution is carried along a measurable map pushing one law to
another. -/
theorem tendstoInDistribution_comp_of_map_eq {ι Ω₀ Ω Ω' E : Type*} [MeasurableSpace Ω₀]
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] {l : Filter ι} {X : ι → Ω → E} {Z : Ω' → E}
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {T : Ω₀ → Ω} (hT : Measurable T)
    (hmap : μ₀.map T = μ) (h : TendstoInDistribution X l Z (fun _ => μ) μ') :
    TendstoInDistribution (fun i ω => X i (T ω)) l Z (fun _ => μ₀) μ' := by
  subst hmap
  refine ⟨fun i => (h.forall_aemeasurable i).comp_measurable hT, h.aemeasurable_limit, ?_⟩
  refine h.tendsto.congr fun i => ?_
  apply ProbabilityMeasure.toMeasure_injective
  exact AEMeasurable.map_map_of_aemeasurable (h.forall_aemeasurable i) hT.aemeasurable

/-! ### Finite sums -/

/-- The sum of squares of a combination of coefficient vectors, expanded into the matrix of
coefficient pairings. -/
theorem sum_sq_sum_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (t : ι → ℝ) (a : ι → κ → ℝ) :
    ∑ k, (∑ i, t i * a i k) ^ 2 = ∑ i, ∑ i', t i * t i' * ∑ k, a i k * a i' k := by
  calc ∑ k, (∑ i, t i * a i k) ^ 2 = ∑ k, ∑ i, ∑ i', t i * t i' * (a i k * a i' k) :=
        Finset.sum_congr rfl fun k _ => by
          rw [sq, Finset.sum_mul_sum]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring
    _ = ∑ i, ∑ k, ∑ i', t i * t i' * (a i k * a i' k) := Finset.sum_comm
    _ = ∑ i, ∑ i', ∑ k, t i * t i' * (a i k * a i' k) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ i', t i * t i' * ∑ k, a i k * a i' k :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
          (Finset.mul_sum _ _ _).symm

/-- The integral of the square of a combination of functions with integrable pairwise
products, expanded into the matrix of their pairings. -/
theorem integral_sum_mul_sum_eq {ι α : Type*} [Fintype ι] [MeasurableSpace α] {μ : Measure α}
    (t : ι → ℝ) (g : ι → α → ℝ) (hg : ∀ i i', Integrable (fun y => g i y * g i' y) μ) :
    ∫ y, (∑ i, t i * g i y) * ∑ i, t i * g i y ∂μ =
      ∑ i, ∑ i', t i * t i' * ∫ y, g i y * g i' y ∂μ := by
  calc ∫ y, (∑ i, t i * g i y) * ∑ i, t i * g i y ∂μ
      = ∫ y, ∑ i, ∑ i', t i * t i' * (g i y * g i' y) ∂μ := by
        congr 1
        funext y
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring
    _ = ∑ i, ∫ y, ∑ i', t i * t i' * (g i y * g i' y) ∂μ :=
        integral_finsetSum _ fun i _ => integrable_finsetSum _ fun i' _ =>
          (hg i i').const_mul _
    _ = ∑ i, ∑ i', ∫ y, t i * t i' * (g i y * g i' y) ∂μ :=
        Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun i' _ => (hg i i').const_mul _
    _ = ∑ i, ∑ i', t i * t i' * ∫ y, g i y * g i' y ∂μ :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => integral_const_mul _ _

/-! ### The common box and the joint coefficients -/

/-- A site whose coordinates are at most `|R| L` in absolute value lies in the interpolation
box. -/
theorem mem_interpBox_of_abs_le {R L : ℝ} {p : ℕ} (r : Fin p → ℝ) (y : Site d)
    (hy : ∀ l, |(y l : ℝ)| ≤ |R| * L) : y ∈ Sandpile.Support.interpBox d R L r := by
  unfold Sandpile.Support.interpBox
  apply Sandpile.mem_boxFinset
  unfold Sandpile.boxDist
  refine Finset.sup_le fun l _ => ?_
  have h1 : ((0 : Site d) l - y l).natAbs = (y l).natAbs := by simp
  have h2 : ((y l).natAbs : ℝ) ≤ (⌈|R| * L⌉₊ : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact (hy l).trans (Nat.le_ceil _)
  have h3 : (y l).natAbs ≤ ⌈|R| * L⌉₊ := by exact_mod_cast h2
  rw [h1]
  omega

/-- A scenery pairing against a function vanishing off a finite set of sites is the finite
sum over an enumeration of that set. -/
theorem scenePair_eq_sum_siteEnum {R : ℝ} {φ : (Fin d → ℝ) → ℝ} {s : Finset (Site d)}
    (hs : ∀ y ∉ s, φ (fun l => (y l : ℝ) / R) = 0) (w : Data d) :
    scenePair w R φ = ∑ k : Fin s.card, (R ^ (-(d : ℝ) / 2) *
      φ (fun l => (Sandpile.siteEnum s k l : ℝ) / R)) *
        (w.1 (Sandpile.siteEnum s k) : ℝ) := by
  have hsum : ∑' y : Site d, (w.1 y : ℝ) * φ (fun l => (y l : ℝ) / R) =
      ∑ y ∈ s, (w.1 y : ℝ) * φ (fun l => (y l : ℝ) / R) :=
    tsum_eq_sum fun y hy => by rw [hs y hy, mul_zero]
  unfold scenePair
  rw [hsum, ← Sandpile.sum_siteEnum s]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The coefficients of the joint vector of scenery pairings and interpolated linear field
values against the scenery on the common interpolation box, the scenery pairings first. -/
def jointFddCoeff {m p : ℕ} (φ : Fin m → (Fin d → ℝ) → ℝ) (sp : Fin p → ℝ × (Fin d → ℝ))
    (L R : ℝ) :
    Fin (m + p) → Fin (Sandpile.Support.interpBox d R L (fun j => (sp j).1)).card → ℝ :=
  Fin.append
    (fun i k => R ^ (-(d : ℝ) / 2) * φ i (fun l =>
      (Sandpile.siteEnum (Sandpile.Support.interpBox d R L (fun j => (sp j).1)) k l : ℝ) /
        R))
    (fun j k => Sandpile.Support.interpCoeff d R (sp j).1 (WithLp.toLp 2 (sp j).2)
      (Sandpile.siteEnum (Sandpile.Support.interpBox d R L (fun j => (sp j).1)) k))

/-- The scenery-pairing coefficients of the joint vector. -/
theorem jointFddCoeff_castAdd {m p : ℕ} (φ : Fin m → (Fin d → ℝ) → ℝ)
    (sp : Fin p → ℝ × (Fin d → ℝ)) (L R : ℝ) (i : Fin m)
    (k : Fin (Sandpile.Support.interpBox d R L (fun j => (sp j).1)).card) :
    jointFddCoeff φ sp L R (Fin.castAdd p i) k = R ^ (-(d : ℝ) / 2) * φ i (fun l =>
      (Sandpile.siteEnum (Sandpile.Support.interpBox d R L (fun j => (sp j).1)) k l : ℝ) /
        R) := by
  simp only [jointFddCoeff, Fin.append_left]

/-- The linear-field coefficients of the joint vector. -/
theorem jointFddCoeff_natAdd {m p : ℕ} (φ : Fin m → (Fin d → ℝ) → ℝ)
    (sp : Fin p → ℝ × (Fin d → ℝ)) (L R : ℝ) (j : Fin p)
    (k : Fin (Sandpile.Support.interpBox d R L (fun j => (sp j).1)).card) :
    jointFddCoeff φ sp L R (Fin.natAdd m j) k =
      Sandpile.Support.interpCoeff d R (sp j).1 (WithLp.toLp 2 (sp j).2)
        (Sandpile.siteEnum (Sandpile.Support.interpBox d R L (fun j => (sp j).1)) k) := by
  simp only [jointFddCoeff, Fin.append_right]

/-- The limiting kernels of the joint vector: the test functions in Euclidean coordinates, then
the Brownian Green kernels at the space-time points. -/
def jointFddKernel {m p : ℕ} (φ : Fin m → (Fin d → ℝ) → ℝ) (sp : Fin p → ℝ × (Fin d → ℝ)) :
    Fin (m + p) → Sandpile.Continuum.Space d → ℝ :=
  Fin.append (fun i y => φ i (WithLp.ofLp y))
    (fun j y => Sandpile.Continuum.greenTimeBM d (sp j).1 (WithLp.toLp 2 (sp j).2) y)

/-- The test-function kernels of the joint limit. -/
theorem jointFddKernel_castAdd {m p : ℕ} (φ : Fin m → (Fin d → ℝ) → ℝ)
    (sp : Fin p → ℝ × (Fin d → ℝ)) (i : Fin m) :
    jointFddKernel φ sp (Fin.castAdd p i) = fun y => φ i (WithLp.ofLp y) := by
  simp only [jointFddKernel, Fin.append_left]

/-- The Brownian Green kernels of the joint limit. -/
theorem jointFddKernel_natAdd {m p : ℕ} (φ : Fin m → (Fin d → ℝ) → ℝ)
    (sp : Fin p → ℝ × (Fin d → ℝ)) (j : Fin p) :
    jointFddKernel φ sp (Fin.natAdd m j) =
      fun y => Sandpile.Continuum.greenTimeBM d (sp j).1 (WithLp.toLp 2 (sp j).2) y := by
  simp only [jointFddKernel, Fin.append_right]

/-! ### The joint finite-dimensional limit -/

/-- **Joint finite-dimensional convergence of the scenery pairings and the interpolated linear
field**, from the scenery covariance limits. -/
theorem jointLinearFdd_of_sceneryCovarianceLimit
    (hSC : ∀ (d : ℕ), 1 ≤ d → d ≤ 3 → ∀ (ν : Measure ℤ), Parking.CriticalLaw ν →
      (∀ φ ψ, Parking.IsTestFun φ → Parking.IsTestFun ψ →
        Tendsto (fun R : ℝ => ∫ w, Parking.scenePair w R φ * Parking.scenePair w R ψ
            ∂(Parking.law d ν)) atTop
          (𝓝 (variance (fun k : ℤ => (k : ℝ)) ν * ∫ y, φ y * ψ y))) ∧
      ∀ φ, Parking.IsTestFun φ → ∀ (r : ℝ) (x : Fin d → ℝ), 0 ≤ r →
        Tendsto (fun R : ℝ => ∫ w, Parking.scenePair w R φ *
            Parking.linHatInterp (fun y => (w.1 y : ℝ)) R (r, x) ∂(Parking.law d ν)) atTop
          (𝓝 (variance (fun k : ℤ => (k : ℝ)) ν *
            ∫ y, φ y * Parking.External.contFiniteGreen d r x y))) :
    ∀ (d : ℕ), 1 ≤ d → d ≤ 3 →
      ∀ (ν : Measure ℤ) [IsProbabilityMeasure (Parking.law d ν)], Parking.CriticalLaw ν →
      ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
        (WD : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ),
        Sandpile.Continuum.IsWhiteNoise d WD PW →
      ∀ (m p' : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ) (sp : Fin p' → ℝ × (Fin d → ℝ)),
        (∀ i, Parking.IsTestFun (φ i)) → (∀ j, 0 ≤ (sp j).1) →
        TendstoInDistribution
          (fun (R : ℝ) (w : Parking.Data d) =>
            ((fun i => Parking.scenePair w R (φ i)),
              (fun j => Parking.linHatInterp (fun y => (w.1 y : ℝ)) R (sp j))))
          atTop
          (fun ω =>
            ((fun i => Real.sqrt (variance (fun k : ℤ => (k : ℝ)) ν) *
                WD (fun y => φ i (WithLp.ofLp y)) ω),
              (fun j => Sandpile.Continuum.gaussianPotential d
                (variance (fun k : ℤ => (k : ℝ)) ν) WD (sp j).1 (WithLp.toLp 2 (sp j).2) ω)))
          (fun _ => Parking.law d ν) PW := by
  intro d hd hd3 ν _ hν ΩW _ PW _ WD hW m p' φ sp hφ hsp
  classical
  have := hν.prob
  have : IsProbabilityMeasure (ν.map (fun k : ℤ => (k : ℝ))) := realLaw_isProbability ν
  obtain ⟨hSS, hSF⟩ := hSC d hd hd3 ν hν
  have hsq : MemLp (id : ℝ → ℝ) 2 (ν.map (fun k : ℤ => (k : ℝ))) := realLaw_memLp_two ν hν
  have hmean : ∫ z, z ∂(ν.map (fun k : ℤ => (k : ℝ))) = 0 := realLaw_mean ν hν
  set v : ℝ := variance (fun k : ℤ => (k : ℝ)) ν with hvdef
  have hvid : variance (id : ℝ → ℝ) (ν.map (fun k : ℤ => (k : ℝ))) = v :=
    variance_id_map measurable_intCastReal.aemeasurable
  have hv2 : ∫ z, z ^ 2 ∂(ν.map (fun k : ℤ => (k : ℝ))) = v := by
    rw [← hvid, variance_eq_sub hsq]
    have h1 : ∫ z, ((id : ℝ → ℝ) ^ 2) z ∂(ν.map (fun k : ℤ => (k : ℝ))) =
        ∫ z, z ^ 2 ∂(ν.map (fun k : ℤ => (k : ℝ))) := rfl
    have h2 : ∫ z, (id : ℝ → ℝ) z ∂(ν.map (fun k : ℤ => (k : ℝ))) = 0 := hmean
    rw [h1, h2]
    ring
  have hvpos : 0 < v := by
    rw [← hvid]
    exact ENNReal.toReal_pos (realLaw_evariance_pos ν hν).ne' (realLaw_evariance_lt_top ν hν).ne
  -- support radius and sup bound of the test functions
  have hsupp : ∀ i, ∃ ρ : ℝ, ∀ x, φ i x ≠ 0 → ‖x‖ ≤ ρ := by
    intro i
    obtain ⟨ρ, hρ⟩ := (hφ i).2.isCompact.isBounded.subset_closedBall 0
    exact ⟨ρ, fun x hx => by simpa using hρ (subset_tsupport _ hx)⟩
  choose ρ hρ using hsupp
  have hbdd : ∀ i, ∃ C : ℝ, ∀ x, ‖φ i x‖ ≤ C := fun i =>
    (hφ i).1.continuous.bounded_above_of_compact_support (hφ i).2
  choose C hC using hbdd
  set L₀ : ℝ := ∑ i, |ρ i| with hL₀def
  set M : ℝ := ∑ i, |C i| with hMdef
  have hL₀ : ∀ i x, φ i x ≠ 0 → ‖x‖ ≤ L₀ := fun i x hx =>
    (hρ i x hx).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |ρ i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)))
  have hM : ∀ i x, |φ i x| ≤ M := fun i x => by
    have h := hC i x
    rw [Real.norm_eq_abs] at h
    exact h.trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)))
  set L : ℝ := L₀ + ∑ j, ‖(WithLp.toLp 2 (sp j).2 : Sandpile.Continuum.Space d)‖ with hLdef
  have hw : ∀ j, ‖(WithLp.toLp 2 (sp j).2 : Sandpile.Continuum.Space d)‖ ≤ L := by
    intro j
    have h1 := Finset.single_le_sum
      (f := fun j => ‖(WithLp.toLp 2 (sp j).2 : Sandpile.Continuum.Space d)‖)
      (fun j _ => norm_nonneg _) (Finset.mem_univ j)
    have h2 : 0 ≤ L₀ := Finset.sum_nonneg fun i _ => abs_nonneg _
    simp only [hLdef]
    linarith
  have hL₀L : L₀ ≤ L := by
    have h := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) =>
      norm_nonneg (WithLp.toLp 2 (sp j).2 : Sandpile.Continuum.Space d)
    simp only [hLdef]
    linarith
  -- the scenery pairings read only the sites of the common box
  have hvanish : ∀ R : ℝ, 0 < R → ∀ i (y : Site d),
      y ∉ Sandpile.Support.interpBox d R L (fun j => (sp j).1) →
        φ i (fun l => (y l : ℝ) / R) = 0 := by
    intro R hR i y hy
    by_contra hne
    refine hy (mem_interpBox_of_abs_le _ y fun l => ?_)
    have h1 := hL₀ i _ hne
    have h2 : |(y l : ℝ) / R| ≤ L₀ := by
      have h := norm_le_pi_norm (fun l => (y l : ℝ) / R) l
      rw [Real.norm_eq_abs] at h
      exact h.trans h1
    rw [abs_div, abs_of_pos hR, div_le_iff₀ hR] at h2
    rw [abs_of_pos hR]
    calc |(y l : ℝ)| ≤ L₀ * R := h2
      _ ≤ L * R := mul_le_mul_of_nonneg_right hL₀L hR.le
      _ = R * L := mul_comm _ _
  have hSrep : ∀ R : ℝ, 0 < R → ∀ (w : Data d) (i : Fin m), scenePair w R (φ i) =
      ∑ k, jointFddCoeff φ sp L R (Fin.castAdd p' i) k *
        (w.1 (Sandpile.siteEnum
          (Sandpile.Support.interpBox d R L (fun j => (sp j).1)) k) : ℝ) := by
    intro R hR w i
    simp only [jointFddCoeff_castAdd]
    exact scenePair_eq_sum_siteEnum (hvanish R hR i) w
  have hFrep : ∀ R : ℝ, 1 ≤ R → ∀ (w : Data d) (j : Fin p'),
      linHatInterp (fun y => (w.1 y : ℝ)) R (sp j) =
      ∑ k, jointFddCoeff φ sp L R (Fin.natAdd m j) k *
        (w.1 (Sandpile.siteEnum
          (Sandpile.Support.interpBox d R L (fun j => (sp j).1)) k) : ℝ) := by
    intro R hR w j
    simp only [jointFddCoeff_natAdd]
    rw [linHatInterpBridge d _ R hR (sp j) (hsp j)]
    exact Sandpile.Support.linInterp_eq_sum_interpBox R L (fun j => (sp j).1)
      (fun j => WithLp.toLp 2 (sp j).2) hw _ j
  have hcov : ∀ R : ℝ,
      ∀ α β : Fin (Sandpile.Support.interpBox d R L (fun j => (sp j).1)).card → ℝ,
      ∫ w, (∑ k, α k * (w.1 (Sandpile.siteEnum
          (Sandpile.Support.interpBox d R L (fun j => (sp j).1)) k) : ℝ)) *
        (∑ k, β k * (w.1 (Sandpile.siteEnum
          (Sandpile.Support.interpBox d R L (fun j => (sp j).1)) k) : ℝ)) ∂(law d ν)
      = v * ∑ k, α k * β k := fun R α β => by
    rw [integral_pick_mul_pick hd ν hν _ (Sandpile.siteEnum_injective _) α β, hv2,
      mul_comm _ v]
  -- the limits of the coefficient pairings
  have hSS' : ∀ i i' : Fin m, Tendsto (fun R : ℝ => ∑ k,
      jointFddCoeff φ sp L R (Fin.castAdd p' i) k * jointFddCoeff φ sp L R (Fin.castAdd p' i') k)
      atTop (𝓝 (∫ y : Sandpile.Continuum.Space d, φ i (WithLp.ofLp y) * φ i' (WithLp.ofLp y))) := by
    intro i i'
    have hlim := (hSS (φ i) (φ i') (hφ i) (hφ i')).const_mul v⁻¹
    have htarget : v⁻¹ * (v * ∫ x, φ i x * φ i' x) =
        ∫ y : Sandpile.Continuum.Space d, φ i (WithLp.ofLp y) * φ i' (WithLp.ofLp y) := by
      rw [← mul_assoc, inv_mul_cancel₀ hvpos.ne', one_mul]
      exact (integral_comp_ofLp d (fun x => φ i x * φ i' x)).symm
    rw [htarget] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    simp only [hSrep R hR]
    rw [hcov R, ← mul_assoc, inv_mul_cancel₀ hvpos.ne', one_mul]
  have hSF' : ∀ (i : Fin m) (j : Fin p'), Tendsto (fun R : ℝ => ∑ k,
      jointFddCoeff φ sp L R (Fin.castAdd p' i) k * jointFddCoeff φ sp L R (Fin.natAdd m j) k)
      atTop (𝓝 (∫ y : Sandpile.Continuum.Space d, φ i (WithLp.ofLp y) *
        Sandpile.Continuum.greenTimeBM d (sp j).1 (WithLp.toLp 2 (sp j).2) y)) := by
    intro i j
    have hlim0 : Tendsto (fun R : ℝ => ∫ w, scenePair w R (φ i) *
        linHatInterp (fun y => (w.1 y : ℝ)) R (sp j) ∂(law d ν)) atTop
        (𝓝 (v * ∫ y, φ i y * External.contFiniteGreen d (sp j).1 (sp j).2 y)) :=
      hSF (φ i) (hφ i) (sp j).1 (sp j).2 (hsp j)
    have hlim := hlim0.const_mul v⁻¹
    have htarget : v⁻¹ * (v * ∫ x, φ i x * External.contFiniteGreen d (sp j).1 (sp j).2 x) =
        ∫ y : Sandpile.Continuum.Space d, φ i (WithLp.ofLp y) *
          Sandpile.Continuum.greenTimeBM d (sp j).1 (WithLp.toLp 2 (sp j).2) y := by
      rw [← mul_assoc, inv_mul_cancel₀ hvpos.ne', one_mul,
        ← integral_comp_ofLp d (fun x => φ i x * External.contFiniteGreen d (sp j).1 (sp j).2 x)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [contFiniteGreen_eq_greenTimeBM d _ (hsp j), WithLp.toLp_ofLp]
    rw [htarget] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    simp only [hSrep R (by linarith), hFrep R hR]
    rw [hcov R, ← mul_assoc, inv_mul_cancel₀ hvpos.ne', one_mul]
  have hFF' : ∀ j j' : Fin p', Tendsto (fun R : ℝ => ∑ k,
      jointFddCoeff φ sp L R (Fin.natAdd m j) k * jointFddCoeff φ sp L R (Fin.natAdd m j') k)
      atTop (𝓝 (∫ y, Sandpile.Continuum.greenTimeBM d (sp j).1 (WithLp.toLp 2 (sp j).2) y *
        Sandpile.Continuum.greenTimeBM d (sp j').1 (WithLp.toLp 2 (sp j').2) y)) := by
    intro j j'
    rw [Sandpile.Support.integral_greenTimeBM_mul_two_interval hd hd3 (hsp j) (hsp j')]
    refine (Sandpile.Support.tendsto_interpDoubleTimeSum_of_continuum
      Sandpile.External.localCLT hd hd3 (Sandpile.Support.continuum_double_time_limit hd hd3)
      (hsp j) (hsp j') _ _).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    simp only [jointFddCoeff_natAdd]
    exact ((Sandpile.Support.sum_siteEnum_interpCoeff_mul d R _ _ _ _
      (fun ε => Sandpile.Support.interp_box_subset_max R L (fun j => (sp j).1)
        (fun j => WithLp.toLp 2 (sp j).2) hw j ε)).trans
      (Sandpile.Support.tsum_interpCoeff_mul d hR _ _ _ _)).symm
  have hswap : ∀ i i' : Fin (m + p'), Tendsto (fun R : ℝ => ∑ k,
      jointFddCoeff φ sp L R i k * jointFddCoeff φ sp L R i' k) atTop
      (𝓝 (∫ y, jointFddKernel φ sp i y * jointFddKernel φ sp i' y)) →
      Tendsto (fun R : ℝ => ∑ k, jointFddCoeff φ sp L R i' k * jointFddCoeff φ sp L R i k) atTop
      (𝓝 (∫ y, jointFddKernel φ sp i' y * jointFddKernel φ sp i y)) := by
    intro i i' h
    have e1 : (fun R : ℝ => ∑ k, jointFddCoeff φ sp L R i' k * jointFddCoeff φ sp L R i k) =
        fun R => ∑ k, jointFddCoeff φ sp L R i k * jointFddCoeff φ sp L R i' k :=
      funext fun R => Finset.sum_congr rfl fun k _ => mul_comm _ _
    have e2 : (∫ y, jointFddKernel φ sp i' y * jointFddKernel φ sp i y) =
        ∫ y, jointFddKernel φ sp i y * jointFddKernel φ sp i' y :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm _ _)
    rw [e1, e2]
    exact h
  have hpair : ∀ i i' : Fin (m + p'), Tendsto (fun R : ℝ => ∑ k,
      jointFddCoeff φ sp L R i k * jointFddCoeff φ sp L R i' k) atTop
      (𝓝 (∫ y, jointFddKernel φ sp i y * jointFddKernel φ sp i' y)) := by
    intro i i'
    induction i using Fin.addCases with
    | left i =>
      induction i' using Fin.addCases with
      | left i' => simpa only [jointFddKernel_castAdd] using hSS' i i'
      | right j' =>
        simpa only [jointFddKernel_castAdd, jointFddKernel_natAdd] using hSF' i j'
    | right j =>
      induction i' using Fin.addCases with
      | left i' =>
        exact hswap _ _
          (by simpa only [jointFddKernel_castAdd, jointFddKernel_natAdd] using hSF' i' j)
      | right j' => simpa only [jointFddKernel_natAdd] using hFF' j j'
  -- the limiting kernels are square integrable
  have hg : ∀ i, MemLp (jointFddKernel φ sp i) 2
      (volume : Measure (Sandpile.Continuum.Space d)) := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      rw [jointFddKernel_castAdd]
      exact memLp_test_comp_ofLp _ (hφ i)
    | right j =>
      rw [jointFddKernel_natAdd]
      exact Sandpile.Support.memLp_greenTimeBM hd hd3 (hsp j) _
  obtain ⟨Q, hQ⟩ : ∃ Q : (Fin (m + p') → ℝ) → ℝ, ∀ t, Q t =
      ∫ y, (∑ i, t i * jointFddKernel φ sp i y) * ∑ i, t i * jointFddKernel φ sp i y :=
    ⟨_, fun t => rfl⟩
  have hQlim : ∀ t : Fin (m + p') → ℝ, Tendsto (fun R : ℝ =>
      ∑ k, (∑ i, t i * jointFddCoeff φ sp L R i k) ^ 2) atTop (𝓝 (Q t)) := by
    intro t
    rw [hQ t, integral_sum_mul_sum_eq t _ fun i i' => (hg i).integrable_mul (hg i')]
    refine Tendsto.congr (fun R => (sum_sq_sum_eq t (jointFddCoeff φ sp L R)).symm) ?_
    exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun i' _ =>
      (hpair i i').const_mul _
  have hQvar : ∀ t : Fin (m + p') → ℝ, (∫ z, z ^ 2 ∂(ν.map (fun k : ℤ => (k : ℝ)))) * Q t =
      ∫ y, (∑ i, t i * (Real.sqrt v • jointFddKernel φ sp i) y) *
        ∑ i, t i * (Real.sqrt v • jointFddKernel φ sp i) y := by
    intro t
    have hc : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hvpos.le
    have hpt : ∀ y, (∑ i, t i * (Real.sqrt v • jointFddKernel φ sp i) y) *
        ∑ i, t i * (Real.sqrt v • jointFddKernel φ sp i) y =
        v * ((∑ i, t i * jointFddKernel φ sp i y) * ∑ i, t i * jointFddKernel φ sp i y) := by
      intro y
      have hs : ∑ i, t i * (Real.sqrt v • jointFddKernel φ sp i) y =
          Real.sqrt v * ∑ i, t i * jointFddKernel φ sp i y := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
      rw [hs]
      linear_combination ((∑ i, t i * jointFddKernel φ sp i y) *
        ∑ i, t i * jointFddKernel φ sp i y) * hc
    simp only [hpt]
    rw [integral_const_mul, hv2, hQ t]
  -- smallness of the coefficients
  have hdpos : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsmall : ∀ (t : Fin (m + p') → ℝ) (δ : ℝ), 0 < δ → ∀ᶠ R : ℝ in atTop,
      ∀ k, |∑ i, t i * jointFddCoeff φ sp L R i k| ≤ δ := by
    intro t δ hδ
    set K : ℝ := M * ∑ i : Fin m, |t (Fin.castAdd p' i)| with hK
    have hlim : Tendsto (fun R : ℝ => R ^ (-(d : ℝ) / 2) * K) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop hdpos).mul_const K
      rw [zero_mul] at h
      refine h.congr fun R => ?_
      rw [neg_div]
    have hS := hlim.eventually (eventually_le_nhds (half_pos hδ))
    have hF := Sandpile.Support.interp_hsmall hd hd3 (fun j => (sp j).1) hsp
      (fun j => WithLp.toLp 2 (sp j).2) L (fun j => t (Fin.natAdd m j)) (δ / 2) (half_pos hδ)
    filter_upwards [hS, hF, eventually_gt_atTop (0 : ℝ)] with R hSR hFR hR k
    have hρ0 : 0 ≤ R ^ (-(d : ℝ) / 2) := Real.rpow_nonneg hR.le _
    rw [Fin.sum_univ_add]
    simp only [jointFddCoeff_castAdd, jointFddCoeff_natAdd]
    have hA : |∑ i : Fin m, t (Fin.castAdd p' i) * (R ^ (-(d : ℝ) / 2) * φ i (fun l =>
        (Sandpile.siteEnum (Sandpile.Support.interpBox d R L (fun j => (sp j).1)) k l : ℝ) /
          R))| ≤ δ / 2 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i : Fin m, |t (Fin.castAdd p' i) * (R ^ (-(d : ℝ) / 2) * φ i (fun l =>
          (Sandpile.siteEnum (Sandpile.Support.interpBox d R L (fun j => (sp j).1)) k l :
            ℝ) / R))|
          ≤ ∑ i : Fin m, |t (Fin.castAdd p' i)| * (R ^ (-(d : ℝ) / 2) * M) :=
            Finset.sum_le_sum fun i _ => by
              rw [abs_mul, abs_mul, abs_of_nonneg hρ0]
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hM i _) hρ0)
                (abs_nonneg _)
        _ = (∑ i : Fin m, |t (Fin.castAdd p' i)|) * (R ^ (-(d : ℝ) / 2) * M) :=
            (Finset.sum_mul _ _ _).symm
        _ = R ^ (-(d : ℝ) / 2) * K := by
            rw [hK]
            ring
        _ ≤ δ / 2 := hSR
    calc |∑ i : Fin m, t (Fin.castAdd p' i) * (R ^ (-(d : ℝ) / 2) * φ i (fun l =>
          (Sandpile.siteEnum (Sandpile.Support.interpBox d R L (fun j => (sp j).1)) k l :
            ℝ) / R)) +
        ∑ j : Fin p', t (Fin.natAdd m j) * Sandpile.Support.interpCoeff d R (sp j).1
          (WithLp.toLp 2 (sp j).2)
            (Sandpile.siteEnum (Sandpile.Support.interpBox d R L (fun j => (sp j).1)) k)|
        ≤ |∑ i : Fin m, t (Fin.castAdd p' i) * (R ^ (-(d : ℝ) / 2) * φ i (fun l =>
          (Sandpile.siteEnum (Sandpile.Support.interpBox d R L (fun j => (sp j).1)) k l :
            ℝ) / R))| +
        |∑ j : Fin p', t (Fin.natAdd m j) * Sandpile.Support.interpCoeff d R (sp j).1
          (WithLp.toLp 2 (sp j).2)
            (Sandpile.siteEnum (Sandpile.Support.interpBox d R L (fun j => (sp j).1)) k)| :=
          abs_add_le _ _
      _ ≤ δ / 2 + δ / 2 := add_le_add hA (hFR k)
      _ = δ := add_halves δ
  -- the vector Lindeberg-Feller step under the sandpile mass law
  have hvec := Sandpile.Support.tendstoInDistribution_vector_pick_mass hd
    (ν.map (fun k : ℤ => (k : ℝ))) hsq hmean
    (fun (R : ℝ) (σ : Site d → ℝ) (i : Fin (m + p')) => ∑ k, jointFddCoeff φ sp L R i k *
      Sandpile.scenery d σ
        (Sandpile.siteEnum (Sandpile.Support.interpBox d R L (fun j => (sp j).1)) k))
    (fun R => (Sandpile.Support.interpBox d R L (fun j => (sp j).1)).card)
    (fun R => jointFddCoeff φ sp L R)
    (fun R => Sandpile.siteEnum (Sandpile.Support.interpBox d R L (fun j => (sp j).1)))
    (fun R => Sandpile.siteEnum_injective _) (fun R σ i => rfl) PW WD hW
    (fun i => Real.sqrt v • jointFddKernel φ sp i) (fun i => (hg i).const_smul _) Q hsmall
    hQlim hQvar
  have hlimae : (fun (ω : ΩW) (i : Fin (m + p')) =>
      WD ((fun i => Real.sqrt v • jointFddKernel φ sp i) i) ω) =ᵐ[PW]
      fun ω i => Real.sqrt v * WD (jointFddKernel φ sp i) ω := by
    have h := (ae_all_iff (ι := Fin (m + p'))
      (p := fun ω i => WD (Real.sqrt v • jointFddKernel φ sp i) ω =
        Real.sqrt v * WD (jointFddKernel φ sp i) ω)).mpr
      fun i => hW.smul (Real.sqrt v) (jointFddKernel φ sp i) (hg i)
    filter_upwards [h] with ω hω
    funext i
    exact hω i
  have h1 := hvec.congr (fun R => Filter.EventuallyEq.refl _ _) hlimae
  have hGc : Continuous (fun x : Fin (m + p') → ℝ =>
      ((fun i => x (Fin.castAdd p' i)), (fun j => x (Fin.natAdd m j)))) :=
    (continuous_pi fun i => continuous_apply _).prodMk (continuous_pi fun j => continuous_apply _)
  have h2 := h1.continuous_comp hGc
  have h3 := tendstoInDistribution_comp_of_map_eq measurable_massField
    (law_map_massField hd ν) h2
  have h4 := h3.congr (fun R => Filter.EventuallyEq.refl _ _)
    (T := fun ω =>
      ((fun i => Real.sqrt v * WD (fun y => φ i (WithLp.ofLp y)) ω),
        (fun j => Sandpile.Continuum.gaussianPotential d v WD (sp j).1
          (WithLp.toLp 2 (sp j).2) ω)))
    (Filter.Eventually.of_forall fun ω => by
      refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
      · simp only [Function.comp_apply, jointFddKernel_castAdd]
      · simp only [Function.comp_apply, jointFddKernel_natAdd]
        rfl)
  refine Sandpile.Support.tendstoInDistribution_congr_atTop (fun R =>
    ((Measurable.of_eval fun i => measurable_scenePair_any_R R).prodMk
      (Measurable.of_eval fun j => measurable_linHatInterp R (sp j))).aemeasurable) ?_ h4
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  funext w
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · simp only [Function.comp_apply, scenery_massField hd]
    exact hSrep R (by linarith) w i
  · simp only [Function.comp_apply, scenery_massField hd]
    exact hFrep R hR w j

end Parking.Support

end
