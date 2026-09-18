/-
The finite-dimensional characteristic-function limit of the rescaled box reward field at
finitely many box points (`parking.tex:3192-3203`, Stage 2 of the covariance-to-Gaussian
step).

Combines the linear decomposition of `Parking.orientedBoxReward` (`TightLinear.lean`), the
covariance limit of the interpolated field (`TightBoxCov.lean`), and the scalar
triangular-array characteristic-function central limit theorem (`TightCLT.lean`) into the
single scalar statement: for any finite weighted combination of finitely many box points, the
characteristic function of the combination converges to the Gaussian one with variance the
corresponding quadratic form of `Parking.contOverlap`.
-/
import Parking.Support.TightLinear
import Parking.Support.TightBoxCov

open MeasureTheory LatticeProb Filter Topology Finset

noncomputable section
namespace Parking

/-- **The second moment of a finite linear combination of the i.i.d. scenery is the variance
times the sum of the coefficient products.** -/
theorem integral_sum_mul_sum (ν : Measure ℤ) (hν : CriticalLaw ν) (S : Finset (Site 2))
    (a b : Site 2 → ℝ) :
    ∫ η : Site 2 → ℝ, (∑ z ∈ S, a z * η z) * (∑ z ∈ S, b z * η z) ∂(iidLaw 2 (realLaw ν))
      = (∫ x : ℝ, x ^ 2 ∂(realLaw ν)) * ∑ z ∈ S, a z * b z := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  have hterm : ∀ z z' : Site 2, Integrable
      (fun η : Site 2 → ℝ => (a z * η z) * (b z' * η z')) (iidLaw 2 (realLaw ν)) := by
    intro z z'
    have hbase := (integrable_eval_mul_eval_iid ν hν z z').abs.const_mul |a z * b z'|
    refine hbase.mono' (((measurable_const.mul (measurable_pi_apply z)).mul
      (measurable_const.mul (measurable_pi_apply z'))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun η => ?_)
    rw [Real.norm_eq_abs]
    show |(a z * η z) * (b z' * η z')| ≤ |a z * b z'| * |η z * η z'|
    rw [show (a z * η z) * (b z' * η z') = (a z * b z') * (η z * η z') by ring, abs_mul]
  have hfun : (fun η : Site 2 → ℝ => (∑ z ∈ S, a z * η z) * (∑ z ∈ S, b z * η z))
      = fun η => ∑ z ∈ S, ∑ z' ∈ S, (a z * η z) * (b z' * η z') := by
    funext η
    rw [Finset.sum_mul_sum]
  rw [hfun, integral_finsetSum _ fun z _ => integrable_finsetSum _ fun z' _ => hterm z z']
  rw [sum_congr rfl fun z _ => integral_finsetSum _ fun z' _ => hterm z z']
  have hval : ∀ z z' : Site 2,
      ∫ η : Site 2 → ℝ, (a z * η z) * (b z' * η z') ∂(iidLaw 2 (realLaw ν))
        = (a z * b z') * if z = z' then ∫ x : ℝ, x ^ 2 ∂(realLaw ν) else 0 := by
    intro z z'
    have hpt : (fun η : Site 2 → ℝ => (a z * η z) * (b z' * η z'))
        = fun η : Site 2 → ℝ => (a z * b z') * (η z * η z') := by ext η; ring
    rw [hpt, integral_const_mul, integral_eval_mul_eval_iid ν hν z z']
  rw [sum_congr rfl fun z _ => sum_congr rfl fun z' _ => hval z z']
  have hdiag : ∀ z ∈ S, (∑ z' ∈ S, (a z * b z') * if z = z' then ∫ x : ℝ, x ^ 2 ∂(realLaw ν) else 0)
      = a z * b z * ∫ x : ℝ, x ^ 2 ∂(realLaw ν) := by
    intro z hz
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq S z]
    simp [hz]
  rw [sum_congr rfl hdiag, Finset.mul_sum]
  exact sum_congr rfl fun z _ => by ring

/-- **The coefficient of `Parking.orientedBoxRewardCoeff` is uniformly bounded**, independent
of the box point and the site: each of the (at most four) corners contributes a hat weight at
most `1` times a Green-function coefficient at most `n^{-1/4}` in absolute value. -/
theorem abs_orientedBoxRewardCoeff_le (T : ℝ) (n : ℕ) (u : Fin 2 → ℝ) (z : Site 2) :
    |orientedBoxRewardCoeff T n u z| ≤ 4 * (n : ℝ) ^ (-(1 : ℝ) / 4) := by
  have hcard : (orientedBoxRewardCorners n u).card = 4 := by
    unfold orientedBoxRewardCorners
    rw [Finset.card_product, Finset.card_pair (by omega), Finset.card_pair (by omega)]
  have hterm : ∀ c ∈ orientedBoxRewardCorners n u,
      |(hat1 ((n : ℝ) * u 0 - (c.1 : ℝ)) *
          hat1 (Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2 - (c.2 : ℝ))) *
        orientedGridRewardCoeff n ⌊(n : ℝ) * T⌋₊ c z| ≤ (n : ℝ) ^ (-(1 : ℝ) / 4) := by
    intro c _
    have hh1 : |hat1 ((n : ℝ) * u 0 - (c.1 : ℝ))| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hat1_nonneg ((n : ℝ) * u 0 - (c.1 : ℝ))],
        hat1_le_one _⟩
    have hh2 : |hat1 (Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2 - (c.2 : ℝ))| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hat1_nonneg (Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2 - (c.2 : ℝ))],
        hat1_le_one _⟩
    have hgc : |orientedGridRewardCoeff n ⌊(n : ℝ) * T⌋₊ c z| ≤ (n : ℝ) ^ (-(1 : ℝ) / 4) := by
      unfold orientedGridRewardCoeff
      rw [abs_mul, abs_neg, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
      calc (n : ℝ) ^ (-(1 : ℝ) / 4) *
            |orientedGreen 2 (⌊(n : ℝ) * T⌋₊ - c.1.toNat) (z - orientedLayerPoint c.1.toNat c.2)|
          = (n : ℝ) ^ (-(1 : ℝ) / 4) *
              orientedGreen 2 (⌊(n : ℝ) * T⌋₊ - c.1.toNat) (z - orientedLayerPoint c.1.toNat c.2) := by
            rw [abs_of_nonneg (orientedGreen_nonneg _ _)]
        _ ≤ (n : ℝ) ^ (-(1 : ℝ) / 4) * 1 :=
            mul_le_mul_of_nonneg_left (orientedGreen_le_one (by norm_num) _ _)
              (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        _ = (n : ℝ) ^ (-(1 : ℝ) / 4) := mul_one _
    calc |(hat1 ((n : ℝ) * u 0 - (c.1 : ℝ)) *
            hat1 (Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2 - (c.2 : ℝ))) *
          orientedGridRewardCoeff n ⌊(n : ℝ) * T⌋₊ c z|
        = |hat1 ((n : ℝ) * u 0 - (c.1 : ℝ))| *
            |hat1 (Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2 - (c.2 : ℝ))| *
            |orientedGridRewardCoeff n ⌊(n : ℝ) * T⌋₊ c z| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * 1 * (n : ℝ) ^ (-(1 : ℝ) / 4) :=
          mul_le_mul (mul_le_mul hh1 hh2 (abs_nonneg _) zero_le_one) hgc (abs_nonneg _)
            (by norm_num)
      _ = (n : ℝ) ^ (-(1 : ℝ) / 4) := by ring
  unfold orientedBoxRewardCoeff
  calc |∑ c ∈ orientedBoxRewardCorners n u,
        (hat1 ((n : ℝ) * u 0 - (c.1 : ℝ)) *
            hat1 (Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2 - (c.2 : ℝ))) *
          orientedGridRewardCoeff n ⌊(n : ℝ) * T⌋₊ c z|
      ≤ ∑ c ∈ orientedBoxRewardCorners n u,
          |(hat1 ((n : ℝ) * u 0 - (c.1 : ℝ)) *
              hat1 (Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2 - (c.2 : ℝ))) *
            orientedGridRewardCoeff n ⌊(n : ℝ) * T⌋₊ c z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ orientedBoxRewardCorners n u, (n : ℝ) ^ (-(1 : ℝ) / 4) :=
        Finset.sum_le_sum hterm
    _ = (orientedBoxRewardCorners n u).card * (n : ℝ) ^ (-(1 : ℝ) / 4) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = 4 * (n : ℝ) ^ (-(1 : ℝ) / 4) := by rw [hcard]; norm_num

/-- **The linear decomposition of the box reward, extended to any superset of its own
support.** -/
theorem orientedBoxReward_eq_sum_of_subset (T : ℝ) (n : ℕ) (η : Site 2 → ℝ) (u : Fin 2 → ℝ)
    {S : Finset (Site 2)} (hS : orientedBoxRewardSupport T n u ⊆ S) :
    orientedBoxReward T n η u = ∑ z ∈ S, orientedBoxRewardCoeff T n u z * η z := by
  rw [orientedBoxReward_eq_sum]
  refine Finset.sum_subset hS fun z _ hz => ?_
  rw [orientedBoxRewardCoeff_eq_zero_of_notMem hz, zero_mul]

/-- **The covariance of the coefficients of two box points converges to the overlap kernel**:
the algebraic content of `Parking.tendsto_integral_orientedBoxReward_mul`, read off through
the linear decomposition rather than through the field's own covariance. -/
theorem tendsto_sum_orientedBoxRewardCoeff_mul (ν : Measure ℤ) (hν : CriticalLaw ν)
    (hBinomial : External.BinomialLocalCLT) (T : ℝ) (u u' : Fin 2 → ℝ)
    (hu0 : 0 ≤ u 0) (huT : u 0 ≤ T) (hu'0 : 0 ≤ u' 0) (hu'T : u' 0 ≤ T)
    {S : ℕ → Finset (Site 2)}
    (hSu : ∀ n, orientedBoxRewardSupport T n u ⊆ S n)
    (hSu' : ∀ n, orientedBoxRewardSupport T n u' ⊆ S n) :
    Tendsto (fun n => ∑ z ∈ S n, orientedBoxRewardCoeff T n u z * orientedBoxRewardCoeff T n u' z)
      atTop (𝓝 (contOverlap T u u')) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  have hσ2 : 0 < ∫ x : ℝ, x ^ 2 ∂(realLaw ν) := realLaw_sq_integral_pos ν hν
  have heq : ∀ n : ℕ, (∫ x : ℝ, x ^ 2 ∂(realLaw ν)) *
      ∑ z ∈ S n, orientedBoxRewardCoeff T n u z * orientedBoxRewardCoeff T n u' z =
      ∫ η : Site 2 → ℝ, orientedBoxReward T n η u * orientedBoxReward T n η u'
        ∂(iidLaw 2 (realLaw ν)) := by
    intro n
    rw [← integral_sum_mul_sum ν hν (S n) (orientedBoxRewardCoeff T n u)
      (orientedBoxRewardCoeff T n u')]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    show (∑ z ∈ S n, orientedBoxRewardCoeff T n u z * η z) *
        ∑ z ∈ S n, orientedBoxRewardCoeff T n u' z * η z =
      orientedBoxReward T n η u * orientedBoxReward T n η u'
    rw [orientedBoxReward_eq_sum_of_subset T n η u (hSu n),
      orientedBoxReward_eq_sum_of_subset T n η u' (hSu' n)]
  have hmain : Tendsto (fun n => (∫ x : ℝ, x ^ 2 ∂(realLaw ν)) *
      ∑ z ∈ S n, orientedBoxRewardCoeff T n u z * orientedBoxRewardCoeff T n u' z) atTop
      (𝓝 ((∫ x : ℝ, x ^ 2 ∂(realLaw ν)) * contOverlap T u u')) := by
    refine Tendsto.congr' (Filter.Eventually.of_forall fun n => (heq n).symm) ?_
    exact tendsto_integral_orientedBoxReward_mul ν hν hBinomial T u u' hu0 huT hu'0 hu'T
  have := hmain.const_mul (∫ x : ℝ, x ^ 2 ∂(realLaw ν))⁻¹
  simp only [← mul_assoc, inv_mul_cancel₀ hσ2.ne', one_mul] at this
  exact this

/-- **The `V(t)` limit**: the sum of squares of the combined linear coefficients converges to
the quadratic form of `Parking.contOverlap` at the weights, for any finite weighted vector of
box points. -/
theorem tendsto_sum_orientedBoxRewardCoeff_sq (ν : Measure ℤ) (hν : CriticalLaw ν)
    (hBinomial : External.BinomialLocalCLT) (T : ℝ) {k : ℕ} (u : Fin k → Fin 2 → ℝ)
    (hu0 : ∀ l, 0 ≤ u l 0) (huT : ∀ l, u l 0 ≤ T) (t : Fin k → ℝ) :
    Tendsto (fun n => ∑ z ∈ Finset.univ.biUnion fun l => orientedBoxRewardSupport T n (u l),
        (∑ l, t l * orientedBoxRewardCoeff T n (u l) z) ^ 2) atTop
      (𝓝 (∑ l, ∑ l', t l * t l' * contOverlap T (u l) (u l'))) := by
  set S : ℕ → Finset (Site 2) := fun n => Finset.univ.biUnion fun l =>
    orientedBoxRewardSupport T n (u l) with hSdef
  have hSsub : ∀ l : Fin k, ∀ n, orientedBoxRewardSupport T n (u l) ⊆ S n := fun l n =>
    Finset.subset_biUnion_of_mem (fun l => orientedBoxRewardSupport T n (u l))
      (Finset.mem_univ l)
  have hpair : ∀ l l' : Fin k, Tendsto (fun n => ∑ z ∈ S n,
      orientedBoxRewardCoeff T n (u l) z * orientedBoxRewardCoeff T n (u l') z) atTop
      (𝓝 (contOverlap T (u l) (u l'))) := fun l l' =>
    tendsto_sum_orientedBoxRewardCoeff_mul ν hν hBinomial T (u l) (u l') (hu0 l) (huT l)
      (hu0 l') (huT l') (hSsub l) (hSsub l')
  have halg : ∀ n : ℕ, ∑ z ∈ S n, (∑ l, t l * orientedBoxRewardCoeff T n (u l) z) ^ 2 =
      ∑ l : Fin k, ∑ l' : Fin k, t l * t l' *
        ∑ z ∈ S n, orientedBoxRewardCoeff T n (u l) z * orientedBoxRewardCoeff T n (u l') z := by
    intro n
    calc ∑ z ∈ S n, (∑ l, t l * orientedBoxRewardCoeff T n (u l) z) ^ 2
        = ∑ z ∈ S n, ∑ l : Fin k, ∑ l' : Fin k,
            (t l * orientedBoxRewardCoeff T n (u l) z) *
              (t l' * orientedBoxRewardCoeff T n (u l') z) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [sq, Finset.sum_mul_sum]
      _ = ∑ l : Fin k, ∑ l' : Fin k, ∑ z ∈ S n,
            (t l * orientedBoxRewardCoeff T n (u l) z) *
              (t l' * orientedBoxRewardCoeff T n (u l') z) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun l _ => Finset.sum_comm
      _ = ∑ l : Fin k, ∑ l' : Fin k, t l * t l' *
            ∑ z ∈ S n,
              orientedBoxRewardCoeff T n (u l) z * orientedBoxRewardCoeff T n (u l') z := by
          refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun z _ => by ring
  refine Tendsto.congr' (Filter.Eventually.of_forall fun n => (halg n).symm) ?_
  refine tendsto_finsetSum Finset.univ fun l _ => ?_
  exact tendsto_finsetSum Finset.univ fun l' _ => (hpair l l').const_mul (t l * t l')

/-- **The finite-dimensional characteristic-function limit.** The characteristic function, at
argument `1`, of any fixed weighted combination of `Parking.orientedBoxReward` at finitely many
box points converges to the Gaussian one, with variance the corresponding quadratic form of
`Parking.contOverlap`. This is the scalar content of Stage 2: reading the vector `t`-frequency
characteristic function of the box points as the scalar characteristic function of the linear
combination `∑ t_l · (box reward at u_l)` (via the inner product `⟪·,t⟫`) reduces
finite-dimensional convergence in law to exactly this statement. -/
theorem tendsto_charFun_orientedBoxReward_linearCombination (ν : Measure ℤ) (hν : CriticalLaw ν)
    (hBinomial : External.BinomialLocalCLT) (T : ℝ) {k : ℕ} (u : Fin k → Fin 2 → ℝ)
    (hu0 : ∀ l, 0 ≤ u l 0) (huT : ∀ l, u l 0 ≤ T) (t : Fin k → ℝ) :
    Tendsto (fun n : ℕ => charFun ((iidLaw 2 (realLaw ν)).map
        (fun η : Site 2 → ℝ => ∑ l, t l * orientedBoxReward T n η (u l))) (1 : ℝ)) atTop
      (𝓝 (Complex.exp (-((∫ x : ℝ, x ^ 2 ∂(realLaw ν) : ℝ) : ℂ) *
            ((∑ l, ∑ l', t l * t l' * contOverlap T (u l) (u l') : ℝ) : ℂ) / 2))) := by
  set S : ℕ → Finset (Site 2) := fun n => Finset.univ.biUnion fun l =>
    orientedBoxRewardSupport T n (u l) with hSdef
  set d : ℕ → Site 2 → ℝ := fun n z => ∑ l, t l * orientedBoxRewardCoeff T n (u l) z with hddef
  have hV := tendsto_sum_orientedBoxRewardCoeff_sq ν hν hBinomial T u hu0 huT t
  set M : ℕ → ℝ := fun n => 4 * (∑ l, |t l|) * (n : ℝ) ^ (-(1 : ℝ) / 4) with hMdef
  have hM : Tendsto M atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 4)) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop (y := (1 : ℝ) / 4) (by norm_num)).comp
        tendsto_natCast_atTop_atTop
      simp only [Function.comp_def, ← neg_div] at h
      exact h
    have := h0.const_mul (4 * ∑ l, |t l|)
    simpa [hMdef, mul_assoc] using this
  have hMd : ∀ n, ∀ w ∈ S n, |d n w| ≤ M n := by
    intro n w _
    calc |d n w| = |∑ l, t l * orientedBoxRewardCoeff T n (u l) w| := rfl
      _ ≤ ∑ l, |t l * orientedBoxRewardCoeff T n (u l) w| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l, |t l| * (4 * (n : ℝ) ^ (-(1 : ℝ) / 4)) := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_orientedBoxRewardCoeff_le T n (u l) w)
            (abs_nonneg _)
      _ = M n := by rw [← Finset.sum_mul, hMdef]; ring
  have hlaw := tendsto_charFun_weighted_scenery_sum_two ν hν S d (1 : ℝ) hV M hM hMd
  simp only [Complex.ofReal_one, one_pow, mul_one] at hlaw
  refine hlaw.congr' (Filter.Eventually.of_forall fun n => ?_)
  have hfun : (fun η : Site 2 → ℝ => ∑ z ∈ S n, d n z * η z) =
      fun η => ∑ l, t l * orientedBoxReward T n η (u l) :=
    funext fun η => (orientedBoxReward_vec_eq_sum T n η u t).symm
  rw [hfun]

end Parking
end
