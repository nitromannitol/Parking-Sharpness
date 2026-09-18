/-
The orthant form of Raic, Theorem 1.1, used at sandpile.tex:1770-1782.
This is the explicit MultivariateBerryEsseen hypothesis of the sealed sibling
critical_toppling, used at parking.tex:1807-1833. Assumed here.
-/
import Parking.Support.NearestCriticalModel

open MeasureTheory ProbabilityTheory

-- FROZEN-STATEMENT-BEGIN
/-- The multivariate Berry--Esseen comparison of `sandpile.tex:1770-1782`, in
the standardized form the proof of `thm:critical-toppling` applies: for an
i.i.d. mean-zero one-site law whose third absolute moment is at most `M` times
the `3/2` power of its variance, and coefficients `a` whose covariance matrix
`Σ` has quadratic form between `1-δ` and `1+δ`, the law of the linear forms
`Y_j = ∑_i a_i(j) ξ_i` and the centred Gaussian with covariance `Σ` assign
probabilities to the orthant `{y_j ≤ h_j}` differing by at most
`C m^{1/4} \Var(ν)^{3/2} ∑_i |a(i)|³`.  Assumed, not proved. -/
def Parking.External.MultivariateBerryEsseen : Prop :=
  ∀ M δ : ℝ, 0 < M → 0 < δ → δ < 1 →
    ∃ C : ℝ, 0 < C ∧
      ∀ (N m : ℕ), 1 ≤ m →
        ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
          ∫ z, z ∂ν = 0 → 0 < variance id ν →
          Integrable (fun z => |z| ^ 3) ν →
          ∫ z, |z| ^ 3 ∂ν ≤ M * variance id ν ^ ((3 : ℝ) / 2) →
          ∀ a : Fin N → Fin m → ℝ,
            (∀ v : Fin m → ℝ,
              (1 - δ) * ∑ j, v j ^ 2 ≤
                  Parking.CriticalScale.quadForm
                    (Parking.CriticalScale.gram ν a) v ∧
                Parking.CriticalScale.quadForm
                    (Parking.CriticalScale.gram ν a) v ≤
                  (1 + δ) * ∑ j, v j ^ 2) →
            ∀ h : Fin m → ℝ,
              |((Measure.pi fun _ : Fin N => ν)
                      {ξ | ∀ j, ∑ i, a i j * ξ i ≤ h j}).toReal -
                  (multivariateGaussian 0
                      (Parking.CriticalScale.gram ν a)
                      {y | ∀ j, y j ≤ h j}).toReal| ≤
                C * (m : ℝ) ^ ((1 : ℝ) / 4) * variance id ν ^ ((3 : ℝ) / 2) *
                  ∑ i, Parking.CriticalScale.coeffNorm a i ^ 3
-- FROZEN-STATEMENT-END
