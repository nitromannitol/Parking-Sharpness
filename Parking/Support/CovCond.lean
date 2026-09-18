/-
The conditional covariance identity of `lem:product` (`parking.tex:2354-2357`):
"The conditional covariance identity splits `Cov(F,Z)` into `Cov(f(Y), z(Y))` and
`E[Cov(F,Z | Y)]`."

In the paper's setting the conditioning variable is the signed count at a site
and the remaining randomness is the walks and uniform variables attached to its
particles, so the underlying space is a PRODUCT and the identity is Fubini and
nothing else: writing `f(a) = ∫ F(a, ·) dρ` and `z(a) = ∫ Z(a, ·) dρ`, the mean of
the product splits as

    ∫ F Z d(μ ⊗ ρ) = ∫ [Cov_ρ(F(a,·), Z(a,·)) + f(a) z(a)] dμ(a),

and subtracting the product of the two means, which are `∫ f dμ` and `∫ z dμ`,
leaves the two terms of the statement.
-/
import Parking.Support.Cov

noncomputable section

open MeasureTheory

namespace Parking

/-- **The conditional covariance identity on a product.**  The covariance under
`μ ⊗ ρ` is the covariance of the two conditional means under `μ` plus the mean
under `μ` of the conditional covariance under `ρ`. -/
theorem cov_prod_decomp {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ρ : Measure β) [IsProbabilityMeasure ρ]
    (F Z : α × β → ℝ)
    (hFZ : Integrable (fun q : α × β => F q * Z q) (μ.prod ρ))
    (hF : Integrable F (μ.prod ρ)) (hZ : Integrable Z (μ.prod ρ))
    (hfz : Integrable (fun a => (∫ b, F (a, b) ∂ρ) * ∫ b, Z (a, b) ∂ρ) μ) :
    cov (μ.prod ρ) F Z
      = cov μ (fun a => ∫ b, F (a, b) ∂ρ) (fun a => ∫ b, Z (a, b) ∂ρ)
        + ∫ a, cov ρ (fun b => F (a, b)) (fun b => Z (a, b)) ∂μ := by
  have hIcond : Integrable (fun a => ∫ b, F (a, b) * Z (a, b) ∂ρ) μ :=
    hFZ.integral_prod_left
  have hcond : ∀ a : α, cov ρ (fun b => F (a, b)) (fun b => Z (a, b))
      = (∫ b, F (a, b) * Z (a, b) ∂ρ) - (∫ b, F (a, b) ∂ρ) * ∫ b, Z (a, b) ∂ρ := fun a => rfl
  have hsplit : ∫ a, cov ρ (fun b => F (a, b)) (fun b => Z (a, b)) ∂μ
      = (∫ a, ∫ b, F (a, b) * Z (a, b) ∂ρ ∂μ)
        - ∫ a, (∫ b, F (a, b) ∂ρ) * (∫ b, Z (a, b) ∂ρ) ∂μ := by
    simp only [hcond]
    exact integral_sub hIcond hfz
  have hprod : ∫ q, F q * Z q ∂(μ.prod ρ) = ∫ a, ∫ b, F (a, b) * Z (a, b) ∂ρ ∂μ :=
    integral_prod _ hFZ
  have hFm : ∫ q, F q ∂(μ.prod ρ) = ∫ a, ∫ b, F (a, b) ∂ρ ∂μ := integral_prod _ hF
  have hZm : ∫ q, Z q ∂(μ.prod ρ) = ∫ a, ∫ b, Z (a, b) ∂ρ ∂μ := integral_prod _ hZ
  rw [cov, cov, hsplit, hprod, hFm, hZm]
  ring

/-- **The triangle inequality on the identity.**  What Step 2 of `lem:product`
uses: the covariance is at most the covariance of the conditional means plus the
MEAN OF THE ABSOLUTE conditional covariances, which is the quantity the paper
bounds by `2 Cov(f(Y), Y)`. -/
theorem abs_cov_prod_le {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ρ : Measure β) [IsProbabilityMeasure ρ]
    (F Z : α × β → ℝ)
    (hFZ : Integrable (fun q : α × β => F q * Z q) (μ.prod ρ))
    (hF : Integrable F (μ.prod ρ)) (hZ : Integrable Z (μ.prod ρ))
    (hfz : Integrable (fun a => (∫ b, F (a, b) ∂ρ) * ∫ b, Z (a, b) ∂ρ) μ) :
    |cov (μ.prod ρ) F Z|
      ≤ |cov μ (fun a => ∫ b, F (a, b) ∂ρ) (fun a => ∫ b, Z (a, b) ∂ρ)|
        + ∫ a, |cov ρ (fun b => F (a, b)) (fun b => Z (a, b))| ∂μ := by
  rw [cov_prod_decomp μ ρ F Z hFZ hF hZ hfz]
  refine le_trans (abs_add_le _ _) ?_
  gcongr
  exact abs_integral_le_integral_abs

end Parking

end
