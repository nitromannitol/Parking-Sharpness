/-
The mean and second-moment integrability of the linear membrane field `V`, under an i.i.d.
law with mean zero and a finite second moment -- the two prerequisites of the grid-gap
estimate of `prop:spatial-scaling`'s Step 1 (`Parking.Support.LinGridGap`): (i) `E[V_n(x)] = 0`,
an instance of the generic centered finite-linear-combination identity
`Parking.integral_linear_sum_infinitePi` (`Parking/Support/LinearFirstMoment.lean`) at the
explicit finite-sum representation `Parking.linPotential_eq_sum`
(`Parking/Support/LinPotentialSum.lean`), since `Parking.iidLaw d ν0` unfolds to
`Measure.infinitePi (fun _ => ν0)`; (ii) the second-moment integrability of `V_n(x)` and of
the two-point, two-time difference `V_n(x) - V_m(y)`, from the SAME finite bilinear-form
machinery `Parking.integrable_sum_mul_sum_pi` (`Parking/Support/LinCovarianceGlue.lean`) that
gives the covariance value, here used to conclude integrability rather than to compute a
value.  Neither prerequisite can be read off the stated conclusion of
`Parking.exists_linPotential_increment_moment` (an `L^q`-moment bound whose integral is, by
the Mathlib junk-value convention, `0` and so satisfies `0 ≤ RHS` trivially when the
underlying quantity is not integrable), so both are proved directly here.
-/
import Parking.Support.LinCovarianceGlue
import Parking.Support.LinearFirstMoment
import Parking.Support.CriticalLawReal
import Parking.Support.LinIncrementConcentration

noncomputable section

namespace Parking

open MeasureTheory LatticeProb Finset

variable {d : ℕ}

/-! ### The mean of `V` -/

/-- **`V_n(x)` has mean zero**, for any i.i.d. law with mean zero and a finite first
moment: the explicit finite-sum representation of `V` (`Parking.linPotential_eq_sum`) is a
finite linear combination of the field's coordinates, and `Parking.iidLaw d ν0` unfolds to
`Measure.infinitePi (fun _ => ν0)`, so the generic centered-sum identity
`Parking.integral_linear_sum_infinitePi` applies directly. -/
theorem integral_linPotential_eq_zero (ν0 : Measure ℝ) [IsProbabilityMeasure ν0]
    (hmean : ∫ z, z ∂ν0 = 0) (hint : Integrable (fun x : ℝ => x) ν0)
    (n : ℕ) (x : Site d) :
    ∫ η, linPotential η n x ∂(iidLaw d ν0) = 0 := by
  have heq : (fun η : Site d → ℝ => linPotential η n x)
      = fun η => ∑ z ∈ boxFinset x n, green d n (x - z) * η z := by
    funext η
    rw [linPotential_eq_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [heq]
  exact integral_linear_sum_infinitePi ν0 hint hmean (boxFinset x n) (fun z => green d n (x - z))

/-- **`V_n(x)` is integrable**, for any i.i.d. law with a finite first moment: the same
finite-sum representation used by `integral_linPotential_eq_zero`, transported through
`Parking.integrable_linear_sum_infinitePi`'s own integrability conclusion. -/
theorem integrable_linPotential (ν0 : Measure ℝ) [IsProbabilityMeasure ν0]
    (hint : Integrable (fun x : ℝ => x) ν0) (n : ℕ) (x : Site d) :
    Integrable (fun η => linPotential η n x) (iidLaw d ν0) := by
  have heq : (fun η : Site d → ℝ => linPotential η n x)
      = fun η => ∑ z ∈ boxFinset x n, green d n (x - z) * η z := by
    funext η
    rw [linPotential_eq_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [heq]
  exact integrable_linear_sum_infinitePi ν0 hint (boxFinset x n) (fun z => green d n (x - z))

/-- **`V_n(x)` is integrable under the critical density.** -/
theorem integrable_linPotential_critical (ν : Measure ℤ) (hν : CriticalLaw ν)
    (n : ℕ) (x : Site d) :
    Integrable (fun η => linPotential η n x) (iidLaw d (realLaw ν)) := by
  haveI := hν.prob
  exact integrable_linPotential (realLaw ν) ((realLaw_memLp_two ν hν).integrable one_le_two) n x

/-- **`E[V_n(x)] = 0` under the critical density.** -/
theorem integral_linPotential_eq_zero_critical (ν : Measure ℤ) (hν : CriticalLaw ν)
    (n : ℕ) (x : Site d) :
    ∫ η, linPotential η n x ∂(iidLaw d (realLaw ν)) = 0 := by
  haveI := hν.prob
  exact integral_linPotential_eq_zero (realLaw ν) (realLaw_mean ν hν)
    ((realLaw_memLp_two ν hν).integrable one_le_two) n x

/-! ### Second-moment integrability of `V` -/

/-- **The product `V_n(x) · V_m(y)` is integrable**, for any i.i.d. law with a finite first
and second moment, over any common finite box `S`.  The same `hpt`/`integrable_sum_mul_sum_pi`
transport `Parking.integral_linPotential_mul` (`Parking/Support/LinCovarianceGlue.lean`) uses
for the covariance VALUE, here concluding integrability instead. -/
theorem integrable_linPotential_mul (ν0 : Measure ℝ) [IsProbabilityMeasure ν0]
    (hint : Integrable (fun x : ℝ => x) ν0) (hsq : Integrable (fun x : ℝ => x ^ 2) ν0)
    {n m : ℕ} {x y : Site d} {S : Finset (Site d)}
    (hSx : boxFinset x n ⊆ S) (hSy : boxFinset y m ⊆ S) :
    Integrable (fun η => linPotential η n x * linPotential η m y) (iidLaw d ν0) := by
  classical
  set a : Site d → ℝ := fun z => green d n (x - z) with hadef
  set b : Site d → ℝ := fun z => green d m (y - z) with hbdef
  set F : (S → ℝ) → ℝ := fun ζ => (∑ i : S, a (i : Site d) * ζ i) * (∑ j : S, b (j : Site d) * ζ j)
    with hFdef
  have hpt : ∀ η : Site d → ℝ,
      linPotential η n x * linPotential η m y = F (S.restrict η) := by
    intro η
    rw [linPotential_eq_sum_of_boxFinset_subset hSx η,
      linPotential_eq_sum_of_boxFinset_subset hSy η, hFdef]
    show (∑ z ∈ S, η z * a z) * (∑ z ∈ S, η z * b z)
      = (∑ i : S, a (i : Site d) * (S.restrict η) i) * (∑ j : S, b (j : Site d) * (S.restrict η) j)
    have hai : ∀ z : S, a (z : Site d) * (S.restrict η) z = η (z : Site d) * a (z : Site d) := by
      intro z; unfold Finset.restrict; ring
    have hbi : ∀ z : S, b (z : Site d) * (S.restrict η) z = η (z : Site d) * b (z : Site d) := by
      intro z; unfold Finset.restrict; ring
    rw [Finset.sum_congr rfl (fun i _ => hai i), Finset.sum_congr rfl (fun j _ => hbi j),
      Finset.sum_coe_sort S (fun z => η z * a z), Finset.sum_coe_sort S (fun z => η z * b z)]
  have hFint : Integrable F (Measure.pi fun _ : S => ν0) :=
    integrable_sum_mul_sum_pi (fun i : S => a (i : Site d)) (fun j : S => b (j : Site d))
      ν0 hint hsq
  have hmeasR : Measurable (S.restrict : (Site d → ℝ) → (S → ℝ)) :=
    measurable_pi_lambda _ fun k => measurable_pi_apply (k : Site d)
  have hFint' : Integrable F ((iidLaw d ν0).map S.restrict) := by
    rw [iidLaw_map_restrict d ν0 S]; exact hFint
  have hcomp : Integrable (F ∘ S.restrict) (iidLaw d ν0) :=
    (integrable_map_measure hFint'.aestronglyMeasurable hmeasR.aemeasurable).mp hFint'
  exact hcomp.congr (Filter.Eventually.of_forall fun η => (hpt η).symm)

/-- **`V_n(x)²` is integrable.** -/
theorem integrable_linPotential_sq (ν0 : Measure ℝ) [IsProbabilityMeasure ν0]
    (hint : Integrable (fun x : ℝ => x) ν0) (hsq : Integrable (fun x : ℝ => x ^ 2) ν0)
    (n : ℕ) (x : Site d) :
    Integrable (fun η => (linPotential η n x) ^ 2) (iidLaw d ν0) := by
  have h := integrable_linPotential_mul ν0 hint hsq
    (S := boxFinset x n) (n := n) (m := n) (x := x) (y := x)
    (Finset.Subset.refl _) (Finset.Subset.refl _)
  simpa [sq] using h

/-- **The two-point, two-time difference `V_n(x) - V_m(y)` has an integrable square.** -/
theorem integrable_linPotential_diff_sq (ν0 : Measure ℝ) [IsProbabilityMeasure ν0]
    (hint : Integrable (fun x : ℝ => x) ν0) (hsq : Integrable (fun x : ℝ => x ^ 2) ν0)
    (n m : ℕ) (x y : Site d) :
    Integrable (fun η => (linPotential η n x - linPotential η m y) ^ 2) (iidLaw d ν0) := by
  have h1 := integrable_linPotential_sq ν0 hint hsq n x
  have h2 := integrable_linPotential_sq ν0 hint hsq m y
  have h3 : Integrable (fun η => linPotential η n x * linPotential η m y) (iidLaw d ν0) :=
    integrable_linPotential_mul ν0 hint hsq
      (S := linIncrementBox n m x y)
      (boxFinset_x_subset_linIncrementBox n m x y) (boxFinset_y_subset_linIncrementBox n m x y)
  have heq : (fun η => (linPotential η n x - linPotential η m y) ^ 2)
      = fun η => (linPotential η n x) ^ 2 - 2 * (linPotential η n x * linPotential η m y)
          + (linPotential η m y) ^ 2 := by
    funext η; ring
  rw [heq]
  exact (h1.sub (h3.const_mul 2)).add h2

/-- **`V_n(x)²` is integrable under the critical density.** -/
theorem integrable_linPotential_sq_critical (ν : Measure ℤ) (hν : CriticalLaw ν)
    (n : ℕ) (x : Site d) :
    Integrable (fun η => (linPotential η n x) ^ 2) (iidLaw d (realLaw ν)) := by
  haveI := hν.prob
  exact integrable_linPotential_sq (realLaw ν) ((realLaw_memLp_two ν hν).integrable one_le_two)
    (realLaw_memLp_two ν hν).integrable_sq n x

/-- **The two-point, two-time difference of `V` has an integrable square under the critical
density.** -/
theorem integrable_linPotential_diff_sq_critical (ν : Measure ℤ) (hν : CriticalLaw ν)
    (n m : ℕ) (x y : Site d) :
    Integrable (fun η => (linPotential η n x - linPotential η m y) ^ 2)
      (iidLaw d (realLaw ν)) := by
  haveI := hν.prob
  exact integrable_linPotential_diff_sq (realLaw ν)
    ((realLaw_memLp_two ν hν).integrable one_le_two) (realLaw_memLp_two ν hν).integrable_sq n m x y

end Parking

end
