/-
The mean number of unfilled holes at a site, which is what Step 1 of
`thm:subcritical` needs (`parking.tex:2453-2458`):

  "Under `E_λ`, `eq:activity-holes` gives `E_λ H_t(0) ≥ δ(λ)`, so by translation
   invariance the expected number of unfilled holes in `R_t` at time `t` is at
   least `δ(λ)|R_t|`."

Both halves are here: the mean is the same at every site, because the law of the
configuration is translation invariant and the process is equivariant; and at the
origin it is at least `-E η(0)`, because `lem:activity-holes` writes it as the
mean activity minus the mean of the configuration and the activity is
nonnegative.
-/
import Parking.Support.ActivityHoles

open MeasureTheory

noncomputable section

namespace Parking

variable {d : ℕ} {μ : Measure (Site d → ℤ)}

/-- The expected number of unfilled holes at a site does not depend on the
site. -/
theorem integral_H_site_eq (hd : 1 ≤ d) [IsProbabilityMeasure μ]
    (hti : TranslationInvariant μ) (t : ℕ) (x : Site d) :
    ∫ ω, (Parking.H ω t x : ℝ) ∂(dataLaw d μ)
      = ∫ ω, (Parking.H ω t 0 : ℝ) ∂(dataLaw d μ) := by
  have hF : AEStronglyMeasurable (fun ω : Data d => (Parking.H ω t 0 : ℝ)) (dataLaw d μ) :=
    ((measurable_from_countable' fun n : ℕ => (n : ℝ)).comp
      (measurable_H t (0 : Site d))).aestronglyMeasurable
  have h := integral_comp_shiftData hd hti x hF
  have hrw : ∀ ω : Data d, (Parking.H (shiftData x ω) t 0 : ℝ) = (Parking.H ω t x : ℝ) := by
    intro ω
    rw [H_shiftData, zero_add]
  simp only [hrw] at h
  exact h

/-- **`E H_t(0) ≥ δ`**, the first half of Step 1 of `thm:subcritical`: the mean
number of unfilled holes at the origin is at least minus the mean of the
configuration, because the mean activity is nonnegative. -/
theorem neg_integral_eta_le_integral_H (hd : 1 ≤ d) [IsProbabilityMeasure μ]
    (hti : TranslationInvariant μ)
    (hint : Integrable (fun η : Site d → ℤ => |((η 0 : ℤ) : ℝ)|) μ) (t : ℕ) :
    -∫ η, ((η 0 : ℤ) : ℝ) ∂μ ≤ ∫ ω, (Parking.H ω t 0 : ℝ) ∂(dataLaw d μ) := by
  have hid := activity_holes_main hd hti hint t
  have hA : 0 ≤ ∫ ω, (Parking.A ω t 0 : ℝ) ∂(dataLaw d μ) :=
    integral_nonneg fun ω => by positivity
  linarith

/-- The same bound at every site. -/
theorem neg_integral_eta_le_integral_H_site (hd : 1 ≤ d) [IsProbabilityMeasure μ]
    (hti : TranslationInvariant μ)
    (hint : Integrable (fun η : Site d → ℤ => |((η 0 : ℤ) : ℝ)|) μ) (t : ℕ) (x : Site d) :
    -∫ η, ((η 0 : ℤ) : ℝ) ∂μ ≤ ∫ ω, (Parking.H ω t x : ℝ) ∂(dataLaw d μ) := by
  rw [integral_H_site_eq hd hti t x]
  exact neg_integral_eta_le_integral_H hd hti hint t

end Parking

end
