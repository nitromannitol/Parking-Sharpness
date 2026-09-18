/- The cumulative routing discrepancy of one instruction.

In the regrouping of the directed error field of `parking.tex:3240-3250` by
INSTRUCTION rather than by round, the instruction `(y,j)` contributes, once and
for all, the sum of the one-step routing discrepancies over the horizons it is
alive for.  That cumulative reward is the object below.  Its first two moments
under the instruction law are the ones the martingale estimate needs: it is
centred, and its second moment is the truncated Green variance
`Parking.orientedGamma`, which is what `parking.tex:3252-3272` calls
`Gamma_m(y)`.  Nothing is lost to cross terms: the directed walk visits a layer
at one time only, so the cumulative variance is the sum of the one-step
variances, which is `Parking.orientedGamma_eq_sum`.
-/
import Parking.Support.OrientedRoutingCoordinate
import Parking.Support.OrientedInstructionIntegral

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

/-- The routing discrepancy of one instruction at `y`, accumulated over the
horizons `l < M`. -/
def orientedCumDisc (M : ℕ) (y z : Site d) : ℝ :=
  ∑ l ∈ range M, orientedRouteDisc l y z

theorem orientedCumDisc_zero (y z : Site d) : orientedCumDisc 0 y z = 0 := by
  simp [orientedCumDisc]

/-- The cumulative discrepancy is the truncated Green function at the arrival
site, recentred by its mean over the departure kernel. -/
theorem orientedCumDisc_eq (hd : 1 ≤ d) (M : ℕ) (y z : Site d) :
    orientedCumDisc M y z =
      orientedGreen d M z - (∑ i : Fin d, orientedGreen d M (y + unit i)) / d := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.zero_lt_of_lt hd))
  have hlayer : ∀ l : ℕ, orientedLayer d (l + 1) y
      = (∑ i : Fin d, orientedLayer d l (y + unit i)) / d := fun l => orientedLayer_succ l y
  calc orientedCumDisc M y z
      = ∑ l ∈ range M, (orientedLayer d l z - orientedLayer d (l + 1) y) := rfl
    _ = (∑ l ∈ range M, orientedLayer d l z)
          - ∑ l ∈ range M, orientedLayer d (l + 1) y := by rw [sum_sub_distrib]
    _ = orientedGreen d M z - ∑ l ∈ range M, (∑ i : Fin d, orientedLayer d l (y + unit i)) / d := by
        rw [orientedGreen]
        exact congrArg _ (sum_congr rfl fun l _ => hlayer l)
    _ = orientedGreen d M z - (∑ i : Fin d, orientedGreen d M (y + unit i)) / d := by
        congr 1
        rw [← sum_div, sum_comm]
        exact congrArg (· / (d : ℝ)) (sum_congr rfl fun i _ => rfl)

/-- **The cumulative discrepancy is centred** under the instruction law, so each
instruction contributes a martingale increment. -/
theorem integral_orientedCumDisc (hd : 1 ≤ d) (M : ℕ) (y : Site d) :
    (∫ z, orientedCumDisc M y z ∂(orientedInstructionLaw y)) = 0 := by
  rw [integral_orientedInstructionLaw]
  have he : ∀ i : Fin d, orientedCumDisc M y (y + unit i)
      = orientedGreen d M (y + unit i) - (∑ j : Fin d, orientedGreen d M (y + unit j)) / d :=
    fun i => orientedCumDisc_eq hd M y (y + unit i)
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.zero_lt_of_lt hd))
  simp only [he, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- **The second moment of the cumulative discrepancy is the truncated Green
variance** `Gamma_M(y)` of `parking.tex:3252-3256`. -/
theorem integral_orientedCumDisc_sq (hd : 1 ≤ d) (M : ℕ) (y : Site d) :
    (∫ z, orientedCumDisc M y z ^ 2 ∂(orientedInstructionLaw y)) = orientedGamma d M y := by
  rw [integral_orientedInstructionLaw]
  have he : ∀ i : Fin d, orientedCumDisc M y (y + unit i)
      = orientedGreen d M (y + unit i) - (∑ j : Fin d, orientedGreen d M (y + unit j)) / d :=
    fun i => orientedCumDisc_eq hd M y (y + unit i)
  simp only [he]
  rfl

/-- The cumulative discrepancy is bounded by one: the truncated Green function
of the directed walk is between zero and one, and so is its kernel average. -/
theorem abs_orientedCumDisc_le (hd : 1 ≤ d) (M : ℕ) (y z : Site d) :
    |orientedCumDisc M y z| ≤ 1 := by
  rw [orientedCumDisc_eq hd M y z]
  have h1 : 0 ≤ orientedGreen d M z := orientedGreen_nonneg M z
  have h2 : orientedGreen d M z ≤ 1 := orientedGreen_le_one hd M z
  have h3 : 0 ≤ (∑ i : Fin d, orientedGreen d M (y + unit i)) / d :=
    div_nonneg (sum_nonneg fun j _ => orientedGreen_nonneg M _) (Nat.cast_nonneg _)
  have h4 : (∑ i : Fin d, orientedGreen d M (y + unit i)) / d ≤ 1 := by
    have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.zero_lt_of_lt hd
    rw [div_le_one hd0]
    calc (∑ i : Fin d, orientedGreen d M (y + unit i))
        ≤ ∑ _i : Fin d, (1 : ℝ) := sum_le_sum fun j _ => orientedGreen_le_one hd M (y + unit j)
      _ = d := by simp
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Parking
end
