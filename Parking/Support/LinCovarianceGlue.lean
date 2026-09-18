/-
**The covariance of the linear membrane field, closed form.**

Assembles `Parking.linPotential_eq_sum_of_boxFinset_subset`
(`Parking/Support/LinPotentialSum.lean`), `Parking.integral_sum_mul_sum_pi`
(`Parking/Support/LinCovariance.lean`) and the finite-marginal reduction
`LatticeProb.integral_restrict` into

    E[V_n(x) V_m(y)] = E[η(0)²] · Σ_{z ∈ S} g_n(x-z) g_m(y-z)

for ANY finite `S` containing both `boxFinset x n` and `boxFinset y m`, over an i.i.d.
mean-zero law with a finite second moment.  This is the deterministic finite-sum form of
`Cov(V_n(x), V_m(y))` (BP's own Proposition 4.3 quantity, `Var(η(0)) = E[η(0)²]` here since
`E[η(0)] = 0`).  The finite sum is then reduced to the closed form
`Σ_{a<n}Σ_{b<m} P^{a+b}(y-x)` via `LatticeProb.tsum_srwGreen_mul_shift`
(`LatticeProb.Walk.GreenPointwise`), which gives
`E[V_n(x) V_m(y)] = E[η(0)²] · Σ_{a<n}Σ_{b<m} P^{a+b}(y-x)`.
-/
import Parking.Support.LinCovariance
import Parking.Support.LinPotentialSum
import Parking.Support.LinTimeShift
import Parking.Support.SpatGreenShift
import LatticeProb.Walk.GreenPointwise

noncomputable section

open MeasureTheory ProbabilityTheory Finset LatticeProb

namespace Parking

variable {d : ℕ}

/-- **Integrability of the finite bilinear form**, extracted from the SAME machinery
`Parking.integral_sum_mul_sum_pi`'s proof uses, needed to marginalize `iidLaw` down to a
finite box. -/
theorem integrable_sum_mul_sum_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℝ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hint : Integrable (fun x : ℝ => x) ν)
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν) :
    Integrable (fun ξ : ι → ℝ => (∑ i, a i * ξ i) * (∑ j, b j * ξ j))
      (Measure.pi fun _ : ι => ν) := by
  have hindep := iIndepFun_eval_pi (ι := ι) ν
  have hIntEval : ∀ i : ι, Integrable (fun ξ : ι → ℝ => ξ i) (Measure.pi fun _ : ι => ν) :=
    fun i => integrable_eval_pi ν i id hint
  have hIntDiag : ∀ i : ι,
      Integrable (fun ξ : ι → ℝ => ξ i * ξ i) (Measure.pi fun _ : ι => ν) := by
    intro i
    have heq : (fun ξ : ι → ℝ => ξ i * ξ i) = (fun ξ : ι → ℝ => (fun x => x ^ 2) (ξ i)) := by
      funext ξ; ring
    rw [heq]
    exact integrable_eval_pi ν i (fun x => x ^ 2) hsq
  have hIntOff : ∀ i j : ι, i ≠ j →
      Integrable (fun ξ : ι → ℝ => ξ i * ξ j) (Measure.pi fun _ : ι => ν) :=
    fun i j hij => (hindep.indepFun hij).integrable_mul (hIntEval i) (hIntEval j)
  have hIntCross : ∀ i j : ι,
      Integrable (fun ξ : ι → ℝ => (a i * b j) * (ξ i * ξ j)) (Measure.pi fun _ : ι => ν) := by
    intro i j
    by_cases hij : i = j
    · subst hij; exact (hIntDiag i).const_mul _
    · exact (hIntOff i j hij).const_mul _
  have hstep : (fun ξ : ι → ℝ => (∑ i, a i * ξ i) * (∑ j, b j * ξ j))
      = fun ξ => ∑ i, ∑ j, (a i * b j) * (ξ i * ξ j) := by
    funext ξ
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hstep]
  exact integrable_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hIntCross i j))

/-- **`E[V_n(x) V_m(y)]` as a finite sum, over any finite index set containing both boxes.** -/
theorem integral_linPotential_mul (ν0 : Measure ℝ) [IsProbabilityMeasure ν0]
    (hmean : ∫ x, x ∂ν0 = 0) (hint : Integrable (fun x : ℝ => x) ν0)
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν0) {n m : ℕ} {x y : Site d} {S : Finset (Site d)}
    (hSx : boxFinset x n ⊆ S) (hSy : boxFinset y m ⊆ S) :
    ∫ η, linPotential η n x * linPotential η m y ∂(iidLaw d ν0)
      = (∫ z, z ^ 2 ∂ν0) * ∑ z ∈ S, green d n (x - z) * green d m (y - z) := by
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
  have hkey : ∫ η, F (S.restrict η) ∂(iidLaw d ν0) = ∫ ζ : S → ℝ, F ζ ∂(Measure.pi fun _ : S => ν0) :=
    LatticeProb.integral_restrict d ν0 S F hFint
  have hval := integral_sum_mul_sum_pi (ι := S) (fun i : S => a (i : Site d))
    (fun j : S => b (j : Site d)) ν0 hmean hint hsq
  have hlhs : (∫ η, linPotential η n x * linPotential η m y ∂(iidLaw d ν0))
      = ∫ η, F (S.restrict η) ∂(iidLaw d ν0) :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hreindex : (∑ i : S, a (i : Site d) * b (i : Site d)) = ∑ z ∈ S, a z * b z :=
    Finset.sum_coe_sort (M := ℝ) S (fun z => a z * b z)
  rw [hlhs, hkey, hval, hreindex, hadef, hbdef]
  ring

/-- **The finite sum over any box containing BOTH `boxFinset x n` and `boxFinset y m` equals
the full `tsum`**, since the product vanishes off `boxFinset x n` alone. -/
theorem sum_green_mul_eq_tsum {n m : ℕ} {x y : Site d} {S : Finset (Site d)}
    (hSx : boxFinset x n ⊆ S) :
    ∑ z ∈ S, green d n (x - z) * green d m (y - z)
      = ∑' z : Site d, green d n (x - z) * green d m (y - z) := by
  symm
  refine tsum_eq_sum fun z hz => ?_
  have hzx : z ∉ boxFinset x n := fun h => hz (hSx h)
  rw [mem_boxFinset_iff'] at hzx
  have hgt : n < supNorm (x - z) := not_le.mp hzx
  have hgtg : n < graphNorm (x - z) := lt_of_lt_of_le hgt (supNorm_le_graphNorm (x - z))
  rw [green_eq_zero_of_le hgtg.le]
  ring

/-- **`Σ'_z g_n(x-z) g_m(y-z)` in BP's closed form**, via `LatticeProb.tsum_srwGreen_mul_shift`
(the Chapman-Kolmogorov cross-term identity): `Σ_{a<n}Σ_{b<m} P^{a+b}(0, y-x)`. -/
theorem tsum_green_mul_eq_closed_form (n m : ℕ) (x y : Site d) :
    ∑' z : Site d, green d n (x - z) * green d m (y - z)
      = ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range m, LatticeProb.srwHeat d (a + b) (y - x) := by
  have hreidx : ∑' z : Site d, green d n (x - z) * green d m (y - z)
      = ∑' w : Site d, green d n w * green d m (w + (y - x)) := by
    rw [← tsum_comp_subLeft x (fun w => green d n w * green d m (w + (y - x)))]
    refine tsum_congr fun z => ?_
    congr 2
    have : y - z = (x - z) + (y - x) := by abel
    rw [this]
  rw [hreidx]
  have hsrw : ∑' w : Site d, green d n w * green d m (w + (y - x))
      = ∑' w : Site d, LatticeProb.srwGreen d n w * LatticeProb.srwGreen d m (w + (y - x)) := by
    refine tsum_congr fun w => ?_
    rw [green_eq_srwGreen, green_eq_srwGreen]
  rw [hsrw, LatticeProb.tsum_srwGreen_mul_shift n m (y - x)]

/-- **`E[V_n(x) V_m(y)]` in BP's closed form, Proposition 4.3**, combining
`integral_linPotential_mul`, `sum_green_mul_eq_tsum` and `tsum_green_mul_eq_closed_form`. -/
theorem integral_linPotential_mul_closed_form (ν0 : Measure ℝ) [IsProbabilityMeasure ν0]
    (hmean : ∫ x, x ∂ν0 = 0) (hint : Integrable (fun x : ℝ => x) ν0)
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν0) (n m : ℕ) (x y : Site d) :
    ∫ η, linPotential η n x * linPotential η m y ∂(iidLaw d ν0)
      = (∫ z, z ^ 2 ∂ν0)
        * ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range m, LatticeProb.srwHeat d (a + b) (y - x) := by
  have hSx : boxFinset x n ⊆ boxFinset x n ∪ boxFinset y m := Finset.subset_union_left
  have hSy : boxFinset y m ⊆ boxFinset x n ∪ boxFinset y m := Finset.subset_union_right
  rw [integral_linPotential_mul ν0 hmean hint hsq hSx hSy,
    sum_green_mul_eq_tsum hSx, tsum_green_mul_eq_closed_form]

end Parking

end
