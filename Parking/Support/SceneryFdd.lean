/-
**The finite-dimensional convergence in law of the rescaled scenery pairings to the canonical
spatial white noise**: for finitely many test functions `φ_1,...,φ_m`,
`(Parking.scenePair w R (φ i))_i` converges in law, as `R → ∞` over the REAL parameter `atTop`,
to `(W(φ i))_i` for `W` the canonical spatial white noise `Parking.contW` of intensity
`variance ν` (`Parking.Support.ScalWhiteNoise`), on the canonical Gaussian sample space
`LatticeProb.whiteNoiseLaw`.

Route: `scenePair w R φ` is, for each fixed `R`, EXACTLY `R^{-d/2}` times a finite weighted sum of
the i.i.d. scenery (the weight `R^{-d/2}·φ(y/R)` vanishing outside a finite box by `φ`'s compact
support, `Parking.Support.RiemannLattice`); the scalar triangular-array CLT
(`Parking.tendsto_charFun_weighted_scenery_sum_filter`, `Parking.Support.SpatCLTFilter`) gives the
characteristic-function limit of any single linear combination `∑ₖ tₖ·scenePair w R (φ k)` (itself
one weighted sum, at the combined test function `ψ := ∑ₖ tₖ·φ k`), with limiting variance
`variance ν · ∫ψ²` identified by the real-parameter multi-dimensional Riemann sum
(`Parking.tendsto_latticeSum_mul_rpow`, `Parking.Support.RiemannLattice`) — exactly the covariance
`Parking.contW`'s own Gaussian law has at `ψ` (`Parking.map_contW`).  The real-parameter
Cramer-Wold theorem
(`Parking.Generic.CramerWold.tendstoInDistribution_of_tendsto_charFun_linearCombination_filter`,
`Parking.Generic.CramerWoldFilter`) assembles the finitely many scalar limits into the
finite-dimensional convergence in law, and
`Parking.Generic.CramerWold.tendsto_integral_of_tendstoInDistribution` reads it off against every
bounded continuous test function, exactly the shape `prop:spatial-scaling`'s clause needs.
-/
import Parking.Support.SpatCLTFilter
import Parking.Generic.CramerWoldFilter
import Parking.Support.RiemannLattice
import Parking.Support.ScalWhiteNoise
import Parking.Support.UConcBridge

open MeasureTheory ProbabilityTheory Filter Topology LatticeProb
open scoped ENNReal NNReal

noncomputable section
namespace Parking

variable {d : ℕ}

/-! ### A finite linear combination of test functions is a test function -/

theorem isTestFun_finset_sum {m : ℕ} {φ : Fin m → (Fin d → ℝ) → ℝ} (t : Fin m → ℝ)
    (hφ : ∀ i, IsTestFun (φ i)) :
    IsTestFun (fun x => ∑ i, t i * φ i x) := by
  constructor
  · exact ContDiff.sum fun i _ => (hφ i).1.const_smul (t i)
  · have heq : (fun x => ∑ i, t i * φ i x) = ∑ i : Fin m, (fun x => t i * φ i x) := by
      funext x; simp
    rw [heq]
    exact HasCompactSupport.finset_sum fun i _ => HasCompactSupport.mul_left (hφ i).2

/-! ### The one-site variance of `ν`, read as the second moment of `realLaw ν` -/

theorem variance_eq_integral_sq_realLaw (ν : Measure ℤ) (hν : CriticalLaw ν) :
    variance (fun k : ℤ => (k : ℝ)) ν = ∫ x : ℝ, x ^ 2 ∂(realLaw ν) := by
  haveI := hν.prob
  rw [variance_eq_integral measurable_intCastReal.aemeasurable]
  have hmean : ν[fun k : ℤ => (k : ℝ)] = 0 := hν.mean
  simp only [hmean, sub_zero]
  exact (realLaw_integral ν (f := fun x : ℝ => x ^ 2) (by fun_prop)).symm

/-! ### A uniform sup-norm bound for finitely many test functions and their combination -/

theorem exists_uniform_norm_bound {m : ℕ} {φ : Fin m → (Fin d → ℝ) → ℝ}
    (hφ : ∀ i, IsTestFun (φ i)) :
    ∃ B : ℝ, 0 < B ∧ (∀ i x, φ i x ≠ 0 → ‖x‖ ≤ B) := by
  choose Bi hBipos hBi using fun i => exists_norm_bound_of_hasCompactSupport (hφ i).2
  have h0 : (0:ℝ) ≤ ∑ i, Bi i := Finset.sum_nonneg (fun i _ => (hBipos i).le)
  refine ⟨1 + ∑ i, Bi i, by linarith, fun i x hx => ?_⟩
  have h1 : Bi i ≤ ∑ j, Bi j := Finset.single_le_sum (fun j _ => (hBipos j).le) (Finset.mem_univ i)
  exact (hBi i x hx).trans (by linarith)

/-! ### The exact finite-sum identity: a linear combination of `scenePair` values is one
weighted sum of the i.i.d. scenery -/

theorem scenePair_linearCombination_eq_sum {m : ℕ} {φ : Fin m → (Fin d → ℝ) → ℝ}
    (t : Fin m → ℝ) {B : ℝ} (hB : 0 < B) (hbound : ∀ i x, φ i x ≠ 0 → ‖x‖ ≤ B)
    {R : ℝ} (hR : 1 ≤ R) (w : Data d) :
    ∑ i, t i * scenePair w R (φ i)
      = ∑ y ∈ sceneryBox d B R,
          (R ^ (-(d : ℝ) / 2) * (fun x => ∑ i, t i * φ i x) (fun j => (y j : ℝ) / R))
            * confReal w y := by
  have hstep1 : ∀ i, scenePair w R (φ i)
      = ∑ y ∈ sceneryBox d B R, R ^ (-(d : ℝ) / 2) * (confReal w y * φ i (fun j => (y j : ℝ) / R)) := by
    intro i
    have hs : scenePair w R (φ i)
        = R ^ (-(d : ℝ) / 2) * ∑ y ∈ sceneryBox d B R,
            confReal w y * φ i (fun j => (y j : ℝ) / R) := by
      show R ^ (-(d : ℝ) / 2) * ∑' y : Site d, (w.1 y : ℝ) * φ i (fun j => (y j : ℝ) / R) = _
      congr 1
      apply tsum_eq_sum
      intro y hy
      by_contra hne
      apply hy
      apply mem_sceneryBox_of_ne_zero hB (hbound i) hR
      intro hz
      exact hne (by rw [hz, mul_zero])
    rw [hs, Finset.mul_sum]
  calc ∑ i, t i * scenePair w R (φ i)
      = ∑ i, ∑ y ∈ sceneryBox d B R,
          t i * (R ^ (-(d : ℝ) / 2) * (confReal w y * φ i (fun j => (y j : ℝ) / R))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hstep1 i, Finset.mul_sum]
    _ = ∑ y ∈ sceneryBox d B R, ∑ i,
          t i * (R ^ (-(d : ℝ) / 2) * (confReal w y * φ i (fun j => (y j : ℝ) / R))) :=
        Finset.sum_comm
    _ = ∑ y ∈ sceneryBox d B R,
          (R ^ (-(d : ℝ) / 2) * (fun x => ∑ i, t i * φ i x) (fun j => (y j : ℝ) / R))
            * confReal w y := by
        refine Finset.sum_congr rfl fun y _ => ?_
        show ∑ i, t i * (R ^ (-(d : ℝ) / 2) * (confReal w y * φ i (fun j => (y j : ℝ) / R)))
          = (R ^ (-(d : ℝ) / 2) * ∑ i, t i * φ i (fun j => (y j : ℝ) / R)) * confReal w y
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring

end Parking
end
