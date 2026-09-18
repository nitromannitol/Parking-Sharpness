/-
Proposition 8.3 of parking.tex, frozen.  `parking.tex:1679-1737` (label
`prop:spatial-scaling`):

  "Let $d\leq3$, and let $(\eta(x))$ be i.i.d., integer-valued and nonconstant,
   with $\E\eta(0)=0$ and $\E e^{\theta|\eta(0)|}<\infty$ for some $\theta>0$.
   For $R>0$, $s\geq0$ and $x\in\mathbb R^d$, let
   $\overline U_R(s,x)=R^{d/2-2}U_{\lfloor sR^2\rfloor}(\lfloor Rx\rfloor)$ and
   $\overline u_R(s,x)=R^{d/2-2}u_{\lfloor sR^2\rfloor}(\lfloor Rx\rfloor)$;
   let $\langle\eta_R,\varphi\rangle=R^{-d/2}\sum_y\eta(y)\varphi(y/R)$ and
   $\langle\nu_R,\varphi\rangle=R^{-d/2}\sum_y(A_{\lfloor R^2\rfloor}(y)
   -H_{\lfloor R^2\rfloor}(y))\varphi(y/R)$.  Let $\mathcal W$ be a mean-zero
   spatial white noise with covariance
   $\E\langle\mathcal W,\varphi\rangle\langle\mathcal W,\psi\rangle
   =\Var\eta(0)\int\varphi\psi$.  Let $\mathcal U$ be the continuous Brownian
   optimal-stopping value driven by $\mathcal W$, with $\mathcal U(0,\cdot)=0$.
   Then, jointly, $(\eta_R,\overline u_R,\overline U_R)\Rightarrow
   (\mathcal W,\mathcal U,\mathcal U)$ as $R\to\infty$, with the first
   coordinate converging as a random distribution and the last two locally
   uniformly on $(0,\infty)\times\mathbb R^d$.  Let
   $\mathcal O=\{\mathcal U>0\}$ and $\mathcal L=(2d)^{-1}\Delta$.  Then, in
   the sense of distributions on $\mathcal O$,
   $\partial_s\mathcal U=\mathcal L\mathcal U+\mathcal W$.  For every
   $\varphi\in C_c^\infty$, jointly with the above,
   $\langle\nu_R,\varphi\rangle\Rightarrow
   \langle\mathcal W+\mathcal L\mathcal U(1,\cdot),\varphi\rangle$.  Moreover,
   on $\mathcal O$ the distribution $v=\partial_s\mathcal U$ is a smooth
   function and $v(s,x)>0$ on $\mathcal O$."

The Brownian optimal-stopping identification exhibits the Green field of the
same noise through its L² extension and an independent Brownian space, with
`Uc = Parking.contUc` for every nonnegative horizon. "Converging locally
uniformly" is transcribed as three clauses: the joint convergence of the
finite-dimensional distributions, the vanishing in probability of the local
uniform distance between the two rescaled odometers, and the equicontinuity in
probability of the rescaled divisible odometer on every compact set of positive
times.  Together these are convergence in distribution in the topology of local
uniform convergence on `(0,∞)×ℝ^d`, which is what the proof of `thm:nearest`
uses.  Convergence in
distribution is stated through bounded continuous test functions, and the
limiting field and the noise are asserted measurable, so that their laws and
their means are those of genuine random variables.

The divisible odometer's scaling limit, Brownian representation and joint
space-time equicontinuity are cited from BP Theorem 1.3(i)(b) through
`Parking.External.SpatialOdometerScaling`. The four growth and concentration
inputs feed the signed-density martingale estimate and the transfer to the
parking odometer. The driven equation and strict positivity of the time
derivative are proved downstream using the three classical parabolic inputs.
-/
import Parking.Support.Continuum
import Parking.External.SandpileGrowth
import Parking.External.Bernstein
import Parking.External.UConcentration
import Parking.External.GreenNorms
import Parking.External.SpatialOdometerScaling
import Parking.Support.UpperTarget
import Parking.Support.SpatialDerivativeLimit
import Parking.Support.SpatialVanishingDistance
import Parking.Support.SpatWSignedJoint
import Parking.Support.SpatialFixedTestPDE
import Parking.Support.SpatialNoiseVersion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.spatial_scaling (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration)
    (hGreenNorms : Parking.External.GreenNorms)
    (hOdometer : Parking.External.SpatialOdometerScaling)
    (hInterior : Parking.External.HeatInteriorRegularity)
    (hMinimum : Parking.External.HeatStrongMinimum)
    (hCompact : Parking.External.HeatCompactness)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
      (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ) (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ)
      (v : Ω → ℝ → (Fin d → ℝ) → ℝ),
      Parking.IsSpatialWhiteNoise d (variance (fun k : ℤ => (k : ℝ)) ν) Q W ∧
      (∀ φ, Parking.IsTestFun φ → Measurable (W φ)) ∧
      (∀ s x, Measurable fun ω => Uc ω s x) ∧
      (∀ s x, Measurable fun ω => v ω s x) ∧
      (∀ ω x, Uc ω 0 x = 0) ∧
      (∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2) ∧
      (∀ ω x, Monotone fun s => Uc ω s x) ∧
      (∃ Z : Ω → ℝ → (Fin d → ℝ) → ℝ,
        Parking.IsSpatialGreenPairing d (variance (fun k : ℤ => (k : ℝ)) ν) Q W Z ∧
        (∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Z ω p.1 p.2) ∧
        ∃ (ΩB : Type) (_ : MeasurableSpace ΩB) (PB : Measure ΩB)
            (B : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d)),
          LatticeProb.IsBrownianSpace d 0 B PB ∧
          ∀ ω T x, 0 ≤ T →
            Uc ω T x = Parking.contUc (Parking.ofBrownianSpace B) PB Z ω T x) ∧
      (∀ (m k p : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ) (χ : Fin p → (Fin d → ℝ) → ℝ)
          (sp : Fin k → ℝ × (Fin d → ℝ)),
        (∀ i, Parking.IsTestFun (φ i)) → (∀ l, Parking.IsTestFun (χ l)) →
        (∀ j, 0 < (sp j).1) →
        ∀ F : BoundedContinuousFunction
            ((Fin m → ℝ) × (Fin k → ℝ) × (Fin k → ℝ) × (Fin p → ℝ)) ℝ,
          Tendsto (fun R : ℝ => ∫ w, F (fun i => Parking.scenePair w R (φ i),
                fun j => Parking.barDivisible w R (sp j).1 (sp j).2,
                fun j => Parking.barOdometer w R (sp j).1 (sp j).2,
                fun l => Parking.signedPair w R (χ l)) ∂(Parking.law d ν)) atTop
            (𝓝 (∫ ω, F (fun i => W (φ i) ω,
                fun j => Uc ω (sp j).1 (sp j).2,
                fun j => Uc ω (sp j).1 (sp j).2,
                fun l => W (χ l) ω
                  + ∫ x, Uc ω 1 x * Parking.contOp d (χ l) x) ∂Q))) ∧
      (∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → (∀ p ∈ K, 0 < p.1) → ∀ ε : ℝ, 0 < ε →
        Tendsto (fun R : ℝ => ((Parking.law d ν) {w | ε < ⨆ p ∈ K,
            |Parking.barOdometer w R p.1 p.2 - Parking.barDivisible w R p.1 p.2|}).toReal)
          atTop (𝓝 0)) ∧
      (∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → (∀ p ∈ K, 0 < p.1) → ∀ ε : ℝ, 0 < ε →
        ∀ ε' : ℝ, 0 < ε' → ∃ δ : ℝ, 0 < δ ∧ ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
          ((Parking.law d ν) {w | ε < ⨆ p ∈ K, ⨆ q ∈ K, ⨆ _ : dist p q ≤ δ,
              |Parking.barDivisible w R p.1 p.2 - Parking.barDivisible w R q.1 q.2|}).toReal
            ≤ ε') ∧
      (∀ᵐ ω ∂Q, ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, Parking.IsSpaceTimeTest ψ →
        tsupport ψ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} →
        -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => ψ (s, p.2)) p.1
          = (∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * Parking.contOp d (fun x => ψ (p.1, x)) p.2)
            + W (fun x => ∫ s : ℝ, ψ (s, x)) ω) ∧
      (∀ᵐ ω ∂Q, ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) => v ω p.1 p.2)
          {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} ∧
        (∀ ψ : ℝ × (Fin d → ℝ) → ℝ, Parking.IsSpaceTimeTest ψ →
          tsupport ψ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} →
          -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => ψ (s, p.2)) p.1
            = ∫ p : ℝ × (Fin d → ℝ), v ω p.1 p.2 * ψ p) ∧
        ∀ s x, 0 < Uc ω s x → 0 < v ω s x)
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨Ω, mΩ, Q, hQ, W, Z, Uc, hW, hWmeas, hZeq, hZcont, hUc0, hUccont, hUcmono, hUcmeas,
      hsuprep, hjointFDD, hequicont⟩ := hOdometer d hd hd3 ν hν
  haveI := hν.prob
  haveI := Parking.law_isProb hd ν
  have hfixed : ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, Parking.IsSpaceTimeTest ψ →
      ∀ᵐ ω ∂Q, tsupport ψ ⊆ {p | 0 < Uc ω p.1 p.2} →
      -(∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => ψ (s, p.2)) p.1)
        = (∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * Parking.contOp d (fun x => ψ (p.1, x)) p.2)
          + W (fun x => ∫ s : ℝ, ψ (s, x)) ω := by
    intro ψ hψ
    filter_upwards [Parking.spatial_fixed_test_residual_ae hd hd3 hGrowth ν hν
      hUccont hUcmeas hWmeas hjointFDD hequicont hψ] with ω hω hsupp
    have h := hω hsupp
    rw [Parking.integral_spaceTimeResidualTest (hUccont ω) hψ] at h
    linarith
  obtain ⟨W', hW', hW'meas, hWeq, hpde⟩ :=
    Parking.exists_spatial_noise_version_of_fixed_pde Q W Uc
      hW hWmeas hUccont hUcmeas hfixed
  have hjointFDD' (m p' : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ)
      (sp : Fin p' → ℝ × (Fin d → ℝ))
      (hφ : ∀ i, Parking.IsTestFun (φ i)) (hsp : ∀ j, 0 < (sp j).1)
      (F : BoundedContinuousFunction ((Fin m → ℝ) × (Fin p' → ℝ)) ℝ) :
      Tendsto (fun R : ℝ => ∫ w, F (fun i => Parking.scenePair w R (φ i),
          fun j => Parking.barDivisible w R (sp j).1 (sp j).2) ∂Parking.law d ν) atTop
        (𝓝 (∫ ω, F (fun i => W' (φ i) ω, fun j => Uc ω (sp j).1 (sp j).2) ∂Q)) := by
    have he : (∫ ω, F (fun i => W' (φ i) ω, fun j => Uc ω (sp j).1 (sp j).2) ∂Q) =
        ∫ ω, F (fun i => W (φ i) ω, fun j => Uc ω (sp j).1 (sp j).2) ∂Q := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr (fun i => hWeq (φ i) (hφ i))] with ω hω
      have hfun : (fun i => W' (φ i) ω) = (fun i => W (φ i) ω) := funext hω
      rw [hfun]
    rw [he]
    exact hjointFDD m p' φ sp hφ hsp F
  have hjoint := Parking.tendsto_spatial_signed_joint hd hd3 hGrowth hBernstein
    hConcentration hGreenNorms ν hν hUccont hUcmeas (fun φ _ => hW'meas φ)
    hjointFDD' hequicont
  obtain ⟨v, hvmeas, hv⟩ := Parking.exists_spatial_derivative_of_pde
    hInterior hMinimum hCompact hd Q W' Uc hUcmeas hUc0 hUccont hUcmono hpde
  exact ⟨Ω, mΩ, Q, hQ, W', Uc, v, hW', (fun φ _ => hW'meas φ),
    hUcmeas, hvmeas, hUc0, hUccont, hUcmono, ⟨Z, hZeq.congr_noise hWeq, hZcont, hsuprep⟩,
    hjoint, Parking.exists_spatial_vanishing_distance hd hd3 hGrowth hBernstein hConcentration
      hGreenNorms ν hν, hequicont, hpde, hv⟩
