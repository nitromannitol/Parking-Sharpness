/-
External input: Bou-Rabee and Panagiotis, *Quantitative explosion and percolation
of the divisible sandpile*, Theorem 1.3(i)(b), "Critical growth and spatial
scaling" (`sandpile.tex:206-235`, `thm:main-explosion`). The enclosing hypotheses
and the cited part read:

  "Let `σ = 1 + 2dζ`, where `(ζ(x))_{x∈Z^d}` are i.i.d. with `E ζ(0) = 0` and
   `0 < Var(ζ(0)) < ∞`.  In parts (i), (ii), and (iii)(a)-(b), assume additionally that
   `E e^{θ₀|ζ(0)|} < ∞` for some `θ₀ > 0`."

  "(i) Dimensions one, two, and three.
   ...
   (b) The parabolic scaling limit is a Brownian optimal-stopping value.  Let `𝒲` be white
   noise on `R^d`, let
     `Z(t,x) := √(Var(ζ(0))) ∫_{R^d} g_t^BM(x,y) 𝒲(dy)`,
   with `g_t^BM` the finite-time Green kernel of Brownian motion, and let
     `𝒰(T,x) := sup_{τ≤T} E_x^BM[Z(T,x) - Z(T-τ,B_τ)]`,
   where the supremum is over stopping times for Brownian motion.  Then, for every `T > 0`,
     `R^{-(2-d/2)} u^{(R)}_{⌊TR²⌋} ⟹ 𝒰(T,·)` in `C_loc(R^d)`,
   where the field on the left denotes the multilinear interpolation from `R^{-1}Z^d` of the
   values `x/R ↦ R^{-(2-d/2)} u_{⌊TR²⌋}(x)`."


Parking uses this theorem in Step 1 of `prop:spatial-scaling`,
`parking.tex:1740-1744`: "The argument proving the parabolic scaling limit in
[BP], with the time variable and scenery retained, gives the joint convergence
of `(η_R, ū_R)`." Its estimates are uniform on compact time intervals. Accordingly
this input retains the scenery and time in the finite-dimensional convergence,
and includes joint space-time equicontinuity on compact sets of positive times.
The lattice normalization is `R^{d/2-2}` and the continuum generator is `Δ/(2d)`.

NOISE AND GREEN PAIRING. BP's noise has unit intensity and the factor `√Var` sits
outside the pairing. Here `W = √Var · W_BP` already has intensity `Var η(0)`, as in
Parking's proposition. `Parking.IsSpatialGreenPairing` supplies a continuous
linear map `I : L²(dx) → L²(Q)` with `‖I f‖ = √Var · ‖f‖`, agreeing with `W` on
every smooth compactly supported test and with `Z(t,x)` at the class of
`contFiniteGreen d t x`. Thus this is the L² white-noise extension, not an
evaluation at an otherwise unspecified non-test coordinate of `W`. Density of
the tests in L² determines the extension. The equalities are coordinatewise
a.e., so they permit the continuous modification `Z` in the cited construction.

BROWNIAN VALUE. `Parking.contUc (Parking.ofBrownianSpace B) PB Z ω T x` unfolds to
`Z ω T x + spatialContValue (ofBrownianSpace B) PB
  (fun k y => -Z ω (T-k) (x+y)) T`.
The Brownian motion starts at zero, independently of the fixed sample `ω`;
translation by `x` gives BP's displayed supremum. The defining equality is
carried together with continuity, time-monotonicity, zero initial value and
coordinate measurability of `Uc`. The supremum's definition admits only
integrable payoffs. This predicate records the value identity; it does not
separately expose boundedness of the set of stopping payoffs.

LEGITIMATE INSTANCE. For i.i.d. critical integer scenery with an exponential
moment in dimensions 1, 2 or 3, take BP's own noise, its continuous Green field,
and its Brownian stopping value. Scaling the unit-intensity isonormal map by
`√Var` gives `I` above. The kernels `g_t(x,·)` are in spatial L², including the
zero kernel at `t=0`. For positive time their possible singularity at `y=x` is
irrelevant to the L² class: in dimensions 2 and 3 the pointwise time integral
there can diverge, and the real Bochner integral assigns its default value.
No pointwise integrability at the diagonal is asserted or used. The explicit
`MemLp` witnesses and the map on L² equivalence classes make the pairing
independent of that value. BP's construction provides the finite Brownian
stopping value and all the asserted regularity and convergence properties.
The probability and positive dimension hypotheses exclude empty probability
spaces and zero-dimensional kernel conventions.

No conclusion about the parking odometer, signed density, driven equation or
strict time derivative is assumed here. Those are proved in Parking from this
input and the separately stated growth and classical parabolic inputs.
-/
import Parking.Support.SpatialGreenPairing
import Parking.Support.ContUc

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

-- FROZEN-STATEMENT-BEGIN
/-- BouRabeePanagiotis2026's Theorem 1.3(i)(b) (`sandpile.tex:206-235`, `thm:main-explosion`):
the parabolic scaling limit of the rescaled divisible odometer is a Brownian optimal-stopping
value driven by a spatial white noise, jointly, with the time variable and scenery retained
(the strengthening `parking.tex:1740-1744` cites for Step 1 of `prop:spatial-scaling`). -/
def Parking.External.SpatialOdometerScaling : Prop :=
  ∀ (d : ℕ), 1 ≤ d → d ≤ 3 → ∀ (ν : Measure ℤ), Parking.CriticalLaw ν →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
      (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ)
      (Z : Ω → ℝ → (Fin d → ℝ) → ℝ)
      (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ),
      Parking.IsSpatialWhiteNoise d (variance (fun k : ℤ => (k : ℝ)) ν) Q W ∧
      (∀ φ, Parking.IsTestFun φ → Measurable (W φ)) ∧
      Parking.IsSpatialGreenPairing d (variance (fun k : ℤ => (k : ℝ)) ν) Q W Z ∧
      (∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Z ω p.1 p.2) ∧
      (∀ ω x, Uc ω 0 x = 0) ∧
      (∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2) ∧
      (∀ ω x, Monotone fun s => Uc ω s x) ∧
      (∀ s x, Measurable fun ω => Uc ω s x) ∧
      (∃ (ΩB : Type) (_ : MeasurableSpace ΩB) (PB : Measure ΩB)
          (B : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d)),
        LatticeProb.IsBrownianSpace d 0 B PB ∧
        ∀ ω T x, 0 ≤ T →
          Uc ω T x = Parking.contUc (Parking.ofBrownianSpace B) PB Z ω T x) ∧
      (∀ (m p' : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ) (sp : Fin p' → ℝ × (Fin d → ℝ)),
        (∀ i, Parking.IsTestFun (φ i)) → (∀ j, 0 < (sp j).1) →
        ∀ F : BoundedContinuousFunction ((Fin m → ℝ) × (Fin p' → ℝ)) ℝ,
          Tendsto (fun R : ℝ =>
              ∫ w : Parking.Data d,
                F (fun i => Parking.scenePair w R (φ i),
                  fun j => Parking.barDivisible w R (sp j).1 (sp j).2) ∂(Parking.law d ν))
            atTop
            (𝓝 (∫ ω, F (fun i => W (φ i) ω, fun j => Uc ω (sp j).1 (sp j).2) ∂Q))) ∧
      (∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → (∀ p ∈ K, 0 < p.1) → ∀ ε : ℝ, 0 < ε →
        ∀ ε' : ℝ, 0 < ε' → ∃ δ : ℝ, 0 < δ ∧ ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
          ((Parking.law d ν) {w | ε < ⨆ p ∈ K, ⨆ q ∈ K, ⨆ _ : dist p q ≤ δ,
              |Parking.barDivisible w R p.1 p.2 - Parking.barDivisible w R q.1 q.2|}).toReal
            ≤ ε')
-- FROZEN-STATEMENT-END
