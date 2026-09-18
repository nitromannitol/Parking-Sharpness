/-
External input: BouRabeePanagiotis2026's Proposition 4.3 ("Invariance of the heat
potential"), the joint space-time weak convergence of the rescaled, interpolated LINEAR
membrane field, in its own vocabulary.  Here "BP" (Bou-Rabee and Panagiotis, *Quantitative
explosion and percolation of the divisible sandpile*) is the paper formalized separately in
the divisible-sandpile repository; this repository does not rebuild its Theorem 1.3(i)(b) or
its Proposition 4.3.

BP's own statement (page 27, Section 4.2):

  "Proposition 4.3 (Invariance of the heat potential).  Fix `0 < T < ∞`.  Then
   `Z_R^lin ⟹ Z` locally uniformly on `[0,T] × R^d`."

where (same page) `Z_R(r,w) := R^{d/2-2} Σ_z g_{⌊R²r⌋}(⌊Rw⌋,z)ζ(z)` is BP's rescaled linear
field and "`Z_R^lin`" is "the standard interpolation of `Z_R` from the mesh
`R^{-2}Z_+ × R^{-1}Z^d`" (`Parking.linHatInterp`, `Parking/Support/LinInterp.lean`).
`Z` is the white-noise field BP defines earlier (Section 2.2, equation (19), page
17 of the PDF, already quoted by `Parking.External.SpatialFixedTimeTightness`'s docstring):
"`Z(t,x) := √(Var ζ(0)) W(g_t^{BM}(x,·))`", `g_t^BM` the finite-time Green kernel
`g_t^{BM}(x,y) = ∫₀^t p_a^{BM}(x,y) da`, and `W` white noise on `R^d`, "that is, the
mean-zero Gaussian linear functional on `L²(R^d)` with covariance `Cov(W(f),W(g)) = ∫f(x)g(x)dx`"
(page 17, immediately above equation (15)): `W` itself has UNIT intensity, and the whole
factor `√(Var ζ(0))` multiplying the pairing is what gives `Z` its `Var ζ(0)`-intensity
covariance (this agrees with the covariance clause below: with `W` at unit
intensity, `Cov(Z(r,x),Z(s,y)) = Var ζ(0)·⟨g_r^{BM}(x,·),g_s^{BM}(y,·)⟩`, linear in `Var
ζ(0)`, exactly that clause; `W` at intensity `Var ζ(0)` itself would instead give a
factor of `(Var ζ(0))²`, contradicting it).

WHAT "LOCALLY UNIFORMLY" IS TRANSCRIBED AS.  Convergence in law "locally uniformly on
`[0,T]×R^d`" is read through a fixed compactly-supported smooth cutoff: for EVERY test
function `χ` (`Parking.IsSpaceTimeTest`,
already restricted to positive times, matching `prop:spatial-scaling`'s own domain) and
EVERY bounded continuous functional `F` of the cut-off field, the expectation of `F` at the
discrete field converges to its expectation at the cut-off limit field.  This is the
STANDARD way "locally uniform" convergence in law is tested without building `C_loc` as its
own topological space object in this repository (`Parking.cutoffBC`,
`Parking/Support/LinInterp.lean`): since `χ` is fixed and compactly supported, the cut-off
field is a genuine element of `BoundedContinuousFunction (R × (Fin d → R)) R`, and testing
against every such cutoff and every bounded continuous `F` of the RESULT is exactly
convergence in law of the field restricted to any compact set, i.e. exactly what "locally
uniformly" asserts, with no strengthening (a wider cutoff only widens the class of `F`
being tested, never narrows what "locally uniform convergence in law" already means) and no
extrapolation of BP's proof mechanism: it is the plain content of the displayed conclusion.
This reading is STRONGER than the fixed-time equicontinuity that
`Parking.External.SpatialFixedTimeTightness` extracts from the analogous phrase for the
odometer, because the passage from the linear field to the divisible odometer runs through the
extended continuous mapping theorem (`Parking.Support.ExtendedMapping.extended_continuous_mapping`),
which needs genuine convergence in law of the field itself, not merely its equicontinuity.

WHAT `Z` IS ASSERTED TO SATISFY, HERE.  `Z` is asserted to exist together with the
structural properties BP's own definition gives it: mean-zero (implicit, `Z _ 0 _ = 0`
already forces this at time `0`, and the covariance formula below is the only further use
made of it), jointly continuous, vanishing at time `0`, and with covariance
`Var(ζ(0))·∫₀^r∫₀^s contHeatKernel(d,a+b,w,v) da db`.  This covariance formula is the
Chapman-Kolmogorov (semigroup) reduction of BP's own displayed formula
`∫g_r^BM(w,y)g_s^BM(v,y)dy` (expand each finite-time Green kernel as `∫₀^{(\cdot)}
p_a^{BM}da`, swap the two time integrals outside the `y`-integral by Fubini, and use
`∫_y p_a^{BM}(w,y)p_b^{BM}(v,y)dy = p_{a+b}^{BM}(w,v)`, the semigroup property of the
Brownian heat kernel): it is an ELEMENTARY consequence of BP's own DEFINITION of `Z` as a
white-noise pairing (an isometry, so its covariance is the inner product of the two Green
kernels), not a restatement of BP's proof MECHANISM for Proposition 4.3 itself, so recording
it here is transcription of BP's definitions, not an extrapolation of BP's argument.
`Parking.External.contHeatKernel` already transcribes BP's equation (14),
`p_t^{BM}(x,y) = (4πt/(2d))^{-d/2}exp(-d|x-y|²/(2t))`.

THE WHITE NOISE `W` AND THE PAIRING IDENTITY.  The existential also exhibits the white noise
`W` of BP's equation (19) itself, and the pairing identity `Z ω' t x =
√(Var ζ(0)) · W (g_t^{BM}(x,·)) ω'` for `t ≥ 0`, both literal transcriptions of the quoted
definitions (not of BP's proof of Proposition 4.3).  `Parking.External.contFiniteGreen d t x
y := ∫ a in Ioc 0 t, contHeatKernel d a x y` names BP's `g_t^{BM}(x,y)`.  The white noise `W`
is taken at UNIT intensity (`Parking.IsSpatialWhiteNoise d 1 Q' W`), as in the source: BP
states (page 17, immediately above equation (15), quoted above) that `W`'s OWN covariance is
`Cov(W(f),W(g)) = ∫fg` with no `Var ζ(0)` factor, and the `√(Var ζ(0))` sits OUTSIDE the
pairing in equation (19).  Taking `W` at intensity `Var ζ(0)` instead, combined with the
`√(Var ζ(0))`-scaled pairing, would give `Cov(Z(r,x),Z(s,y)) = (Var ζ(0))² ·
⟨g_r^{BM}(x,·), g_s^{BM}(y,·)⟩`, contradicting the covariance clause above (linear in
`Var ζ(0)`, an elementary isometry consequence of the SAME definition).  With `W` at unit
intensity, the covariance consequence of the pairing identity is consistent with that
clause.

WHAT IS NOT ASSUMED.  Nothing about `Parking.barDivisible`, `Parking.barOdometer`,
`Parking.u`, or a coupling of `Z`'s probability space to an independent Brownian motion:
those are the surrounding proof's own objects (the proof uses `Z` only as the reward
field of a SEPARATE optimal-stopping value, built from `Parking.u_eq_potential_add_
stoppingSup`, `Parking.Support.ValueLipschitz` and `Parking.External.SpatialStoppingStability`
through `Parking.Support.ExtendedMapping.extended_continuous_mapping`).  Nothing about
`Parking.scenePair`'s own limit being literally the SAME random variable as `W` here (`W` is
asserted only to be A spatial white noise of the stated variety on `Z`'s own space `Ω'`; that
its finite-dimensional law coincides with `Parking.contW`'s canonical realization, so that the
two can be combined on one product space, is a SEPARATE fact — any two witnesses of
`IsSpatialWhiteNoise d v` have the same finite-dimensional Gaussian law by the definition's
own mean/covariance/Gaussian-marginal clauses — used, not reproved, where the joint clause is
assembled).

VACUITY.  Checked at the paper's own model, `Z^d` with a critical i.i.d. scenery: the
covariance target is a finite double integral of a positive, bounded (away from `a+b=0`)
continuous function over a bounded rectangle, so it is never the junk value of an
undefined/infinite integral; `Parking.cutoffBC` never needs a nonempty cutoff class (`Parking.
IsSpaceTimeTest` is satisfiable, e.g. by a standard bump function on a small space-time ball
away from `s=0`), so the weak-convergence clause is a genuine constraint on a nonempty
family of tests, not vacuously true over an empty class.  `Parking.External.contFiniteGreen d
t x y` is a genuine real number for every `t ≥ 0` (the same finite-integral check as the
covariance clause's inner integral, at `s = 0` collapsing to one time variable), and
`Parking.IsSpatialWhiteNoise d 1` is satisfiable (`Parking.contW 1` on
`LatticeProb.whiteNoiseLaw`, the SAME construction `Parking.isSpatialWhiteNoise_contW`
already uses for `Parking.tendsto_scenePair_fdd`'s own limit, at `v := 1` instead of the
general `v`), so the existential is not vacuous.
-/
import Parking.Support.LinInterp
import Parking.External.SRWLocalCLT
import Parking.Support.Continuum

open MeasureTheory ProbabilityTheory Filter Topology

/-- **The finite-time Brownian Green kernel**, BP's `g_t^{BM}(x,y) = ∫₀^t p_a^{BM}(x,y) da`
(equation (14)-(19), page 17). -/
noncomputable def Parking.External.contFiniteGreen (d : ℕ) (t : ℝ) (x y : Fin d → ℝ) : ℝ :=
  ∫ a in Set.Ioc (0 : ℝ) t, Parking.External.contHeatKernel d a x y

-- FROZEN-STATEMENT-BEGIN
/-- BouRabeePanagiotis2026's Proposition 4.3 ("Invariance of the heat potential", page 27):
the rescaled, interpolated linear membrane field converges in law, locally uniformly, to the
white-noise-driven continuum field `Z`, exhibited together with the white noise `W`, and in the
scenery-retained form the paper cites at parking.tex:1741-1744 ("the argument proving the
parabolic scaling limit in BP, with the time variable and scenery retained, gives the joint
convergence of `(η_R, ū_R)`"): the scenery pairings `η_R(φ) = scenePair` converge jointly
with the linear field to `(√Var ζ(0) · W(φ), Z)`, with the cross-covariance
`E[W(φ) Z(t,x)] = √Var ζ(0) ∫ φ(y) g_t^{BM}(x,y) dy`.

What `Z` and `W` are assumed to share is exactly the covariance structure written here: the
covariance of `Z` with itself, and its cross-covariance with `W` against test functions.
The displayed identity `Z(t,x) = √Var ζ(0) · W(g_t^{BM}(x,·))` is recorded as well, but it
carries no force on its own, since the white-noise axioms bind `W` only on test functions
and the Green kernel is not compactly supported. -/
def Parking.External.LinearFieldScaling : Prop :=
  ∀ (d : ℕ), 1 ≤ d → d ≤ 3 → ∀ (ν : Measure ℤ), Parking.CriticalLaw ν →
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q' : Measure Ω') (_ : IsProbabilityMeasure Q')
      (W : ((Fin d → ℝ) → ℝ) → Ω' → ℝ)
      (Z : Ω' → ℝ → (Fin d → ℝ) → ℝ)
      (hZcont : ∀ ω', Continuous fun p : ℝ × (Fin d → ℝ) => Z ω' p.1 p.2),
      Parking.IsSpatialWhiteNoise d 1 Q' W ∧
      (∀ φ, Parking.IsTestFun φ → Measurable (W φ)) ∧
      (∀ ω' t x, 0 ≤ t → Z ω' t x
          = Real.sqrt (variance (fun k : ℤ => (k : ℝ)) ν) *
            W (fun y => Parking.External.contFiniteGreen d t x y) ω') ∧
      (∀ ω' x, Z ω' 0 x = 0) ∧
      (∀ r x, Measurable fun ω' => Z ω' r x) ∧
      (∀ r x s y, 0 ≤ r → 0 ≤ s →
        Integrable (fun ω' => Z ω' r x * Z ω' s y) Q' ∧
        ∫ ω', Z ω' r x * Z ω' s y ∂Q'
          = variance (fun k : ℤ => (k : ℝ)) ν *
            ∫ a in Set.Ioc (0 : ℝ) r, ∫ b in Set.Ioc (0 : ℝ) s,
              Parking.External.contHeatKernel d (a + b) x y) ∧
      (∀ (χ : ℝ × (Fin d → ℝ) → ℝ) (hχ : Parking.IsSpaceTimeTest χ),
        ∀ F : BoundedContinuousFunction (BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ) ℝ,
          Tendsto (fun R : ℝ =>
              ∫ w : Parking.Data d,
                F (Parking.cutoffBC χ (Parking.linHatInterp (fun y => (w.1 y : ℝ)) R)
                    hχ.1.continuous hχ.2.1
                    (Parking.continuous_linHatInterp (fun y => (w.1 y : ℝ)) R))
                ∂(Parking.law d ν))
            atTop
            (𝓝 (∫ ω', F (Parking.cutoffBC χ (fun p => Z ω' p.1 p.2) hχ.1.continuous hχ.2.1
                    (hZcont ω')) ∂Q'))) ∧
      (∀ φ, Parking.IsTestFun φ → ∀ t x, 0 ≤ t →
        Integrable (fun ω' => W φ ω' * Z ω' t x) Q' ∧
        ∫ ω', W φ ω' * Z ω' t x ∂Q'
          = Real.sqrt (variance (fun k : ℤ => (k : ℝ)) ν) *
            ∫ y, φ y * Parking.External.contFiniteGreen d t x y) ∧
      (∀ (m : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ), (∀ i, Parking.IsTestFun (φ i)) →
        ∀ (χ : ℝ × (Fin d → ℝ) → ℝ) (hχ : Parking.IsSpaceTimeTest χ),
        ∀ F : BoundedContinuousFunction
            ((Fin m → ℝ) × BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ) ℝ,
          Tendsto (fun R : ℝ =>
              ∫ w : Parking.Data d,
                F (fun i => Parking.scenePair w R (φ i),
                  Parking.cutoffBC χ (Parking.linHatInterp (fun y => (w.1 y : ℝ)) R)
                    hχ.1.continuous hχ.2.1
                    (Parking.continuous_linHatInterp (fun y => (w.1 y : ℝ)) R))
                ∂(Parking.law d ν))
            atTop
            (𝓝 (∫ ω', F (fun i => Real.sqrt (variance (fun k : ℤ => (k : ℝ)) ν) * W (φ i) ω',
                  Parking.cutoffBC χ (fun p => Z ω' p.1 p.2) hχ.1.continuous hχ.2.1
                    (hZcont ω')) ∂Q')))
-- FROZEN-STATEMENT-END
