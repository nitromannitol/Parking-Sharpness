/-
The scenery-side export for the final assembly of `Parking.Frozen.spatial_scaling`'s joint
clause (`parking.tex:1679-1737`).

What is DISCHARGED here, unconditionally (given the four Externals `Parking.Frozen.growth`
carries): `Parking.tendsto_signedPair_sub_scenePair_of_convergence`
(`Parking/Support/SpatWSignedDecomp.lean`) takes two hypotheses, `hM` (`signedM(φ) → 0` in
probability) and `hMiddle` (`signedMiddle(φ) → L` in probability, for the value side's own
`L`).  `Parking.tendsto_signedM_zero` (`Parking/Support/SpatWMartingaleVariance.lean`) proves
`hM` unconditionally (Lemma 5.3 + Corollary 1.3, `parking.tex:1758-1766`).
`Parking.tendsto_signedPair_sub_scenePair_sub_middle_zero` below plugs it in, leaving ONLY
`hMiddle` as a hypothesis: the convergence `Ū_R(1,·) → 𝒰(1,·)` on the value side, identified
with `L(w) := ∫x, Uc w 1 x * contOp d φ x`.

The joint statement below rests on Slutsky's theorem, in the form `Parking.Generic.Slutsky`
(`Parking/Generic/Slutsky.lean`): Mathlib's own
`MeasureTheory.TendstoInDistribution.prodMk_of_tendstoInMeasure_const` already IS Slutsky's
theorem, in exactly the needed generality (an arbitrary `SeminormedAddCommGroup`, no tightness
hypothesis, proved by a Lipschitz-approximation argument), so `Parking.Generic.Slutsky` is a
short adaptation layer.  `Parking.tendsto_scenePair_linHatInterp_joint_fdd_signedResidual`
below is the three-block export: it combines `Parking.tendsto_scenePair_linHatInterp_joint_fdd`
(the scenery/linear-field block, `X_R`) with the `signedPair(χ)-scenePair(χ)-middle(χ)` block
(`Y_R → 0` in probability, via `Parking.tendsto_signedPair_sub_scenePair_sub_middle_zero` above,
combined coordinatewise by `Parking.Generic.Slutsky.tendsto_zero_pi_of_forall_tendsto_zero`) into
ONE joint statement via `Parking.Generic.Slutsky.tendsto_prodMk_of_tendsto_zero`.  In this
statement the third block converges to `0` (not to `(√v·W(χ_l))_l`), which is equivalent to
`signedPair(χ_l) - L l ⇒ √v·W(χ_l)`: `scenePair(χ_l)` itself also converges to `√v·W(χ_l)`, by
`Parking.tendsto_scenePair_fdd`, so adding it back on both sides recovers the version with the
middle term.  That version is not stated here; the shape with third block `0` is the one the
value side's assembly consumes. -/
import Parking.Support.SpatWMartingaleVariance
import Parking.Support.SpatWJointLaw
import Parking.Support.LinHatMeasurable
import Parking.Support.NearestEvents
import Parking.Generic.Slutsky

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section
namespace Parking

variable {d : ℕ}

/-- **`signedPair`'s convergence in probability, relative to `scenePair`, conditional ONLY on
the value side's own convergence of the middle term.**  The martingale remainder's own
convergence (`hM` of `Parking.tendsto_signedPair_sub_scenePair_of_convergence`) is
UNCONDITIONAL (`Parking.tendsto_signedM_zero`), so this theorem drops it: the ONLY hypothesis
left is `hMiddle`, the value side's `Ū_R(1,·) → 𝒰(1,·)` convergence packaged through the
Taylor expansion of `(P-I)φ_R`. -/
theorem tendsto_signedPair_sub_scenePair_sub_middle_zero (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : Parking.External.SandpileGrowth) (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration) (hGreenNorms : Parking.External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν) {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ)
    (L : Data d → ℝ)
    (hMiddle : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun R : ℝ => ((law d ν) {w | ε < |signedMiddle w R φ - L w|}).toReal) atTop
        (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun R : ℝ =>
        ((law d ν) {w | ε < |signedPair w R φ - scenePair w R φ - L w|}).toReal) atTop
      (𝓝 0) :=
  tendsto_signedPair_sub_scenePair_of_convergence hd ν hν hφ L
    (tendsto_signedM_zero hd hd3 hGrowth hBernstein hConcentration hGreenNorms ν hν hφ) hMiddle

/-- **The three-block scenery export**: the joint convergence in law, tested
against every bounded continuous `G`, of
`((scenePair(φ_i))_i, (linHatInterp(sp_j))_j, (signedPair(χ_l) - scenePair(χ_l) - L l)_l)` to
`((√v·W(φ_i))_i, (Z(sp_j))_j, 0)`, `v := variance (fun k:ℤ=>(k:ℝ)) ν`.  `L l` is the value
side's own limit of `signedMiddle(χ l)` (`hMiddle`, per `l`, in `(law d ν)`-probability); `hLmeas`
is the ONE extra bookkeeping hypothesis this export needs beyond what
`tendsto_signedPair_sub_scenePair_sub_middle_zero` already asks for: genuine measurability of
`L l`, needed because `MeasureTheory.TendstoInDistribution` (unlike a bare "measure of a tail
set" statement) bundles measurability of the whole limiting random vector as part of its own
definition; in the intended application `L` is built from the value side's own `Uc`, which is
measurable (indeed continuous), so this is not a real restriction.  The final assembly applies
this statement at the concatenation of the test functions and points that the `Uc`-side
construction needs, matching `L l` to the continuum limit
`ω' ↦ ∫ x, Uc ω' 1 x * contOp d (χ l) x`.  That identification is not assumed here: `L` is left
abstract, exactly as in `tendsto_signedPair_sub_scenePair_of_convergence`. -/
theorem tendsto_scenePair_linHatInterp_joint_fdd_signedResidual
    (d p m q : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : Parking.External.SandpileGrowth) (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration) (hGreenNorms : Parking.External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν) (hLin : Parking.External.LinearFieldScaling)
    (φ : Fin m → (Fin d → ℝ) → ℝ) (hφ : ∀ i, IsTestFun (φ i))
    (sp : Fin p → ℝ × (Fin d → ℝ)) (hsp : ∀ j, 0 < (sp j).1)
    (χ : Fin q → (Fin d → ℝ) → ℝ) (hχ : ∀ l, IsTestFun (χ l))
    (L : Fin q → Data d → ℝ) (hLmeas : ∀ l, Measurable (L l))
    (hMiddle : ∀ l, ∀ ε : ℝ, 0 < ε →
      Tendsto (fun R : ℝ =>
          ((law d ν) {w | ε < |signedMiddle w R (χ l) - L l w|}).toReal) atTop (𝓝 0)) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q' : Measure Ω') (_ : IsProbabilityMeasure Q')
      (W : ((Fin d → ℝ) → ℝ) → Ω' → ℝ) (Z : Ω' → ℝ → (Fin d → ℝ) → ℝ),
      Parking.IsSpatialWhiteNoise d 1 Q' W ∧
      (∀ ω' t x, 0 ≤ t → Z ω' t x
          = Real.sqrt (variance (fun k : ℤ => (k : ℝ)) ν) *
            W (fun y => Parking.External.contFiniteGreen d t x y) ω') ∧
      ∀ G : BoundedContinuousFunction (((Fin m → ℝ) × (Fin p → ℝ)) × (Fin q → ℝ)) ℝ,
        Tendsto (fun R : ℝ =>
            ∫ w : Data d, G ((fun i => scenePair w R (φ i),
                  fun j => linHatInterp (fun y => (w.1 y : ℝ)) R (sp j)),
                fun l => signedPair w R (χ l) - scenePair w R (χ l) - L l w) ∂(law d ν))
          atTop
          (𝓝 (∫ ω', G ((fun i => Real.sqrt (variance (fun k : ℤ => (k : ℝ)) ν) * W (φ i) ω',
                  fun j => Z ω' (sp j).1 (sp j).2), (0 : Fin q → ℝ)) ∂Q')) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  obtain ⟨Ω', mΩ', Q', hQ', W, Z, hW, hpairEq, hWmeas, hZmeas, hconv⟩ :=
    tendsto_scenePair_linHatInterp_joint_fdd d p m hd hd3 ν hν hLin φ hφ sp hsp
  refine ⟨Ω', mΩ', Q', hQ', W, Z, hW, hpairEq, fun G => ?_⟩
  have hXm : ∀ R : ℝ, Measurable (fun w : Data d =>
      (fun i => scenePair w R (φ i), fun j => linHatInterp (fun y => (w.1 y : ℝ)) R (sp j))) :=
    fun R => Measurable.prodMk
      (measurable_pi_lambda _ fun i => measurable_scenePair_any_R R)
      (measurable_pi_lambda _ fun j => measurable_linHatInterp R (sp j))
  have hYm : ∀ R : ℝ, Measurable (fun w : Data d =>
      fun l : Fin q => signedPair w R (χ l) - scenePair w R (χ l) - L l w) :=
    fun R => measurable_pi_lambda _ fun l =>
      ((measurable_signedPair R (χ l)).sub (measurable_scenePair_any_R R)).sub (hLmeas l)
  have hZM : Measurable (fun ω' : Ω' =>
      (fun i => Real.sqrt (variance (fun k : ℤ => (k : ℝ)) ν) * W (φ i) ω',
        fun j => Z ω' (sp j).1 (sp j).2)) :=
    Measurable.prodMk
      (measurable_pi_lambda _ fun i => measurable_const.mul (hWmeas i))
      (measurable_pi_lambda _ fun j => hZmeas j)
  have hY : ∀ ε : ℝ, 0 < ε → Tendsto (fun R : ℝ =>
      ((law d ν) {w | ε < ‖(fun l : Fin q =>
          signedPair w R (χ l) - scenePair w R (χ l) - L l w)‖}).toReal) atTop (𝓝 0) :=
    Parking.Generic.Slutsky.tendsto_zero_pi_of_forall_tendsto_zero
      (fun l => tendsto_signedPair_sub_scenePair_sub_middle_zero hd hd3 hGrowth hBernstein
        hConcentration hGreenNorms ν hν (hχ l) (L l) (hMiddle l))
  exact Parking.Generic.Slutsky.tendsto_prodMk_of_tendsto_zero
    (fun R => (hXm R).aemeasurable) (fun R => (hYm R).aemeasurable) hZM.aemeasurable hconv hY G

end Parking

end
