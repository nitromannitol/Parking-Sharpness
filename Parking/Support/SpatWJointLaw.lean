/-
The finite-dimensional form of the scenery-retained joint clause of
`Parking.External.LinearFieldScaling`: for finitely many test functions `φ_i` and finitely many
space-time points `sp_j` at positive times, the pair `(scenePair(φ_i)_i, linHatInterp(sp_j)_j)`
converges jointly in law to `((√v·W(φ_i))_i, Z(sp_j)_j)`, tested against every bounded continuous
`G` of the combined tuple.

This is a transcription of that clause, not new mathematics: it generalizes
`Parking.tendsto_linHatInterp_fdd` (`Parking/Support/SpatWLinFdd.lean`, the field-alone case) by
carrying the `scenePair` tuple through UNCHANGED.  The route is the same cutoff trick: choose one
fixed space-time test function `χ` (`Parking.exists_spaceTimeTest_
eqOn_finite`) equal to `1` at every target point `sp_j`; since `Parking.cutoffBC
χ f _ _ _ p = χ p * f p` (`Parking.cutoffBC_apply`), evaluating the cutoff field at a point
where `χ = 1` reads off the true field exactly, so composing the External's own `hjoint`
clause's bounded continuous `F` of `(scenePair-tuple, cutoffBC χ linHatInterp)` with "evaluate
the second coordinate at every `sp_j`" (`BoundedContinuousFunction.compContinuous`, via
`continuous_eval_const`, exactly as `tendsto_linHatInterp_fdd` does) instantiates
`hjoint` at precisely the finite-dimensional statement wanted; the `scenePair`-tuple coordinate
of `F` is untouched by this composition, so it passes through the whole computation unchanged.
-/
import Parking.Support.SpatWLinFdd

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section
namespace Parking

variable {d : ℕ}

/-- **The joint finite-dimensional convergence in law of the scenery pairings and the linear
field's point evaluations**: for test functions `φ_i` and space-time points `sp_j`, all at
positive times, `(scenePair(φ_i)_i, linHatInterp(sp_j)_j)` converges to
`((√v·W(φ_i))_i, Z(sp_j)_j)`, tested against every bounded continuous `G`.  Unconditional modulo
`Parking.External.LinearFieldScaling` (its scenery-retained joint clause), with no further
hypothesis.  Also exposes `W`'s and `Z`'s own measurability at a test function/point
(`Parking.External.LinearFieldScaling`'s own clauses, threaded through here rather than
re-derived), needed to assemble a `TendstoInDistribution` witness for the limit random vector
downstream (`Parking/Support/SpatWAssemblyExport.lean`). -/
theorem tendsto_scenePair_linHatInterp_joint_fdd (d p m : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℤ) (hν : CriticalLaw ν) (hLin : Parking.External.LinearFieldScaling)
    (φ : Fin m → (Fin d → ℝ) → ℝ) (hφ : ∀ i, IsTestFun (φ i))
    (sp : Fin p → ℝ × (Fin d → ℝ)) (hsp : ∀ j, 0 < (sp j).1) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q' : Measure Ω') (_ : IsProbabilityMeasure Q')
      (W : ((Fin d → ℝ) → ℝ) → Ω' → ℝ) (Z : Ω' → ℝ → (Fin d → ℝ) → ℝ),
      Parking.IsSpatialWhiteNoise d 1 Q' W ∧
      (∀ ω' t x, 0 ≤ t → Z ω' t x
          = Real.sqrt (variance (fun k : ℤ => (k : ℝ)) ν) *
            W (fun y => Parking.External.contFiniteGreen d t x y) ω') ∧
      (∀ i, Measurable (W (φ i))) ∧
      (∀ j, Measurable fun ω' => Z ω' (sp j).1 (sp j).2) ∧
      ∀ G : BoundedContinuousFunction ((Fin m → ℝ) × (Fin p → ℝ)) ℝ,
        Tendsto (fun R : ℝ =>
            ∫ w : Data d, G (fun i => scenePair w R (φ i),
                fun j => linHatInterp (fun y => (w.1 y : ℝ)) R (sp j)) ∂(law d ν))
          atTop
          (𝓝 (∫ ω', G (fun i => Real.sqrt (variance (fun k : ℤ => (k : ℝ)) ν) * W (φ i) ω',
                fun j => Z ω' (sp j).1 (sp j).2) ∂Q')) := by
  obtain ⟨χ, hχ, hχeq⟩ := exists_spaceTimeTest_eqOn_finite d p sp hsp
  obtain ⟨Ω', mΩ', Q', hQ', W, Z, hZcont, hW, hWmeas, hpair, hZ0, hZmeas, hZcov, hFconv,
    _hcross, hjoint⟩ := hLin d hd hd3 ν hν
  refine ⟨Ω', mΩ', Q', hQ', W, Z, hW, hpair, fun i => hWmeas (φ i) (hφ i),
    fun j => hZmeas (sp j).1 (sp j).2, fun G => ?_⟩
  have hcont1 : Continuous
      (fun q : (Fin m → ℝ) × BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ =>
        (q.1, fun j => q.2 (sp j))) :=
    continuous_fst.prodMk
      (continuous_pi fun j => (continuous_eval_const (sp j)).comp continuous_snd)
  set F : BoundedContinuousFunction
      ((Fin m → ℝ) × BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ) ℝ :=
    G.compContinuous ⟨_, hcont1⟩ with hFdef
  have hFapp : ∀ (A : Fin m → ℝ) (B : BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ),
      F (A, B) = G (A, fun j => B (sp j)) := fun A B => rfl
  have hconv := hjoint m φ hφ χ hχ F
  have heq1 : (fun R : ℝ =>
        ∫ w : Data d, F (fun i => scenePair w R (φ i),
            Parking.cutoffBC χ (linHatInterp (fun y => (w.1 y : ℝ)) R)
              hχ.1.continuous hχ.2.1 (continuous_linHatInterp (fun y => (w.1 y : ℝ)) R))
          ∂(law d ν))
      = fun R : ℝ =>
        ∫ w : Data d, G (fun i => scenePair w R (φ i),
            fun j => linHatInterp (fun y => (w.1 y : ℝ)) R (sp j))
          ∂(law d ν) := by
    funext R
    congr 1
    funext w
    rw [hFapp]
    have hsnd : (fun j => (Parking.cutoffBC χ (linHatInterp (fun y => (w.1 y : ℝ)) R)
          hχ.1.continuous hχ.2.1 (continuous_linHatInterp (fun y => (w.1 y : ℝ)) R)) (sp j))
        = fun j : Fin p => linHatInterp (fun y => (w.1 y : ℝ)) R (sp j) := by
      funext j
      rw [cutoffBC_apply, hχeq j, one_mul]
    rw [hsnd]
  have heq2 : (∫ ω', F (fun i => Real.sqrt (variance (fun k : ℤ => (k : ℝ)) ν) * W (φ i) ω',
        Parking.cutoffBC χ (fun p => Z ω' p.1 p.2) hχ.1.continuous hχ.2.1 (hZcont ω')) ∂Q')
      = ∫ ω', G (fun i => Real.sqrt (variance (fun k : ℤ => (k : ℝ)) ν) * W (φ i) ω',
          fun j => Z ω' (sp j).1 (sp j).2) ∂Q' := by
    congr 1
    funext ω'
    rw [hFapp]
    have hsnd : (fun j => (Parking.cutoffBC χ (fun p => Z ω' p.1 p.2) hχ.1.continuous hχ.2.1
          (hZcont ω')) (sp j))
        = fun j : Fin p => Z ω' (sp j).1 (sp j).2 := by
      funext j
      rw [cutoffBC_apply, hχeq j, one_mul]
    rw [hsnd]
  rw [heq1, heq2] at hconv
  exact hconv

end Parking

end
