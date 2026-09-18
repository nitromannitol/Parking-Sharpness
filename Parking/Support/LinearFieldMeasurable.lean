/-
**Instantiation of `Parking.Generic.FieldMeasurability` for the linear field `Z` of
`Parking.External.LinearFieldScaling`.**

`Parking.External.LinearFieldScaling`'s own clauses already give `Z` continuous paths
(`hZcont`, its own bound variable) and measurable point evaluations (its fifth conjunct,
`∀ r x, Measurable fun ω' => Z ω' r x`), so
`Parking.Generic.FieldMeasurability.measurable_cutoffBC_of_continuous_measurable` applies
directly and gives the cutoff field `ω' ↦ Parking.cutoffBC χ (fun p => Z ω' p.1 p.2) ...` as a
genuine measurable random element of `E := BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ`.
This is the measurability ingredient that
`Parking.Support.ExtendedMappingReal.tendsto_integral_comp_real_of_lipschitz` requires on the
continuum side.

No `External` is consumed or registered by this module: it is stated for arbitrary `Z`,
`hZcont`, `hZmeas` of the shape `LinearFieldScaling`'s existential supplies, so a caller who
has already destructured that existential applies it directly to its own witnesses.
-/
import Parking.Generic.FieldMeasurability
import Parking.External.LinearFieldScaling

noncomputable section

namespace Parking

/-- `Parking.cutoffBC` (`Parking/Support/LinInterp.lean`) and the generic module's own
`cutoffBC` are the SAME construction, `ofCompactSupport (fun p => χ p * f p) ...`: literally
definitionally equal. -/
theorem cutoffBC_eq_generic {d : ℕ} (χ f : ℝ × (Fin d → ℝ) → ℝ) (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (hf : Continuous f) :
    Parking.cutoffBC χ f hχ hχc hf
      = Parking.Generic.FieldMeasurability.cutoffBC χ f hχ hχc hf := rfl

/-- **The cutoff, rescaled linear field of `Parking.External.LinearFieldScaling` is a
measurable random element of `E := BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ`**, given
only the continuity and measurability clauses `LinearFieldScaling`'s own existential
supplies (`hZcont`, its fifth conjunct read as `hZmeas`). -/
theorem measurable_cutoffBC_linearField {d : ℕ} {Ω' : Type} [MeasurableSpace Ω']
    (Z : Ω' → ℝ → (Fin d → ℝ) → ℝ)
    (hZcont : ∀ ω', Continuous fun p : ℝ × (Fin d → ℝ) => Z ω' p.1 p.2)
    (hZmeas : ∀ r x, Measurable fun ω' => Z ω' r x)
    (χ : ℝ × (Fin d → ℝ) → ℝ) (hχ1 : Continuous χ) (hχ2 : HasCompactSupport χ)
    [MeasurableSpace (BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ)]
    [BorelSpace (BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ)] :
    Measurable (fun ω' => Parking.cutoffBC χ (fun p => Z ω' p.1 p.2) hχ1 hχ2 (hZcont ω')) := by
  have hmeasG := Parking.Generic.FieldMeasurability.measurable_cutoffBC_of_continuous_measurable
    (Z := fun ω' p => Z ω' p.1 p.2) hZcont (fun p => hZmeas p.1 p.2) χ hχ1 hχ2
  have heq : (fun ω' => Parking.cutoffBC χ (fun p => Z ω' p.1 p.2) hχ1 hχ2 (hZcont ω'))
      = (fun ω' =>
          Parking.Generic.FieldMeasurability.cutoffBC χ (fun p => Z ω' p.1 p.2) hχ1 hχ2
            (hZcont ω')) := by
    funext ω'
    exact cutoffBC_eq_generic χ (fun p => Z ω' p.1 p.2) hχ1 hχ2 (hZcont ω')
  rw [heq]
  exact hmeasG

end Parking

end
