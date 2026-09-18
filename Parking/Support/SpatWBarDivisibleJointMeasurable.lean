/-
Joint measurability of the rescaled divisible odometer `barDivisible w R t x`, in `(w, x)`
together, at a FIXED `R` and `t`.  This is needed for the pairing convergence of
`Parking/Support/SpatWPairingConvergence.lean`: the McShane-lifted functional
`Parking.Generic.BoundedFunctionalLift.liftPhiOn K (Phi0 K h F) (NiceOnK K) L0` must be shown
measurable IN `w` when composed with the (spatially non-continuous) field `fun x => barDivisible
w R t x`, matching the `hfΦm` hypothesis of `LatticeProb.tendsto_integral_of_fdd_of_equicontinuous'`.
`Parking.Generic.BoundedFunctionalLift.liftPhiOn_eq_of_nice`
(`Parking/Generic/BoundedFunctionalLift.lean`) identifies the lift with `Phi0 K h F` exactly at
`barDivisible w R t ·`, since it is `NiceOnK` (`Parking.niceOnK_barDivisible`,
`Parking/Support/SpatWDivisiblePairing.lean`); this reduces the measurability question to
`Measurable fun w => ∫ x in K, barDivisible w R t x * h x`, a Bochner integral depending
measurably on a parameter.

The route: `barDivisible w R t x = R^{d/2-2} * uOf w n (latticePoint R x)` for the fixed
`n := ⌊t * R^2⌋₊`, so JOINT measurability of `(w, x) ↦ barDivisible w R t x` on
`Data d × (Fin d → ℝ)` follows from `Parking.measurable_eval_var`
(`Parking/Support/Measurability.lean`: `Measurable fun a => f a (q a)` from a
measurable index map `q` and marginal measurability `∀ i, Measurable fun a => f a i`), applied at
the measurable index map `q (w, x) := latticePoint R x : Data d × (Fin d → ℝ) → Site d` and the
marginal family `f (w, x) y := uOf w n y` (measurable in `(w, x)` for each fixed `y`, since
`Parking.measurable_uOf n y` is measurable in `w` alone). This is EXACTLY the mechanism
`measurable_eval_var` was built for (evaluating a measurable family at a measurable
countable-valued index), just with the "index" playing the role usually played by a stopping
time. Once the field is jointly measurable, `MeasureTheory.StronglyMeasurable.integral_prod_right'`
(Mathlib, the measurability half of Fubini's theorem) gives the parametrized integral's
measurability directly.
-/
import Parking.Support.SpatWDivisiblePairing
import Parking.Support.Measurability

open MeasureTheory

noncomputable section
namespace Parking

variable {d : ℕ}

/-- **The rescaled divisible odometer, jointly measurable in `(w, x)` at fixed `R, t`.** -/
theorem measurable_uncurry_barDivisible (R t : ℝ) :
    Measurable (fun p : Data d × (Fin d → ℝ) => barDivisible p.1 R t p.2) := by
  set n : ℕ := ⌊t * R ^ 2⌋₊ with hn
  have hq : Measurable (fun p : Data d × (Fin d → ℝ) => latticePoint R p.2) :=
    (measurable_pi_lambda _ (fun i => Int.measurable_floor.comp
      (measurable_const.mul (measurable_pi_apply i)))).comp measurable_snd
  have hf : ∀ y : Site d, Measurable (fun p : Data d × (Fin d → ℝ) => uOf p.1 n y) :=
    fun y => (measurable_uOf n y).comp measurable_fst
  have hjoint : Measurable (fun p : Data d × (Fin d → ℝ) => uOf p.1 n (latticePoint R p.2)) :=
    measurable_eval_var (fun p : Data d × (Fin d → ℝ) => latticePoint R p.2) hq
      (fun p y => uOf p.1 n y) hf
  have heq : (fun p : Data d × (Fin d → ℝ) => barDivisible p.1 R t p.2)
      = fun p => R ^ ((d : ℝ) / 2 - 2) * uOf p.1 n (latticePoint R p.2) := by
    funext p
    rfl
  rw [heq]
  exact hjoint.const_mul _

/-- **The parametrized integral `w ↦ ∫ x in K, barDivisible w R t x * h x` is measurable**, for a
fixed `R`, `t`, a compact `K`, and a continuous `h`.  Fubini's measurability half applied to the
joint field above, restricted to `K` by an indicator. -/
theorem measurable_integral_barDivisible_mul (R t : ℝ) (K : Set (Fin d → ℝ)) (hK : IsCompact K)
    (h : (Fin d → ℝ) → ℝ) (hh : Continuous h) :
    Measurable (fun w : Data d => ∫ x in K, barDivisible w R t x * h x) := by
  set F : Data d × (Fin d → ℝ) → ℝ :=
    fun p => K.indicator (fun x => barDivisible p.1 R t x * h x) p.2 with hFdef
  have hFmeas : Measurable F := by
    have hjoint : Measurable (fun p : Data d × (Fin d → ℝ) => barDivisible p.1 R t p.2 * h p.2) :=
      (measurable_uncurry_barDivisible R t).mul (hh.measurable.comp measurable_snd)
    have hKmeas : MeasurableSet {p : Data d × (Fin d → ℝ) | p.2 ∈ K} :=
      hK.measurableSet.preimage measurable_snd
    have hind := hjoint.indicator hKmeas
    have hFeq : F = {p : Data d × (Fin d → ℝ) | p.2 ∈ K}.indicator
        (fun p => barDivisible p.1 R t p.2 * h p.2) := by
      funext p
      simp only [hFdef, Set.indicator, Set.mem_setOf_eq]
      rfl
    rw [hFeq]
    exact hind
  have hSM : StronglyMeasurable F := hFmeas.stronglyMeasurable
  have hint : StronglyMeasurable fun w : Data d => ∫ x, F (w, x) := hSM.integral_prod_right'
  have heq : (fun w : Data d => ∫ x, F (w, x))
      = fun w : Data d => ∫ x in K, barDivisible w R t x * h x := by
    funext w
    have : (fun x => F (w, x)) = K.indicator (fun x => barDivisible w R t x * h x) := rfl
    rw [this, integral_indicator hK.measurableSet]
  rw [heq] at hint
  exact hint.measurable

/-- **The parametrized integral `ω ↦ ∫ x in K, Uc ω t x * h x` is measurable**, for a limit field
`Uc` measurable in `ω` at each fixed point and continuous in space-time for each fixed `ω`
(exactly `Parking.External.SpatialOdometerScaling`'s own `hUcmeas`/`hUccont` clauses).  The
proof follows the Carathéodory-function route of `Parking.measurable_integral_potential`
(`Parking/Support/NearestFromSpatial.lean`) for the UNRESTRICTED integral, adapted to the
compact-set restriction `K` in the same way `measurable_integral_barDivisible_mul` restricts the
lattice-field version above. -/
theorem measurable_integral_Uc_mul {Ω : Type} [MeasurableSpace Ω] {Uc : Ω → ℝ → (Fin d → ℝ) → ℝ}
    (hUm : ∀ s x, Measurable fun ω => Uc ω s x)
    (hct : ∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2)
    (t : ℝ) (K : Set (Fin d → ℝ)) (hK : IsCompact K)
    (h : (Fin d → ℝ) → ℝ) (hh : Continuous h) :
    Measurable fun ω : Ω => ∫ x in K, Uc ω t x * h x := by
  have hjoint : Measurable (Function.uncurry fun (x : Fin d → ℝ) (ω : Ω) => Uc ω t x * h x) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun ω => ((hct ω).comp (continuous_const.prodMk continuous_id)).mul hh)
      (fun x => (hUm t x).mul_const _)
  have hswap : Measurable fun p : Ω × (Fin d → ℝ) => Uc p.1 t p.2 * h p.2 :=
    hjoint.comp measurable_swap
  set F : Ω × (Fin d → ℝ) → ℝ := fun p => K.indicator (fun x => Uc p.1 t x * h x) p.2 with hFdef
  have hFmeas : Measurable F := by
    have hKmeas : MeasurableSet {p : Ω × (Fin d → ℝ) | p.2 ∈ K} :=
      hK.measurableSet.preimage measurable_snd
    have hind := hswap.indicator hKmeas
    have hFeq : F = {p : Ω × (Fin d → ℝ) | p.2 ∈ K}.indicator
        (fun p => Uc p.1 t p.2 * h p.2) := by
      funext p
      simp only [hFdef, Set.indicator, Set.mem_setOf_eq]
      rfl
    rw [hFeq]
    exact hind
  have hSM : StronglyMeasurable F := hFmeas.stronglyMeasurable
  have hint : StronglyMeasurable fun ω : Ω => ∫ x, F (ω, x) := hSM.integral_prod_right'
  have heq : (fun ω : Ω => ∫ x, F (ω, x)) = fun ω : Ω => ∫ x in K, Uc ω t x * h x := by
    funext ω
    have : (fun x => F (ω, x)) = K.indicator (fun x => Uc ω t x * h x) := rfl
    rw [this, integral_indicator hK.measurableSet]
  rw [heq] at hint
  exact hint.measurable

end Parking
end
