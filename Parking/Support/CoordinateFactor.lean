import LatticeProb.Prob.Coordinate

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory LatticeProb

/-- A measurable function invariant under a coordinate update factors against any observable of that coordinate. -/
theorem integral_mul_coordinate_of_update_invariant {ι : Type*} {X : ι → Type*}
    [DecidableEq ι] [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] (q : ι) (b : X q)
    (F : (Π i, X i) → ℝ) (hF : Measurable F) (hiF : ∀ ω, F (Function.update ω q b) = F ω)
    (g : X q → ℝ) (hg : Measurable g) :
    ∫ ω, F ω * g (ω q) ∂(Measure.infinitePi μ) =
      (∫ ω, F ω ∂(Measure.infinitePi μ)) * ∫ a, g a ∂(μ q) := by
  have hind : IndepFun F (fun ω : Π i, X i => ω q) (Measure.infinitePi μ) :=
    indepFun_of_update_invariant μ b F hF hiF
  have hmap : (Measure.infinitePi μ).map (fun ω : Π i, X i => ω q) = μ q := Measure.infinitePi_map_eval _ q
  have hga : AEStronglyMeasurable g ((Measure.infinitePi μ).map (fun ω : Π i, X i => ω q)) := by
    rw [hmap]
    exact hg.aestronglyMeasurable
  have h := hind.integral_fun_comp_mul_comp (f := (id : ℝ → ℝ)) (g := g)
    hF.aemeasurable (measurable_pi_apply q).aemeasurable aestronglyMeasurable_id hga
  have he := integral_eval μ q g hg.aestronglyMeasurable
  simpa only [id_eq, he] using h
end Parking
