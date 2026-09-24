/- A function unchanged by erasing a coordinate set is independent of that set. -/
import LatticeProb.Prob.Coordinate

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory LatticeProb
open scoped Classical

theorem indepFun_of_erasure_invariant {ι X E : Type*} [MeasurableSpace X] [MeasurableSpace E]
    (P : ι → Measure X) [∀ i, IsProbabilityMeasure (P i)] (S : Set ι) (c : ι → X)
    (F : (ι → X) → E) (hF : Measurable F)
    (hinv : ∀ ω, F (fun i => if i ∈ S then c i else ω i) = F ω) :
    IndepFun F (fun ω : ι → X => fun i : S => ω i) (Measure.infinitePi P) := by
  classical
  let m : ι → MeasurableSpace (ι → X) := fun i =>
    MeasurableSpace.comap (fun ω : ι → X => ω i) inferInstance
  have hcoord : iIndepFun (fun (i : ι) (ω : ι → X) => ω i) (Measure.infinitePi P) :=
    iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  have hind : iIndep m (Measure.infinitePi P) := (iIndepFun_iff_iIndep _ _ _).mp hcoord
  have hle : ∀ i, m i ≤ (inferInstance : MeasurableSpace (ι → X)) := fun i =>
    (measurable_pi_apply i).comap_le
  have hsplit := indep_biSup_compl hle hind Sᶜ
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le hsplit ?_ ?_
  · let erase : (ι → X) → ι → X := fun ω i => if i ∈ S then c i else ω i
    have herase : MeasurableSpace.comap erase inferInstance ≤ ⨆ i ∈ Sᶜ, m i := by
      apply comap_pi_le_of_coordinates
      intro i
      by_cases hi : i ∈ S
      · have he : (fun ω : ι → X => erase ω i) = fun _ => c i := by
          funext ω
          simp only [erase, if_pos hi]
        rw [he, MeasurableSpace.comap_const]
        exact bot_le
      · have he : (fun ω : ι → X => erase ω i) = fun ω => ω i := by
          funext ω
          simp only [erase, if_neg hi]
        rw [he]
        exact le_biSup m hi
    have hcomp : F ∘ erase = F := funext hinv
    calc MeasurableSpace.comap F inferInstance =
        MeasurableSpace.comap erase (MeasurableSpace.comap F inferInstance) := by
          rw [MeasurableSpace.comap_comp, hcomp]
      _ ≤ MeasurableSpace.comap erase inferInstance := MeasurableSpace.comap_mono hF.comap_le
      _ ≤ _ := herase
  · apply comap_pi_le_of_coordinates
    intro i
    exact le_biSup m (show i.val ∈ Sᶜᶜ by simpa only [compl_compl] using i.property)

end Parking
