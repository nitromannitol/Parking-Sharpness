/- The directed particle odometer as a recursion on lower layers. -/
import Parking.Support.OrientedInstructionSupport
import Parking.Support.OrientedLayer
import Parking.Support.ErrorUnroll

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

theorem layerHeight_sub (x y : Site d) : layerHeight (x - y) = layerHeight x - layerHeight y := by
  simp only [layerHeight, Pi.sub_apply, sum_sub_distrib]

def orientedOdometer (η : Site d → ℤ) (σ : Site d × ℕ → Site d) : ℕ → Site d → ℕ
  | 0 => fun _ => 0
  | n + 1 => fun x => (η x + ∑ i : Fin d,
      (arrivals σ (x - unit i) x (orientedOdometer η σ n (x - unit i)) : ℤ)).toNat

theorem arrivals_eq_zero_of_forward {σ : Site d × ℕ → Site d}
    (hσ : ∀ q : Site d × ℕ, ∃ i : Fin d, σ q = q.1 + unit i)
    (y x : Site d) (m : ℕ) (hxy : ¬∃ i : Fin d, x = y + unit i) : arrivals σ y x m = 0 := by
  classical
  rw [arrivals, card_eq_zero, filter_eq_empty_iff]
  intro j _ hj
  obtain ⟨i, hi⟩ := hσ (y, j)
  exact hxy ⟨i, hj.symm.trans hi⟩

theorem sum_arrivals_oriented {σ : Site d × ℕ → Site d}
    (hσ : ∀ q : Site d × ℕ, ∃ i : Fin d, σ q = q.1 + unit i)
    (x : Site d) (v : Site d → ℕ) :
    (∑ y ∈ nbrFinset x, arrivals σ y x (v y)) =
      ∑ i : Fin d, arrivals σ (x - unit i) x (v (x - unit i)) := by
  have hz (i : Fin d) : arrivals σ (x + unit i) x (v (x + unit i)) = 0 := by
    apply arrivals_eq_zero_of_forward hσ
    rintro ⟨j, hj⟩
    have h := congrArg layerHeight hj
    simp only [layerHeight_add, layerHeight_unit] at h
    omega
  have h := sum_nbrFinset_eq x (fun y => (arrivals σ y x (v y) : ℝ))
  simp only [hz, Nat.cast_zero, zero_add] at h
  exact_mod_cast h

theorem orientedOdometer_eq_U (ω : Data d)
    (hσ : ∀ q : Site d × ℕ, ∃ i : Fin d, ω.2.1 q = q.1 + unit i) (n : ℕ) (x : Site d) :
    orientedOdometer ω.1 ω.2.1 n x = U ω n x := by
  have hnbr : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1 := by
    intro q
    obtain ⟨i, hi⟩ := hσ q
    rw [hi]
    exact mem_nbrFinset_add q.1 i
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have hpar := (parallel_of_labelOrder (D := toDriver ω) (labelOrder d) hnbr).2 n x
    have hsum : (∑ y ∈ nbrFinset x, (arrivals ω.2.1 y x (U ω n y) : ℤ)) =
        ∑ i : Fin d, (arrivals ω.2.1 (x - unit i) x (U ω n (x - unit i)) : ℤ) := by
      exact_mod_cast sum_arrivals_oriented hσ x (U ω n)
    change (U ω (n + 1) x : ℤ) = max 0 (ω.1 x + ∑ y ∈ nbrFinset x,
      (arrivals ω.2.1 y x (U ω n y) : ℤ)) at hpar
    rw [hsum] at hpar
    simp only [orientedOdometer, ih]
    have hmax (z : ℤ) : (max 0 z).toNat = z.toNat := by omega
    simpa only [Int.toNat_natCast, hmax]
      using (congrArg Int.toNat hpar).symm

theorem orientedOdometer_ae_eq_U (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (n : ℕ) (x : Site d) :
    (fun ω : Data d => orientedOdometer ω.1 ω.2.1 n x) =ᵐ[orientedLaw d ν] fun ω => U ω n x :=
  (orientedLaw_ae_forward hd ν).mono fun ω hω => orientedOdometer_eq_U ω hω n x

theorem orientedOdometer_lower_layers {η η' : Site d → ℤ} {σ σ' : Site d × ℕ → Site d}
    (n : ℕ) (x : Site d)
    (hη : ∀ y : Site d, layerHeight y ≤ layerHeight x → η y = η' y)
    (hσ : ∀ q : Site d × ℕ, layerHeight q.1 < layerHeight x → σ q = σ' q) :
    orientedOdometer η σ n x = orientedOdometer η' σ' n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [orientedOdometer, hη x le_rfl]
    congr 2
    apply sum_congr rfl
    intro i _
    have hh : layerHeight (x - unit i) = layerHeight x - 1 := by
      rw [layerHeight_sub, layerHeight_unit]
    have he := ih (x - unit i) (fun y hy => hη y (by rw [hh] at hy; omega))
      (fun q hq => hσ q (by rw [hh] at hq; omega))
    rw [he]
    apply congrArg (fun m : ℕ => (m : ℤ))
    unfold arrivals
    apply congrArg Finset.card
    apply filter_congr
    intro j _
    rw [hσ (x - unit i, j) (by change layerHeight (x - unit i) < layerHeight x; rw [hh]; omega)]

end Parking
