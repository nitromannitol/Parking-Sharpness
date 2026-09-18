import Parking.Support.IsolatedTransport
import Parking.Support.FiniteTransport
import Parking.Support.IndicatorIntegral

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
open scoped Classical
variable {d : ℕ}

theorem measure_isolated_le_good_add_activity (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] (t K : ℕ)
    (hiA : Integrable (fun ω : Data d => (A ω t 0 : ℝ)) (law d ν)) :
    ((law d ν) {ω | IsolatedHole ω t (2 * K) 0}).toReal ≤
      ((law d ν) {ω | IsolatedHole ω t (2 * K) 0 ∧ (activeSites ω t K 0).card ≤ 1}).toReal +
        (1 / 2 : ℝ) * ∫ ω, (A ω t 0 : ℝ) ∂(law d ν) := by
  haveI := stackRankLaw_isProbability hd
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  haveI : IsProbabilityMeasure (law d ν) :=
    inferInstanceAs (IsProbabilityMeasure ((iidLaw d ν).prod (stackRankLaw d)))
  let μ := law d ν
  let F := fun (ω : Data d) (y a : Site d) => (isolatedActiveMass ω t K y a : ℝ)
  have hiF : ∀ y a, Integrable (fun ω => F ω y a) μ := by
    intro y a
    apply integrable_of_le_nat (measurable_isolatedActiveMass t K y a) (integrable_const 1)
    intro ω
    exact_mod_cast isolatedActiveMass_le_one ω t K y a
  have htrans := integral_box_transport hd ν F K hiF (fun v ω y a => by
    dsimp only [F]
    rw [isolatedActiveMass_shift])
  have hiOut : Integrable (fun ω => ∑ a ∈ boxFinset 0 K, F ω 0 a) μ :=
    integrable_finsetSum _ (fun a _ => hiF 0 a)
  have hOut : (∫ ω, ∑ a ∈ boxFinset 0 K, F ω 0 a ∂μ) ≤ ∫ ω, (A ω t 0 : ℝ) ∂μ := by
    rw [← htrans]
    apply integral_mono (integrable_finsetSum _ (fun y _ => hiF y 0)) hiA
    intro ω
    have h := isolatedActiveMass_in ω t K
    have hc := (Nat.cast_le (α := ℝ)).mpr h
    simpa only [F, Nat.cast_sum] using hc
  let I := fun ω : Data d => if IsolatedHole ω t (2 * K) 0 then (1 : ℝ) else 0
  let G := fun ω : Data d => if IsolatedHole ω t (2 * K) 0 ∧ (activeSites ω t K 0).card ≤ 1 then (1 : ℝ) else 0
  have hmI := measurableSet_IsolatedHole (d := d) t (2 * K) 0
  have hmG : MeasurableSet {ω : Data d | IsolatedHole ω t (2 * K) 0 ∧ (activeSites ω t K 0).card ≤ 1} :=
    hmI.inter (measurableSet_le (measurable_activeSites_card t K 0) measurable_const)
  have hiI : Integrable I μ := integrable_ite_one_zero μ _ hmI
  have hiG : Integrable G μ := integrable_ite_one_zero μ _ hmG
  have hp : ∀ ω, I ω ≤ G ω + (1 / 2 : ℝ) * ∑ a ∈ boxFinset 0 K, F ω 0 a := by
    intro ω
    have hOutω : (∑ a ∈ boxFinset 0 K, F ω 0 a) =
        if IsolatedHole ω t (2 * K) 0 then ((activeSites ω t K 0).card : ℝ) else 0 := by
      have h := congrArg (fun n : ℕ => (n : ℝ)) (isolatedActiveMass_out ω t K)
      simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero] using h
    rw [hOutω]
    by_cases hI : IsolatedHole ω t (2 * K) 0
    · by_cases hC : (activeSites ω t K 0).card ≤ 1
      · simp only [I, G, hI, hC, and_self, if_true]
        have hn : 0 ≤ ((activeSites ω t K 0).card : ℝ) := Nat.cast_nonneg _
        linarith
      · have h2 : (2 : ℝ) ≤ (activeSites ω t K 0).card := by exact_mod_cast (show 2 ≤ (activeSites ω t K 0).card by omega)
        simp only [I, G, hI, hC, and_false, if_true, if_false]
        linarith
    · simp only [I, G, hI, false_and, if_false, mul_zero, add_zero, le_refl]
  have h := integral_mono hiI (hiG.add (hiOut.const_mul (1 / 2 : ℝ))) hp
  change (∫ ω, I ω ∂μ) ≤ ∫ ω, G ω + (1 / 2 : ℝ) * ∑ a ∈ boxFinset 0 K, F ω 0 a ∂μ at h
  rw [integral_add hiG (hiOut.const_mul (1 / 2 : ℝ)), integral_const_mul] at h
  have hI : (∫ ω, I ω ∂μ) = (μ {ω | IsolatedHole ω t (2 * K) 0}).toReal := integral_ite_one_zero μ _ hmI
  have hG : (∫ ω, G ω ∂μ) = (μ {ω | IsolatedHole ω t (2 * K) 0 ∧ (activeSites ω t K 0).card ≤ 1}).toReal := integral_ite_one_zero μ _ hmG
  rw [hI, hG] at h
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hOut (by norm_num)))

end Parking
