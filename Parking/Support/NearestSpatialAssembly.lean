/- The endgame of `parking.tex:1807-1833` assembled from the clauses of
`prop:spatial-scaling`.

The joint finite-dimensional clause is projected twice, once onto finitely many
values of the rescaled divisible odometer at time one and once onto the signed
pair.  The ball event comes from the net argument; the signed pair is read off
the same convergence by one clamp.  Together they give the positive test event
of `Parking.nearest_of_positive_test_events`.
-/
import Parking.Support.NearestBallEvent
import Parking.Support.NearestLimit

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset Filter Topology

variable {d : ℕ}

/-- The clamp as a bounded continuous function of one real variable. -/
def clampBcf (a η : ℝ) (hη : 0 < η) : BoundedContinuousFunction ℝ ℝ :=
  ⟨⟨clampAt a η, continuous_clampAt a η⟩, ⟨1, by
    intro x y
    have h1 := clampAt_nonneg a η x hη
    have h2 := clampAt_le_one a η x
    have h3 := clampAt_nonneg a η y hη
    have h4 := clampAt_le_one a η y
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith⟩⟩

theorem clampBcf_apply (a η : ℝ) (hη : 0 < η) (t : ℝ) : clampBcf a η hη t = clampAt a η t := rfl

/-- The finite-dimensional clause of `prop:spatial-scaling`, projected onto finitely many
values of the rescaled divisible odometer at time one. -/
theorem spatial_fdd_barDivisible (ν : Measure ℤ)
    {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω)
    (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ) (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hFDD : ∀ (m k p : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ) (χ : Fin p → (Fin d → ℝ) → ℝ)
        (sp : Fin k → ℝ × (Fin d → ℝ)),
      (∀ i, IsTestFun (φ i)) → (∀ l, IsTestFun (χ l)) → (∀ j, 0 < (sp j).1) →
      ∀ F : BoundedContinuousFunction
          ((Fin m → ℝ) × (Fin k → ℝ) × (Fin k → ℝ) × (Fin p → ℝ)) ℝ,
        Tendsto (fun R : ℝ => ∫ w, F (fun i => scenePair w R (φ i),
              fun j => barDivisible w R (sp j).1 (sp j).2,
              fun j => barOdometer w R (sp j).1 (sp j).2,
              fun l => signedPair w R (χ l)) ∂(law d ν)) atTop
          (𝓝 (∫ ω, F (fun i => W (φ i) ω,
              fun j => Uc ω (sp j).1 (sp j).2,
              fun j => Uc ω (sp j).1 (sp j).2,
              fun l => W (χ l) ω
                + ∫ x, Uc ω 1 x * contOp d (χ l) x) ∂Q))) :
    ∀ (k : ℕ) (pts : Fin k → (Fin d → ℝ)),
      ∀ F : BoundedContinuousFunction (Fin k → ℝ) ℝ,
        Tendsto (fun R : ℝ => ∫ w, F (fun j => barDivisible w R 1 (pts j)) ∂(law d ν))
          atTop (𝓝 (∫ ω, F (fun j => Uc ω 1 (pts j)) ∂Q)) := by
  intro k pts F
  exact hFDD 0 k 0 (fun _ => 0) (fun _ => 0) (fun j => (1, pts j))
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun _ => one_pos)
    (F.compContinuous ⟨fun z => z.2.1, by fun_prop⟩)

/-- The finite-dimensional clause of `prop:spatial-scaling`, projected onto the signed pair. -/
theorem spatial_fdd_signedPair (ν : Measure ℤ)
    {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω)
    (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ) (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hFDD : ∀ (m k p : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ) (χ : Fin p → (Fin d → ℝ) → ℝ)
        (sp : Fin k → ℝ × (Fin d → ℝ)),
      (∀ i, IsTestFun (φ i)) → (∀ l, IsTestFun (χ l)) → (∀ j, 0 < (sp j).1) →
      ∀ F : BoundedContinuousFunction
          ((Fin m → ℝ) × (Fin k → ℝ) × (Fin k → ℝ) × (Fin p → ℝ)) ℝ,
        Tendsto (fun R : ℝ => ∫ w, F (fun i => scenePair w R (φ i),
              fun j => barDivisible w R (sp j).1 (sp j).2,
              fun j => barOdometer w R (sp j).1 (sp j).2,
              fun l => signedPair w R (χ l)) ∂(law d ν)) atTop
          (𝓝 (∫ ω, F (fun i => W (φ i) ω,
              fun j => Uc ω (sp j).1 (sp j).2,
              fun j => Uc ω (sp j).1 (sp j).2,
              fun l => W (χ l) ω
                + ∫ x, Uc ω 1 x * contOp d (χ l) x) ∂Q))) :
    ∀ φ : (Fin d → ℝ) → ℝ, IsTestFun φ →
      ∀ F : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun R : ℝ => ∫ w, F (signedPair w R φ) ∂(law d ν)) atTop
          (𝓝 (∫ ω, F (W φ ω + ∫ x, Uc ω 1 x * contOp d φ x) ∂Q)) := by
  intro φ hφ F
  exact hFDD 0 0 1 (fun _ => 0) (fun _ => φ) (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) (fun _ => hφ) (fun i => Fin.elim0 i)
    (F.compContinuous ⟨fun z => z.2.2.2 0, by fun_prop⟩)

theorem integrable_clampBcf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {a η : ℝ} (hη : 0 < η) (X : Ω → ℝ) (hX : Measurable X) :
    Integrable (fun w => clampBcf a η hη (X w)) P := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (((clampBcf a η hη).continuous.measurable.comp hX)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  rw [clampBcf_apply, Real.norm_eq_abs, abs_of_nonneg (clampAt_nonneg a η _ hη)]
  exact clampAt_le_one a η _

/-- One clamp turns a lower bound on the continuum signed-pair limit into the eventual
positivity of the discrete signed pair. -/
theorem eventually_signedPair_pos (ν : Measure ℤ) [IsProbabilityMeasure (law d ν)]
    {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (S : Ω → ℝ) (hS : Measurable S) (φ : (Fin d → ℝ) → ℝ) {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hconv : ∀ F : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun R : ℝ => ∫ w, F (signedPair w R φ) ∂(law d ν)) atTop (𝓝 (∫ ω, F (S ω) ∂Q)))
    (hpos : 1 - ε ≤ (Q {ω | a ≤ S ω}).toReal) :
    ∀ᶠ R : ℝ in atTop, 1 - 2 * ε ≤ ((law d ν) {w | 0 < signedPair w R φ}).toReal := by
  have hη : (0 : ℝ) < a / 2 := by positivity
  have hQ : 1 - ε ≤ ∫ ω, clampBcf a (a / 2) hη (S ω) ∂Q := by
    refine le_trans hpos ?_
    exact measureReal_le_integral Q _ (integrable_clampBcf Q hη S hS)
      (fun ω => clampAt_nonneg a (a / 2) _ hη) _ (measurableSet_le measurable_const hS)
      (fun ω hω => le_of_eq (clampAt_eq_one hη hω).symm)
  have hdisc : ∀ᶠ R : ℝ in atTop, 1 - 2 * ε ≤
      ∫ w, clampBcf a (a / 2) hη (signedPair w R φ) ∂(law d ν) := by
    have hlt : 1 - 2 * ε < ∫ ω, clampBcf a (a / 2) hη (S ω) ∂Q := by linarith
    exact ((hconv (clampBcf a (a / 2) hη)).eventually
      (eventually_gt_nhds hlt)).mono fun R hR => hR.le
  filter_upwards [hdisc] with R hR
  refine le_trans hR (integral_le_measureReal (law d ν) _
    (integrable_clampBcf (law d ν) hη (fun w => signedPair w R φ) (measurable_signedPair R φ))
    (fun w => clampAt_le_one a (a / 2) _) {w | 0 < signedPair w R φ}
    (measurableSet_lt measurable_const (measurable_signedPair R φ)) (fun w hw => ?_))
  have hle : signedPair w R φ ≤ a - a / 2 := by
    have h0 : ¬ (0 < signedPair w R φ) := hw
    have := not_lt.mp h0
    linarith
  exact clampAt_eq_zero hη hle

/-- **The endgame of `parking.tex:1818-1833`.**  The ball event and the positivity of the
signed pair give the positive test event, and with it the nearest theorem. -/
theorem nearest_of_ball_and_signed (hd : 1 ≤ d) (ν : Measure ℤ) (hprob : IsProbabilityMeasure ν)
    [IsProbabilityMeasure (law d ν)]
    (hEv : ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ ∃ φ : (Fin d → ℝ) → ℝ,
      (∀ x, 0 ≤ φ x) ∧ (∀ x, 0 < φ x → (∑ i, |x i|) ≤ r) ∧
      (∀ᶠ R : ℝ in atTop,
        1 - ε / 2 ≤ ((law d ν) {w | ∀ x ∈ ellOneBall d r, 0 < barOdometer w R 1 x}).toReal) ∧
      (∀ᶠ R : ℝ in atTop, 1 - ε / 2 ≤ ((law d ν) {w | 0 < signedPair w R φ}).toReal)) :
    Tendsto (fun t : ℕ => ((law d ν) {ω | HoleCloser ω t}).toReal) atTop (𝓝 0) := by
  refine nearest_of_positive_test_events hd ν hprob ?_
  intro ε hε
  obtain ⟨r, hr, φ, hφ0, hφsupp, hball, hsign⟩ := hEv ε hε
  refine ⟨r, hr, φ, hφ0, hφsupp, ?_⟩
  filter_upwards [hball, hsign, eventually_gt_atTop (0 : ℝ)] with R hb hs hR
  set A : Set (Data d) := {w | ∀ y : Site d, (graphNorm y : ℝ) ≤ r * R →
    0 < U w ⌊R ^ 2⌋₊ y} with hAdef
  set B : Set (Data d) := {w | 0 < signedPair w R φ} with hBdef
  have hAm : MeasurableSet A := measurableSet_positive_U_ball _ _
  have hBm : MeasurableSet B := measurableSet_lt measurable_const (measurable_signedPair R φ)
  have hAge : 1 - ε / 2 ≤ ((law d ν) A).toReal := by
    refine le_trans hb (measureReal_mono (μ := law d ν) ?_ (measure_ne_top _ _))
    exact fun w hw => U_pos_of_ball_barOdometer_pos w hR hw
  have hPTE : PositiveTestEvent R r φ = A ∩ B := rfl
  have hcompl : (law d ν).real (A ∩ B)ᶜ ≤ (law d ν).real Aᶜ + (law d ν).real Bᶜ := by
    rw [Set.compl_inter]
    exact measureReal_union_le _ _
  rw [probReal_compl_eq_one_sub hAm, probReal_compl_eq_one_sub hBm,
    probReal_compl_eq_one_sub (hAm.inter hBm)] at hcompl
  simp only [measureReal_def] at hcompl
  rw [hPTE]
  linarith

/-- **`thm:nearest` from the clauses of `prop:spatial-scaling` and ONE continuum statement.**
Everything of `parking.tex:1807-1833` is discharged here except the positivity of the continuum
signed pair, which is the paper's `∫ φ(x) v(1,x) dx > 2a` read through the continuum equation. -/
theorem nearest_of_spatial_data (hd : 1 ≤ d) (ν : Measure ℤ) (hprob : IsProbabilityMeasure ν)
    [IsProbabilityMeasure (law d ν)]
    {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ) (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hUm : ∀ s x, Measurable fun ω => Uc ω s x)
    (hct : ∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2)
    (hFDD : ∀ (m k p : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ) (χ : Fin p → (Fin d → ℝ) → ℝ)
        (sp : Fin k → ℝ × (Fin d → ℝ)),
      (∀ i, IsTestFun (φ i)) → (∀ l, IsTestFun (χ l)) → (∀ j, 0 < (sp j).1) →
      ∀ F : BoundedContinuousFunction
          ((Fin m → ℝ) × (Fin k → ℝ) × (Fin k → ℝ) × (Fin p → ℝ)) ℝ,
        Tendsto (fun R : ℝ => ∫ w, F (fun i => scenePair w R (φ i),
              fun j => barDivisible w R (sp j).1 (sp j).2,
              fun j => barOdometer w R (sp j).1 (sp j).2,
              fun l => signedPair w R (χ l)) ∂(law d ν)) atTop
          (𝓝 (∫ ω, F (fun i => W (φ i) ω,
              fun j => Uc ω (sp j).1 (sp j).2,
              fun j => Uc ω (sp j).1 (sp j).2,
              fun l => W (χ l) ω
                + ∫ x, Uc ω 1 x * contOp d (χ l) x) ∂Q)))
    (hclose : ∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → (∀ p ∈ K, 0 < p.1) → ∀ η : ℝ, 0 < η →
      Tendsto (fun R : ℝ => ((law d ν) {w | η < ⨆ p ∈ K,
          |barOdometer w R p.1 p.2 - barDivisible w R p.1 p.2|}).toReal) atTop (𝓝 0))
    (htight : ∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → (∀ p ∈ K, 0 < p.1) → ∀ η : ℝ, 0 < η →
      ∀ ε' : ℝ, 0 < ε' → ∃ δ : ℝ, 0 < δ ∧ ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
        ((law d ν) {w | η < ⨆ p ∈ K, ⨆ q ∈ K, ⨆ _ : dist p q ≤ δ,
            |barDivisible w R p.1 p.2 - barDivisible w R q.1 q.2|}).toReal ≤ ε')
    (hpos0 : ∀ᵐ ω ∂Q, 0 < Uc ω 1 0)
    (hSigned : ∀ r₀ : ℝ, 0 < r₀ → ∀ ε : ℝ, 0 < ε →
      ∃ (φ : (Fin d → ℝ) → ℝ) (a : ℝ), IsTestFun φ ∧ (∀ x, 0 ≤ φ x) ∧
        (∀ x, 0 < φ x → (∑ i, |x i|) ≤ r₀) ∧ 0 < a ∧
        Measurable (fun ω => W φ ω + ∫ x, Uc ω 1 x * contOp d φ x) ∧
        1 - ε ≤ (Q {ω | a ≤ W φ ω + ∫ x, Uc ω 1 x * contOp d φ x}).toReal) :
    Tendsto (fun t : ℕ => ((law d ν) {ω | HoleCloser ω t}).toReal) atTop (𝓝 0) := by
  refine nearest_of_ball_and_signed hd ν hprob ?_
  intro ε hε
  have hball := ae_exists_pos_l1_ball Q Uc hct hpos0
  obtain ⟨r, a, hr, ha, hlevel⟩ := exists_radius_level Q Uc
    (fun ω => (hct ω).comp (continuous_const.prodMk continuous_id)) hball
    (show (0 : ℝ) < ε / 8 by positivity)
  obtain ⟨φ, a₂, hφtest, hφ0, hφsupp, ha₂, hSm, hsig⟩ := hSigned r hr (ε / 4) (by positivity)
  refine ⟨r, hr, φ, hφ0, hφsupp, ?_, ?_⟩
  · have h := eventually_ball_barOdometer_pos hd ν Q Uc hUm ha
      (show (0 : ℝ) < ε / 8 by positivity)
      (spatial_fdd_barDivisible ν Q W Uc hFDD)
      (fun η hη => hclose (timeOneSlice d r) (isCompact_timeOneSlice d r) timeOneSlice_pos η hη)
      (fun η hη ε' hε' => htight (timeOneSlice d r) (isCompact_timeOneSlice d r)
        timeOneSlice_pos η hη ε' hε')
      hlevel
    exact h.mono fun R hR => by linarith
  · have h := eventually_signedPair_pos ν Q
      (fun ω => W φ ω + ∫ x, Uc ω 1 x * contOp d φ x) hSm φ ha₂
      (show (0 : ℝ) < ε / 4 by positivity)
      (spatial_fdd_signedPair ν Q W Uc hFDD φ hφtest) hsig
    exact h.mono fun R hR => by linarith

end Parking
end
