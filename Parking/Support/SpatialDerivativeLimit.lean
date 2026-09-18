/- The smooth limit of positive time quotients is the continuum time derivative. -/
import Parking.External.HeatCompactness
import Parking.Generic.TimeDifferenceLimit
import Parking.Support.SpatialDifferenceQuotient
import Parking.Support.SpatialMeasurableDerivative

open MeasureTheory Filter Topology

noncomputable section
namespace Parking

/-- Interior compactness applies to the forward quotients: their local integral
bounds follow from telescoping, and their limit differentiates the same primitive. -/
theorem spatial_time_derivative_regular
    (hInterior : External.HeatInteriorRegularity) (hCompact : External.HeatCompactness)
    {d : ℕ} (hd : 1 ≤ d)
    (u : ℝ × (Fin d → ℝ) → ℝ) (W : ((Fin d → ℝ) → ℝ) → ℝ)
    (hu : Continuous u) (hzero : ∀ x, u (0, x) = 0)
    (hmono : ∀ x, Monotone fun s => u (s, x))
    (hpde : ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ → tsupport ψ ⊆ {p | 0 < u p} →
      -∫ p, u p * deriv (fun s => ψ (s, p.2)) p.1 =
        (∫ p, u p * contOp d (fun x => ψ (p.1, x)) p.2) + W (fun x => ∫ s : ℝ, ψ (s, x))) :
    ∃ v : ℝ × (Fin d → ℝ) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v {p | 0 < u p} ∧
      (∀ p, 0 < u p → HasDerivAt (fun s => u (s, p.2)) (v p) p.1) ∧
      (∀ p, 0 < u p → HasDerivAt (fun s => v (s, p.2))
        (contOp d (fun x => v (p.1, x)) p.2) p.1) := by
  let h : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hh : ∀ n, 0 < h n := fun n => by dsimp [h]; positivity
  have hh1 : ∀ n, h n ≤ 1 := fun n => by
    dsimp [h]
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  choose f hsmooth heq hnonneg hheat using fun n =>
    spatial_difference_quotient_regular hInterior u W hu hzero hmono hpde (hh n)
  have hbound : ∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → K ⊆ {p | 0 < u p} →
      ∃ C : ℝ, ∀ n, IntegrableOn (f n) K ∧ (∫ p in K, ‖f n p‖) ≤ C := by
    intro K hK hKO
    obtain ⟨C, hC⟩ := Generic.TimeDifference.exists_integral_norm_difference_bound hu hmono hK
    refine ⟨C, fun n => ?_⟩
    obtain ⟨hi, hb⟩ := hC (h n) (hh n) (hh1 n)
    have hae : (fun p => (u (p.1 + h n, p.2) - u p) / h n) =ᵐ[volume.restrict K] f n :=
      (ae_restrict_iff' hK.measurableSet).mpr
        (Filter.Eventually.of_forall (fun p hp => heq n p (hKO hp)))
    refine ⟨hi.congr hae, ?_⟩
    have hn := integral_congr_ae (hae.fun_comp norm)
    dsimp only [Function.comp_def] at hn
    rwa [← hn]
  obtain ⟨r, v, hr, hv, _, hheatv, hlim⟩ :=
    hCompact d hd {p | 0 < u p} (isOpen_lt continuous_const hu) f hsmooth hnonneg hheat hbound
  refine ⟨v, hv, ?_, hheatv⟩
  intro p hp
  have hstep : Tendsto (fun n => h (r n)) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat.comp hr.tendsto_atTop, ?_⟩
    exact Filter.Eventually.of_forall fun n => hh (r n)
  have hlimD : ∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → K ⊆ {p | 0 < u p} →
      TendstoUniformlyOn (fun n p => (u (p.1 + h (r n), p.2) - u p) / h (r n)) v atTop K := by
    intro K hK hKO
    apply (hlim K hK hKO).congr
    apply Filter.Eventually.of_forall
    intro n q hq
    exact (heq (r n) q (hKO hq)).symm
  exact Generic.TimeDifference.hasDerivAt_of_tendsto_difference
    (hu.comp (continuous_id.prodMk continuous_const))
    ((isOpen_lt continuous_const hu).preimage (continuous_id.prodMk continuous_const))
    hstep (Generic.TimeDifference.tendstoLocallyUniformlyOn_slice
      (isOpen_lt continuous_const hu) hlimD p.2) hp

/-- The continuum equation implies the complete measurable smooth positive
time-derivative clause, on the original probability space and with its original field. -/
theorem exists_spatial_derivative_of_pde
    (hInterior : External.HeatInteriorRegularity) (hMinimum : External.HeatStrongMinimum)
    (hCompact : External.HeatCompactness) {d : ℕ} (hd : 1 ≤ d)
    {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω)
    (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ) (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hUcmeas : ∀ s x, Measurable fun ω => Uc ω s x)
    (hUc0 : ∀ ω x, Uc ω 0 x = 0)
    (hUccont : ∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2)
    (hUcmono : ∀ ω x, Monotone fun s => Uc ω s x)
    (hpde : ∀ᵐ ω ∂Q, ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ →
      tsupport ψ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} →
      -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => ψ (s, p.2)) p.1
        = (∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * contOp d (fun x => ψ (p.1, x)) p.2)
          + W (fun x => ∫ s : ℝ, ψ (s, x)) ω) :
    ∃ v : Ω → ℝ → (Fin d → ℝ) → ℝ,
      (∀ s x, Measurable fun ω => v ω s x) ∧
      (∀ᵐ ω ∂Q, ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) => v ω p.1 p.2)
          {p | 0 < Uc ω p.1 p.2} ∧
        (∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ →
          tsupport ψ ⊆ {p | 0 < Uc ω p.1 p.2} →
          -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => ψ (s, p.2)) p.1
            = ∫ p : ℝ × (Fin d → ℝ), v ω p.1 p.2 * ψ p) ∧
        ∀ s x, 0 < Uc ω s x → 0 < v ω s x) := by
  apply exists_spatial_measurable_derivative hMinimum Q Uc hUcmeas hUc0 hUccont hUcmono
  filter_upwards [hpde] with ω hω
  exact spatial_time_derivative_regular hInterior hCompact hd (fun p => Uc ω p.1 p.2)
    (fun φ => W φ ω) (hUccont ω) (hUc0 ω) (hUcmono ω) hω

end Parking
