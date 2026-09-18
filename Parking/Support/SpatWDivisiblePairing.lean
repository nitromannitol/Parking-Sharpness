/-
Building blocks for the pairing convergence of `barDivisible` against a fixed test function, the
piece needed to close the `signedPair` block of `prop:spatial-scaling`'s joint clause and the
continuum equation (`parking.tex:1740-1766`, Steps 1-2 of the proof).

The generic theorem that finite-dimensional convergence together with joint equicontinuity in
probability implies convergence of a bounded, sup-norm-uniformly-continuous functional is
`LatticeProb.tendsto_integral_of_fdd_of_equicontinuous'`, in the shared library module
`LatticeProb.Prob.FddTight`.  `Parking/Support/SpatialTightnessBridge.lean`
(`htight_of_spatial_tightness`) converts `prop:spatial-scaling`'s own space-time equicontinuity
clause into EXACTLY that theorem's `htight` hypothesis shape.  What this module supplies is the
bridge needed to APPLY the theorem to `barDivisible`, whose realizations are NOT continuous
(unlike the other uses of the theorem in this repository, which feed it a continuous field
obtained through an interpolation map such as `Parking.boxRewardMap`).

Applying `tendsto_integral_of_fdd_of_equicontinuous'` to a NON-continuous field needs its
functional `Φ : (E → ℝ) → ℝ` to be bounded and "uniformly continuous for the sup distance on `K`"
for EVERY function `E → ℝ`, continuous or not.  The functional needed here,
`Φ0 g := F (∫ x in K, g x * h x)` (`h` a fixed test function, `F` a fixed bounded Lipschitz real
function, so that the convergence identifies the limit `∫ Uc(·,t,·) * contOp(d)(φ)`), is bounded
and Lipschitz for the sup distance only between functions that are measurable and bounded on `K`
(`NiceOnK`): a wild non-measurable `g` makes the Bochner integral silently return the junk value
`0`, breaking any Lipschitz bound that ranges over ALL functions.
`Parking.Generic.BoundedFunctionalLift`, which mentions no object specific to this paper,
supplies the fix: a McShane-type Lipschitz extension of `Φ0` off `NiceOnK` to all of `E → ℝ`,
recovering `Φ0` exactly on `NiceOnK` inputs
(`Parking.Generic.BoundedFunctionalLift.liftPhiOn_eq_of_nice`).

This file proves that both `barDivisible w R t ·` and `Uc ω t ·` are `NiceOnK` on any compact ball
(`niceOnK_barDivisible`, using the deterministic bound `Parking.abs_barDivisible_le`;
`niceOnK_Uc`, using the external's own continuity of `Uc`), and that the candidate functional
`Phi0 K h F` is bounded everywhere (`abs_Phi0_le`, trivial: `F` absorbs everything) and Lipschitz
for the sup distance BETWEEN `NiceOnK` functions (`abs_Phi0_sub_le`, the real-analysis core of
the module: a Lebesgue dominated-convergence-style bound
`|Phi0 H - Phi0 G| ≤ (L_F · M_h · vol(K)) · sup_K|H - G|`, `L_F` `F`'s Lipschitz constant, `M_h` a
bound on `h` over `K`).

`abs_liftPhiOn_le`/`abs_liftPhiOn_sub_le`/`liftPhiOn_eq_of_nice`
(`Parking.Generic.BoundedFunctionalLift`) plus `abs_Phi0_le`/`abs_Phi0_sub_le` above supply
EXACTLY the `hΦb`/`hΦu` hypotheses of `tendsto_integral_of_fdd_of_equicontinuous'`, and the
recovery lemma identifies its `Φ` at the two realizations of interest with `Phi0`'s own value.
The other hypotheses of that theorem are supplied in
`Parking/Support/SpatWPairingConvergence.lean`:
(1) `hfdd`, by specializing `hOdometer`'s own `hjointFDD` field at the empty `φ`-tuple and the
tuple `sp j := (t, x j)`, converted from the "tested against every bounded continuous F" form to
a `TendstoInDistribution` structure via
`Parking.Generic.Slutsky.tendstoInDistribution_of_tendsto_integral`; (2) `htight`, by applying
`Parking.htight_of_spatial_tightness` at the SPACE-TIME compact set `{t} ×ˢ K` (the external's
own `hequicont`, read at the single time-slice `t`, gives exactly the needed bound, since
`dist (t, z) (t, y) = dist z y` on the product metric); (3) the assembly of
`tendsto_integral_of_fdd_of_equicontinuous'` itself with
`Φ := liftPhiOn K (Phi0 K h F) (NiceOnK K) (L0' + 2 * M_F)` for `L0' := LF * Mh * volume.real K`;
(4) the bootstrap from bounded LIPSCHITZ `F` to every bounded CONTINUOUS `F`, exactly as
`Parking.hlaw_orientedBoxReward` (`Parking/Support/TightHlawAssembly.lean`) does, via
`MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto` +
`MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`.  The result of (1)-(4) is
`TendstoInDistribution (fun R w => ∫ x in K, barDivisible w R t x * h x) atTop
  (fun ω => ∫ x in K, Uc ω t x * h x) (fun _ => law d ν) Q`, the "pairing convergence" that,
combined with a deterministic Taylor/Riemann-discretization bound relating `signedMiddle`
to this pairing, closes `hMiddle` and hence the `signedPair` block of `hjoint`; the SAME
technique one level up (space AND time) closes the continuum equation `hpde`.
-/
import Parking.Support.SpatialTightnessBridge
import Parking.Generic.BoundedFunctionalLift

open MeasureTheory Parking.Generic.BoundedFunctionalLift

noncomputable section
namespace Parking

variable {d : ℕ}

/-- `barDivisible w R s ·` is measurable in the SPATIAL variable, for fixed `w, R, s` (unlike
`Parking.measurable_barDivisible`, which is measurability in `w`): it factors through the
countable-discrete `Site d`, via the floor map `latticePoint R`. -/
theorem measurable_barDivisible_in_x (w : Data d) (R s : ℝ) :
    Measurable (fun x : Fin d → ℝ => barDivisible w R s x) := by
  unfold barDivisible
  apply Measurable.const_mul
  apply (Parking.measurable_from_countable' (uOf w ⌊s * R ^ 2⌋₊ : Site d → ℝ)).comp
  exact measurable_pi_lambda _ (fun i => Int.measurable_floor.comp
    (measurable_const.mul (measurable_pi_apply i)))

/-- `g` is bounded and (globally) measurable, restricted to `K`.  The "niceness" predicate the
McShane lift of `Parking.Generic.BoundedFunctionalLift` needs: `Phi0`'s Lipschitz bound
(`abs_Phi0_sub_le`) holds exactly between two `NiceOnK` functions. -/
def NiceOnK (K : Set (Fin d → ℝ)) (g : (Fin d → ℝ) → ℝ) : Prop :=
  Measurable g ∧ ∃ M : ℝ, ∀ x ∈ K, |g x| ≤ M

/-- **`NiceOnK` descends to a subset**: measurability is global, and a bound on a larger set
bounds it on any subset. Needed to transfer `niceOnK_barDivisible`/`niceOnK_Uc` (proved on a
closed ball containing an arbitrary compact `K`) down to `K` itself. -/
theorem niceOnK_mono {K K' : Set (Fin d → ℝ)} (hsub : K ⊆ K') {g : (Fin d → ℝ) → ℝ}
    (hg : NiceOnK K' g) : NiceOnK K g :=
  ⟨hg.1, hg.2.imp fun _ hM x hx => hM x (hsub hx)⟩

theorem norm_le_of_mem_closedBall {B : ℝ} {x : Fin d → ℝ}
    (hx : x ∈ Metric.closedBall (0 : Fin d → ℝ) B) (i : Fin d) : |x i| ≤ B := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx
  calc |x i| = ‖x i‖ := rfl
    _ ≤ ‖x‖ := norm_le_pi_norm x i
    _ ≤ B := hx

/-- **`barDivisible w R t ·` is `NiceOnK` on any closed ball**, from the deterministic bound
`Parking.abs_barDivisible_le`. -/
theorem niceOnK_barDivisible (hd : 1 ≤ d) (w : Data d) (R t B : ℝ) (hR : 0 ≤ R) (ht : 0 ≤ t) :
    NiceOnK (Metric.closedBall (0 : Fin d → ℝ) B) (fun x => barDivisible w R t x) := by
  refine ⟨measurable_barDivisible_in_x w R t, ?_⟩
  set C := max t B with hCdef
  have hC : 0 ≤ C := le_trans ht (le_max_left _ _)
  refine ⟨R ^ ((d : ℝ) / 2 - 2) * ((⌊C * R ^ 2⌋₊ : ℝ) *
      confBox w 0 ((⌈C * R⌉₊ + 1) + ⌊C * R ^ 2⌋₊)), ?_⟩
  intro x hx
  exact abs_barDivisible_le (p := (t, x)) hd w hR hC
    (by rw [abs_of_nonneg ht]; exact le_max_left t B)
    (fun i => le_trans (norm_le_of_mem_closedBall hx i) (le_max_right _ _))

/-- **`Uc ω t ·` is `NiceOnK` on any closed ball**, from the external's own joint continuity of
`Uc` (a continuous function on a compact set is bounded, via `IsCompact.exists_isMaxOn`). -/
theorem niceOnK_Uc {Ω : Type} (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ) (ω : Ω) (t B : ℝ) (hB : 0 ≤ B)
    (hUccont : Continuous fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2) :
    NiceOnK (Metric.closedBall (0 : Fin d → ℝ) B) (fun x => Uc ω t x) := by
  have hcont : Continuous (fun x : Fin d → ℝ => Uc ω t x) :=
    hUccont.comp (Continuous.prodMk continuous_const continuous_id)
  refine ⟨hcont.measurable, ?_⟩
  obtain ⟨x0, hx0mem, hx0max⟩ := (isCompact_closedBall (0 : Fin d → ℝ) B).exists_isMaxOn
    ⟨0, by simp [hB]⟩ hcont.abs.continuousOn
  exact ⟨|Uc ω t x0|, fun x hx => hx0max hx⟩

section Phi0

/-- The candidate functional: `F` applied to the pairing of `g` against a fixed test function
`h` over `K`.  `F ∘ (linear pairing)` is exactly the shape needed to identify, after
`tendsto_integral_of_fdd_of_equicontinuous'` and the recovery lemma, the convergence in
distribution of `∫_K barDivisible(·, R, t, ·) h` to `∫_K Uc(·, t, ·) h` (test `F` against every
bounded Lipschitz real function, matching `Parking.hlaw_orientedBoxReward`'s own bootstrap). -/
noncomputable def Phi0 (K : Set (Fin d → ℝ)) (h : (Fin d → ℝ) → ℝ) (F : ℝ → ℝ)
    (g : (Fin d → ℝ) → ℝ) : ℝ := F (∫ x in K, g x * h x)

/-- **`Phi0` is bounded everywhere**, trivially: `F` absorbs any input. -/
theorem abs_Phi0_le (K : Set (Fin d → ℝ)) (h : (Fin d → ℝ) → ℝ) {F : ℝ → ℝ} {M0 : ℝ}
    (hF : ∀ y, |F y| ≤ M0) (g : (Fin d → ℝ) → ℝ) :
    |Phi0 K h F g| ≤ M0 := hF _

/-- `h` is bounded on the compact `K`. -/
theorem exists_bound_h_on_K {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    {h : (Fin d → ℝ) → ℝ} (hh : Continuous h) :
    ∃ Mh : ℝ, 0 ≤ Mh ∧ ∀ x ∈ K, |h x| ≤ Mh := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨0, le_refl 0, fun x hx => absurd hx (by rw [hKe]; exact Set.notMem_empty x)⟩
  · obtain ⟨x0, hx0mem, hx0max⟩ := hK.exists_isMaxOn hKne hh.abs.continuousOn
    exact ⟨|h x0|, abs_nonneg _, fun x hx => hx0max hx⟩

theorem integrableOn_mul_of_niceOnK {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    {h : (Fin d → ℝ) → ℝ} (hh : Continuous h) {g : (Fin d → ℝ) → ℝ} (hg : NiceOnK K g) :
    IntegrableOn (fun x => g x * h x) K volume := by
  obtain ⟨hgm, M, hgb⟩ := hg
  obtain ⟨Mh, hMh0, hhb⟩ := exists_bound_h_on_K hK hh
  haveI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have hmeas : AEStronglyMeasurable (fun x => g x * h x) (volume.restrict K) :=
    (hgm.mul hh.measurable).aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  apply MeasureTheory.HasFiniteIntegral.mono' (g := fun _ => M * Mh)
  · exact (integrable_const (M * Mh)).2
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    calc ‖g x * h x‖ = |g x| * |h x| := by rw [Real.norm_eq_abs, abs_mul]
      _ ≤ M * Mh := mul_le_mul (hgb x hx) (hhb x hx) (abs_nonneg _)
          (le_trans (abs_nonneg _) (hgb x hx))

/-- **`Phi0` is Lipschitz for the sup distance BETWEEN `NiceOnK` functions.**  This is the
real-analysis core of the module: a dominated-convergence-style bound
`|Phi0 H - Phi0 G| ≤ (L_F · M_h · vol(K)) · sup_K|H - G|`, `L_F` a Lipschitz constant of `F`,
`M_h` a bound on `h` over `K`.  It is exactly the `hΦ0lip` hypothesis
`Parking.Generic.BoundedFunctionalLift.liftPhiOn_eq_of_nice` needs to identify the McShane lift
of `Phi0` with `Phi0` itself on `NiceOnK` inputs (in particular, on `barDivisible w R t ·` and
`Uc ω t ·`, both `NiceOnK` by the lemmas above). -/
theorem abs_Phi0_sub_le {K : Set (Fin d → ℝ)} (hK : IsCompact K) (hKne : K.Nonempty)
    {h : (Fin d → ℝ) → ℝ} (hh : Continuous h)
    {F : ℝ → ℝ} {LF : ℝ} (hFlip : ∀ y z, |F y - F z| ≤ LF * |y - z|)
    {Mh : ℝ} (_hMh0 : 0 ≤ Mh) (hhb : ∀ x ∈ K, |h x| ≤ Mh)
    {H G : (Fin d → ℝ) → ℝ} (hH : NiceOnK K H) (hG : NiceOnK K G) :
    |Phi0 K h F H - Phi0 K h F G| ≤
      (LF * Mh * volume.real K) * supDistOn K H G := by
  haveI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have hLF : 0 ≤ LF := by
    have h10 := hFlip 1 0
    norm_num at h10
    exact le_trans (abs_nonneg _) h10
  obtain ⟨hHm, MH, hHb⟩ := hH
  obtain ⟨hGm, MG, hGb⟩ := hG
  obtain ⟨x1, hx1⟩ := hKne
  have hMH0 : 0 ≤ MH := le_trans (abs_nonneg _) (hHb x1 hx1)
  have hMG0 : 0 ≤ MG := le_trans (abs_nonneg _) (hGb x1 hx1)
  have hIH : IntegrableOn (fun x => H x * h x) K volume :=
    integrableOn_mul_of_niceOnK hK hh ⟨hHm, MH, hHb⟩
  have hIG : IntegrableOn (fun x => G x * h x) K volume :=
    integrableOn_mul_of_niceOnK hK hh ⟨hGm, MG, hGb⟩
  have hstep1 :
      |Phi0 K h F H - Phi0 K h F G| ≤ LF * |(∫ x in K, H x * h x) - ∫ x in K, G x * h x| :=
    hFlip _ _
  have hsub : (∫ x in K, H x * h x) - ∫ x in K, G x * h x
      = ∫ x in K, (H x - G x) * h x := by
    rw [← integral_sub hIH hIG]
    congr 1; funext x; ring
  have habs : |(∫ x in K, H x * h x) - ∫ x in K, G x * h x| ≤ ∫ x in K, |(H x - G x) * h x| := by
    rw [hsub]; exact abs_integral_le_integral_abs
  have hpt : ∀ x ∈ K, |(H x - G x) * h x| ≤ (supDistOn K H G) * Mh := by
    intro x hx
    rw [abs_mul]
    refine mul_le_mul ?_ (hhb x hx) (abs_nonneg _) (supDistOn_nonneg K H G)
    exact le_supDistOn (M := MH + MG) (add_nonneg hMH0 hMG0)
      (fun p hp => (abs_sub (H p) (G p)).trans (by linarith [hHb p hp, hGb p hp])) hx
  have hIabsHG : IntegrableOn (fun x => |(H x - G x) * h x|) K volume := by
    have hmeas : AEStronglyMeasurable (fun x => |(H x - G x) * h x|) (volume.restrict K) :=
      ((hHm.sub hGm).mul hh.measurable).abs.aestronglyMeasurable
    refine ⟨hmeas, ?_⟩
    apply MeasureTheory.HasFiniteIntegral.mono' (g := fun _ => (MH + MG) * Mh)
    · exact (integrable_const ((MH + MG) * Mh)).2
    · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      have hHGx : |H x - G x| ≤ MH + MG :=
        (abs_sub (H x) (G x)).trans (by linarith [hHb x hx, hGb x hx])
      calc ‖|(H x - G x) * h x|‖ = |H x - G x| * |h x| := by
            rw [Real.norm_eq_abs, abs_abs, abs_mul]
        _ ≤ (MH + MG) * Mh := mul_le_mul hHGx (hhb x hx) (abs_nonneg _) (by linarith)
  have hconstbound : ∫ x in K, |(H x - G x) * h x| ≤ ∫ _x in K, (supDistOn K H G) * Mh :=
    setIntegral_mono_on hIabsHG (integrableOn_const hK.measure_lt_top.ne) hK.measurableSet hpt
  rw [setIntegral_const, smul_eq_mul] at hconstbound
  have hcomb : |(∫ x in K, H x * h x) - ∫ x in K, G x * h x|
      ≤ volume.real K * (supDistOn K H G * Mh) :=
    le_trans habs hconstbound
  calc |Phi0 K h F H - Phi0 K h F G|
      ≤ LF * |(∫ x in K, H x * h x) - ∫ x in K, G x * h x| := hstep1
    _ ≤ LF * (volume.real K * (supDistOn K H G * Mh)) :=
        mul_le_mul_of_nonneg_left hcomb hLF
    _ = (LF * Mh * volume.real K) * supDistOn K H G := by ring

end Phi0

end Parking
end
