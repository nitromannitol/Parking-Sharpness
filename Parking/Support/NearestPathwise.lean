/-
The mollification identity of `parking.tex:1813-1814`: the continuum signed pair
of `thm:nearest` is positive at every nonnegative test function supported where
the limit field is positive.

The two distributional displays of `prop:spatial-scaling` share their left-hand
side `-∫∫ U ∂_s ψ`, so together they say

  `∫∫ U (Lψ) + ⟨W, ∫ ψ ds⟩ = ∫∫ v ψ`

for every space-time test function whose closed support lies in `{U > 0}`.
Testing this against `ψ_h(s,x) = ρ_h(s) φ(x)` with `ρ_h` a nonnegative kernel of
integral one supported in `[1, 1+h]` gives, at every `h`,

  `∫ ρ_h(s) F(s) ds + ⟨W, φ⟩ = ∫∫ v ψ_h`,   `F(s) = ∫ U(s,x) (Lφ)(x) dx`.

The left-hand side of the displays, which carries `ρ_h'` and is of size `h^{-2}`,
is never used.  On the right, `U` is nondecreasing in `s`, so the compact box
`[1,2] × tsupport φ` lies inside `{U > 0}`, where `v` is continuous and positive;
its minimum `c` there bounds `∫∫ v ψ_h ≥ c ∫ φ` uniformly in `h ≤ 1`.  Since `F`
is continuous at `1`, choosing `h` so that `|∫ ρ_h F - F(1)| ≤ c ∫φ / 2` gives
`⟨W,φ⟩ + F(1) ≥ c ∫φ / 2 > 0`, with no limit taken anywhere.
-/
import Parking.Support.ContOpRegularity
import Parking.Support.NearestMollifier

open MeasureTheory Filter Topology

noncomputable section

namespace Parking

variable {d : ℕ}

/-- A product `ρ(s) g(s,x) χ(x)` has compact support when `ρ` and `χ` do. -/
theorem hasCompactSupport_slab {ρ : ℝ → ℝ} {g : ℝ × (Fin d → ℝ) → ℝ}
    {χ : (Fin d → ℝ) → ℝ} (hρ : HasCompactSupport ρ) (hχ : HasCompactSupport χ) :
    HasCompactSupport (fun p : ℝ × (Fin d → ℝ) => ρ p.1 * (g p * χ p.2)) := by
  refine HasCompactSupport.intro (hρ.prod hχ) fun p hp => ?_
  rw [Set.mem_prod] at hp
  rcases not_and_or.1 hp with h | h
  · rw [image_eq_zero_of_notMem_tsupport h]; ring
  · rw [image_eq_zero_of_notMem_tsupport h]; ring

/-- A function continuous only on an open set becomes continuous after
multiplication by a test function whose closed support lies in that set. -/
theorem continuous_mul_of_continuousOn {X : Type*} [TopologicalSpace X]
    {v ψ : X → ℝ} {O : Set X} (hO : IsOpen O) (hv : ContinuousOn v O)
    (hψ : Continuous ψ) (hsub : tsupport ψ ⊆ O) :
    Continuous (fun p => v p * ψ p) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p ∈ tsupport ψ
  · exact (hv.continuousAt (hO.mem_nhds (hsub hp))).mul hψ.continuousAt
  · have h1 : (fun q => v q * ψ q) =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hp] with q hq
      rw [image_eq_zero_of_notMem_tsupport hq, mul_zero]
    exact ContinuousAt.congr continuousAt_const h1.symm

/-- The integral `∫ U(s,x) (Lφ)(x) dx` is continuous in the time variable. -/
theorem continuousAt_potentialPairing {Uc : ℝ → (Fin d → ℝ) → ℝ}
    (hct : Continuous fun p : ℝ × (Fin d → ℝ) => Uc p.1 p.2)
    {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) (s₀ : ℝ) :
    ContinuousAt (fun s => ∫ x, Uc s x * contOp d φ x) s₀ := by
  set χ := contOp d φ with hχdef
  have hχc : Continuous χ := continuous_contOp hφ
  have hχs : HasCompactSupport χ := hasCompactSupport_contOp hφ
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ p ∈ Set.Icc (s₀ - 1) (s₀ + 1) ×ˢ tsupport χ,
      ‖Uc p.1 p.2‖ ≤ C :=
    (isCompact_Icc.prod hχs).exists_bound_of_continuousOn hct.continuousOn
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  refine continuousAt_of_dominated (bound := fun x => C' * ‖χ x‖) ?_ ?_ ?_ ?_
  · filter_upwards with s using
      ((hct.comp (continuous_const.prodMk continuous_id)).mul hχc).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds s₀ one_pos] with s hs
    filter_upwards with x
    rw [norm_mul]
    by_cases hx : x ∈ tsupport χ
    · have hsi : s ∈ Set.Icc (s₀ - 1) (s₀ + 1) := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
        constructor <;> linarith [hs.1, hs.2]
      exact mul_le_mul_of_nonneg_right
        ((hC (s, x) ⟨hsi, hx⟩).trans (le_max_left _ _)) (norm_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  · exact (hχc.norm.const_mul C').integrable_of_hasCompactSupport hχs.norm.mul_left
  · filter_upwards with x
    exact ((hct.comp (continuous_id.prodMk continuous_const)).mul continuous_const).continuousAt


/-- The mass of a nonnegative test function normalised at the origin is positive. -/
theorem integral_pos_of_testFun {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ)
    (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : φ 0 = 1) : 0 < ∫ x, φ x := by
  have hφi : Integrable φ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2
  rw [integral_pos_iff_support_of_nonneg (fun x => hφ0 x) hφi]
  have hopen : IsOpen (Function.support φ) :=
    isOpen_compl_singleton.preimage hφ.1.continuous
  refine hopen.measure_pos volume ⟨0, ?_⟩
  simp [Function.mem_support, hφ1]

/-- **The mollification identity of `parking.tex:1813-1814`.**  The continuum
signed pair is positive at every nonnegative test function normalised at the
origin whose closed support lies where the limit field is positive at time one. -/
theorem pathwise_signed_of_displays {Uc v : ℝ → (Fin d → ℝ) → ℝ}
    {Wf : ((Fin d → ℝ) → ℝ) → ℝ}
    (hct : Continuous fun p : ℝ × (Fin d → ℝ) => Uc p.1 p.2)
    (hmono : ∀ x, Monotone fun s => Uc s x)
    (hvc : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => v p.1 p.2)
      {p : ℝ × (Fin d → ℝ) | 0 < Uc p.1 p.2})
    (hvpos : ∀ s x, 0 < Uc s x → 0 < v s x)
    (heq : ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ →
      tsupport ψ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc p.1 p.2} →
      (∫ p : ℝ × (Fin d → ℝ), Uc p.1 p.2 * contOp d (fun x => ψ (p.1, x)) p.2)
        + Wf (fun x => ∫ s : ℝ, ψ (s, x))
        = ∫ p : ℝ × (Fin d → ℝ), v p.1 p.2 * ψ p)
    {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : φ 0 = 1)
    (hsupp : ∀ x ∈ tsupport φ, 0 < Uc 1 x) :
    0 < Wf φ + ∫ x, Uc 1 x * contOp d φ x := by
  classical
  set O : Set (ℝ × (Fin d → ℝ)) := {p : ℝ × (Fin d → ℝ) | 0 < Uc p.1 p.2} with hOdef
  have hOopen : IsOpen O := isOpen_lt continuous_const hct
  set χ : (Fin d → ℝ) → ℝ := contOp d φ with hχdef
  have hχc : Continuous χ := continuous_contOp hφ
  have hχs : HasCompactSupport χ := hasCompactSupport_contOp hφ
  set F : ℝ → ℝ := fun s => ∫ x, Uc s x * χ x with hFdef
  have hFcont : Continuous F :=
    continuous_iff_continuousAt.2 fun s => continuousAt_potentialPairing hct hφ s
  -- the compact box on which the limit field is positive
  have h0T : (0 : Fin d → ℝ) ∈ tsupport φ :=
    subset_closure (by simp [Function.mem_support, hφ1])
  set B : Set (ℝ × (Fin d → ℝ)) := Set.Icc (1 : ℝ) 2 ×ˢ tsupport φ with hBdef
  have hBc : IsCompact B := isCompact_Icc.prod hφ.2
  have hBO : B ⊆ O := by
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    exact lt_of_lt_of_le (hsupp x hx) (hmono x hs.1)
  have hBne : B.Nonempty := ⟨(1, 0), ⟨by norm_num, h0T⟩⟩
  obtain ⟨p₀, hp₀B, hp₀min⟩ := hBc.exists_isMinOn hBne (hvc.mono hBO)
  set c : ℝ := v p₀.1 p₀.2 with hcdef
  have hc : 0 < c := hvpos _ _ (hBO hp₀B)
  have hcle : ∀ p ∈ B, c ≤ v p.1 p.2 := fun p hp => hp₀min hp
  -- the mass of the test function
  set I : ℝ := ∫ x, φ x with hIdef
  have hI : 0 < I := integral_pos_of_testFun hφ hφ0 hφ1
  have hφi : Integrable φ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2
  -- the width of the mollifier
  have hεpos : 0 < c * I / 2 := by positivity
  obtain ⟨δ₀, hδ₀0, hδ₀⟩ := Metric.continuousAt_iff.1 hFcont.continuousAt (c * I / 2) hεpos
  set δ : ℝ := min (δ₀ / 2) 1 with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hFδ : ∀ s ∈ Set.Icc (1 : ℝ) (1 + δ), |F s - F 1| ≤ c * I / 2 := by
    intro s hs
    have : dist s 1 < δ₀ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]
      have : s - 1 ≤ δ := by linarith [hs.2]
      have hδle : δ ≤ δ₀ / 2 := min_le_left _ _
      linarith
    have := hδ₀ this
    rw [Real.dist_eq] at this
    exact this.le
  obtain ⟨ρ, hρsm, hρcs, hρnn, hρsupp, hρint⟩ := exists_timeMollifier hδ0
  have hρc : Continuous ρ := hρsm.continuous
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρcs
  set ψ : ℝ × (Fin d → ℝ) → ℝ := fun p => ρ p.1 * φ p.2 with hψdef
  have hψtest : IsSpaceTimeTest ψ :=
    isSpaceTimeTest_mul hρsm hρcs (fun s hs => lt_of_lt_of_le one_pos (hρsupp hs).1) hφ
  have hψsub : tsupport ψ ⊆ O := tsupport_mul_subset_pos hρsupp hmono hsupp
  have hψc : Continuous ψ := hψtest.1.continuous
  have hψcs : HasCompactSupport ψ := hψtest.2.1
  have hψnn : ∀ p, 0 ≤ ψ p := fun p => mul_nonneg (hρnn p.1) (hφ0 p.2)
  -- the space-time integrand of the first display is a slab
  have hslab : Integrable (fun p : ℝ × (Fin d → ℝ) => ρ p.1 * (Uc p.1 p.2 * χ p.2)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (hasCompactSupport_slab hρcs hχs)
    exact (hρc.comp continuous_fst).mul (hct.mul (hχc.comp continuous_snd))
  -- the first display, after Fubini
  have hFub : (∫ p : ℝ × (Fin d → ℝ), Uc p.1 p.2 * contOp d (fun x => ψ (p.1, x)) p.2)
      = ∫ s : ℝ, ρ s * F s := by
    have hpt : ∀ p : ℝ × (Fin d → ℝ),
        Uc p.1 p.2 * contOp d (fun x => ψ (p.1, x)) p.2
          = ρ p.1 * (Uc p.1 p.2 * χ p.2) := by
      intro p
      rw [show (fun x => ψ (p.1, x)) = fun x => ρ p.1 * φ x from rfl, contOp_const_mul]
      ring
    simp_rw [hpt]
    rw [MeasureTheory.Measure.volume_eq_prod ℝ (Fin d → ℝ)]
    rw [integral_prod _ (by rwa [MeasureTheory.Measure.volume_eq_prod ℝ (Fin d → ℝ)] at hslab)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    show (∫ y : Fin d → ℝ, ρ s * (Uc s y * χ y)) = ρ s * F s
    rw [integral_const_mul]
  -- the noise argument is the test function itself
  have hWarg : (fun x => ∫ s : ℝ, ψ (s, x)) = φ := by
    funext x
    show (∫ s : ℝ, ρ s * φ x) = φ x
    rw [integral_mul_const, hρint, one_mul]
  -- the second display is bounded below by the minimum of the density
  have hvint : Integrable (fun p : ℝ × (Fin d → ℝ) => v p.1 p.2 * ψ p) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.mul_left hψcs)
    exact continuous_mul_of_continuousOn hOopen hvc hψc hψsub
  have hψint : Integrable ψ := hψc.integrable_of_hasCompactSupport hψcs
  have hmass : (∫ p : ℝ × (Fin d → ℝ), ψ p) = I := by
    show (∫ p : ℝ × (Fin d → ℝ), ρ p.1 * φ p.2) = I
    rw [MeasureTheory.Measure.volume_eq_prod ℝ (Fin d → ℝ), integral_prod_mul, hρint, one_mul]
  have hlow : c * I ≤ ∫ p : ℝ × (Fin d → ℝ), v p.1 p.2 * ψ p := by
    have hle : ∀ p : ℝ × (Fin d → ℝ), c * ψ p ≤ v p.1 p.2 * ψ p := by
      intro p
      by_cases hp : ψ p = 0
      · rw [hp, mul_zero, mul_zero]
      · refine mul_le_mul_of_nonneg_right (hcle p ?_) (hψnn p)
        have hpt : p ∈ tsupport ρ ×ˢ tsupport φ :=
          tsupport_mul_prod_subset ρ φ (subset_closure hp)
        exact ⟨⟨(hρsupp hpt.1).1, le_trans (hρsupp hpt.1).2 (by linarith)⟩, hpt.2⟩
    have := integral_mono (hψint.const_mul c) hvint hle
    rwa [integral_const_mul, hmass] at this
  -- the kernel average of the time profile is close to its value at one
  have hρF : Integrable (fun s => ρ s * F s) := by
    refine Continuous.integrable_of_hasCompactSupport (hρc.mul hFcont) ?_
    exact HasCompactSupport.mul_right hρcs
  have hdiff : (∫ s : ℝ, ρ s * F s) - F 1 = ∫ s : ℝ, ρ s * (F s - F 1) := by
    have : (fun s => ρ s * (F s - F 1)) = fun s => ρ s * F s - ρ s * F 1 :=
      funext fun s => by ring
    rw [this, integral_sub hρF (hρi.mul_const _), integral_mul_const, hρint, one_mul]
  have hgi : Integrable (fun s => ρ s * (F s - F 1)) := by
    refine Continuous.integrable_of_hasCompactSupport
      (hρc.mul (hFcont.sub continuous_const)) ?_
    exact HasCompactSupport.mul_right hρcs
  have hclose : |(∫ s : ℝ, ρ s * F s) - F 1| ≤ c * I / 2 := by
    rw [hdiff]
    have hb : ∀ s, |ρ s * (F s - F 1)| ≤ ρ s * (c * I / 2) := by
      intro s
      by_cases hs : ρ s = 0
      · rw [hs, zero_mul, zero_mul, abs_zero]
      · have hsB : s ∈ Set.Icc (1 : ℝ) (1 + δ) := hρsupp (subset_closure hs)
        rw [abs_mul, abs_of_nonneg (hρnn s)]
        exact mul_le_mul_of_nonneg_left (hFδ s hsB) (hρnn s)
    calc |∫ s : ℝ, ρ s * (F s - F 1)|
        ≤ ∫ s : ℝ, |ρ s * (F s - F 1)| := by
          simpa [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (μ := (volume : Measure ℝ))
              (f := fun s => ρ s * (F s - F 1))
      _ ≤ ∫ s : ℝ, ρ s * (c * I / 2) :=
          integral_mono hgi.abs (hρi.mul_const _) hb
      _ = c * I / 2 := by rw [integral_mul_const, hρint, one_mul]
  have key := heq ψ hψtest hψsub
  rw [hFub, hWarg] at key
  have h1 : F 1 = ∫ x, Uc 1 x * contOp d φ x := rfl
  rw [abs_le] at hclose
  linarith [hclose.1, hclose.2, hlow, key]

end Parking

end
