/- Time differentiation of tests cancels a time-independent source. -/
import Parking.Support.ContOpRegularity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open MeasureTheory

noncomputable section

namespace Parking

variable {d : ℕ}

/-- The partial derivative of a space-time function `ψ` in the TIME direction,
`∂_sψ`, written as the Fréchet derivative applied to the unit time vector `(1,0)`.
The spatial analogue, one axis at a time, is `Parking.partialDeriv`. -/
def timeDeriv (ψ : ℝ × (Fin d → ℝ) → ℝ) (p : ℝ × (Fin d → ℝ)) : ℝ :=
  fderiv ℝ ψ p (1, 0)

/-- `timeDeriv ψ` agrees with the ordinary one-variable derivative of every time
slice of `ψ`, exactly as `Parking.deriv_slice` does for a spatial axis. -/
theorem deriv_timeSlice {ψ : ℝ × (Fin d → ℝ) → ℝ} (hψ : Differentiable ℝ ψ)
    (x : Fin d → ℝ) (t : ℝ) :
    deriv (fun s => ψ (s, x)) t = timeDeriv ψ (t, x) := by
  have hd : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : Fin d → ℝ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact (((hψ (t, x)).hasFDerivAt).comp_hasDerivAt t hd).deriv

/-- `timeDeriv ψ` is smooth when `ψ` is. -/
theorem contDiff_timeDeriv {ψ : ℝ × (Fin d → ℝ) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (timeDeriv ψ) :=
  (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × (Fin d → ℝ))).contDiff.comp
    (hψ.fderiv_right (by simp))

/-- `timeDeriv ψ` has compact support when `ψ` does. -/
theorem hasCompactSupport_timeDeriv {ψ : ℝ × (Fin d → ℝ) → ℝ} (hψ : HasCompactSupport ψ) :
    HasCompactSupport (timeDeriv ψ) :=
  HasCompactSupport.fderiv_apply (𝕜 := ℝ) hψ (1, 0)

/-- The closed support of `timeDeriv ψ` sits inside that of `ψ`. -/
theorem tsupport_timeDeriv_subset (ψ : ℝ × (Fin d → ℝ) → ℝ) :
    tsupport (timeDeriv ψ) ⊆ tsupport ψ :=
  tsupport_fderiv_apply_subset ℝ (1, 0)

/-- **The time-derivative of a space-time test function is again a space-time test
function.** In particular its closed support only shrinks, so it is supported
wherever `ψ` is. -/
theorem isSpaceTimeTest_timeDeriv {ψ : ℝ × (Fin d → ℝ) → ℝ} (hψ : IsSpaceTimeTest ψ) :
    IsSpaceTimeTest (timeDeriv ψ) := by
  obtain ⟨hc, hs, hp⟩ := hψ
  exact ⟨contDiff_timeDeriv hc,
    hs.of_isClosed_subset (isClosed_tsupport _) (tsupport_timeDeriv_subset ψ),
    fun p hp' => hp p (tsupport_timeDeriv_subset ψ hp')⟩

/-- The integral over the whole line of the derivative of a `C¹`, compactly
supported real function is zero: it vanishes identically outside its (bounded)
support, so both half-line boundary terms of the fundamental theorem of calculus
are zero. -/
theorem integral_deriv_eq_zero_of_hasCompactSupport {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (h2f : HasCompactSupport f) : ∫ x, deriv f x = 0 := by
  have hInt : Integrable (deriv f) :=
    (hf.continuous_deriv le_rfl).integrable_of_hasCompactSupport h2f.deriv
  have h1 := HasCompactSupport.integral_Iic_deriv_eq hf h2f 0
  have h2 := HasCompactSupport.integral_Ioi_deriv_eq hf h2f 0
  have hsplit := MeasureTheory.integral_add_compl (measurableSet_Iic (a := (0 : ℝ))) hInt
  rw [Set.compl_Iic, h1, h2] at hsplit
  linarith [hsplit]

/-- The time slice `s ↦ φ (s, x)` of a compactly supported space-time function has
compact support: its support lies inside the (compact) image of `tsupport φ` under
the time projection. -/
theorem hasCompactSupport_timeSlice {φ : ℝ × (Fin d → ℝ) → ℝ} (hφ : HasCompactSupport φ)
    (x : Fin d → ℝ) : HasCompactSupport (fun s => φ (s, x)) := by
  have hsub : tsupport (fun s => φ (s, x)) ⊆ Prod.fst '' tsupport φ := by
    have h1 : Function.support (fun s => φ (s, x)) ⊆ Prod.fst '' Function.support φ :=
      fun s hs => ⟨(s, x), hs, rfl⟩
    calc tsupport (fun s => φ (s, x)) = closure (Function.support (fun s => φ (s, x))) := rfl
      _ ⊆ closure (Prod.fst '' Function.support φ) := closure_mono h1
      _ ⊆ closure (Prod.fst '' tsupport φ) := closure_mono (Set.image_mono subset_closure)
      _ = Prod.fst '' tsupport φ := IsClosed.closure_eq (hφ.image continuous_fst).isClosed
  exact IsCompact.of_isClosed_subset (hφ.image continuous_fst) isClosed_closure hsub

/-- The time slice `s ↦ φ (s, x)` of a smooth space-time function is smooth. -/
theorem contDiff_timeSlice {φ : ℝ × (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (x : Fin d → ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun s => φ (s, x)) :=
  hφ.comp (contDiff_id.prodMk contDiff_const)

/-- **The total time-integral of the time-derivative of a space-time test function
vanishes at every point `x`.**  This is the elementary fact behind the paper's
"the time-independent white noise cancels": in `Parking.IsSpatialWhiteNoise`, `W`
is tested against exactly this function of `x`, and it is identically zero. -/
theorem integral_timeDeriv_slice_eq_zero {φ : ℝ × (Fin d → ℝ) → ℝ} (hφ : IsSpaceTimeTest φ)
    (x : Fin d → ℝ) : ∫ s : ℝ, timeDeriv φ (s, x) = 0 := by
  have hdiff : Differentiable ℝ φ := hφ.1.differentiable (by simp)
  have hcongr : (fun s => timeDeriv φ (s, x)) = fun s => deriv (fun s' => φ (s', x)) s :=
    funext fun s => (deriv_timeSlice hdiff x s).symm
  rw [hcongr]
  exact integral_deriv_eq_zero_of_hasCompactSupport
    ((contDiff_timeSlice hφ.1 x).of_le (by exact_mod_cast le_top))
    (hasCompactSupport_timeSlice hφ.2.1 x)

/-- The zero function on `R^d` is a test function. -/
theorem isTestFun_zero : IsTestFun (fun _ : Fin d → ℝ => (0 : ℝ)) :=
  ⟨contDiff_const, by simp [HasCompactSupport, tsupport]⟩

/-- **A spatial white noise vanishes at the zero test function, everywhere (not
merely almost everywhere): linearity with `a = b = 0` forces `W 0 =ᵐ 0`, and the
left side does not depend on `ω`, so the null set is empty.** -/
theorem whiteNoise_apply_zero {Ω : Type} [MeasurableSpace Ω] {v : ℝ} {μ : Measure Ω}
    {W : ((Fin d → ℝ) → ℝ) → Ω → ℝ} (hW : IsSpatialWhiteNoise d v μ W) :
    ∀ᵐ ω ∂μ, W (fun _ => (0 : ℝ)) ω = 0 := by
  obtain ⟨hlin, _, _, _⟩ := hW
  have h0 := hlin (fun _ : Fin d → ℝ => (0 : ℝ)) (fun _ => (0 : ℝ)) isTestFun_zero isTestFun_zero 0 0
  filter_upwards [h0] with ω hω
  simpa using hω

variable {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω}
  {W : ((Fin d → ℝ) → ℝ) → Ω → ℝ} {Uc : Ω → ℝ → (Fin d → ℝ) → ℝ}

-- **The white noise cancels upon time-differentiation (paper Step 3, first
-- sentence), at a single `ω` where `hpde` and `W 0 = 0` both hold.**  Testing the
-- driven equation `hpdeω` against the time-derivative of any space-time test
-- function `φ` supported where `Uc ω` is positive leaves exactly the HOMOGENEOUS
-- identity `-∫Uc·∂_s(∂_sφ) = ∫Uc·L(∂_sφ)`: the source term `W (∫ (timeDeriv φ) ds)`
-- is `W` applied to the identically-zero function of `x`
-- (`Parking.integral_timeDeriv_slice_eq_zero`), which is `0` at this `ω`.
omit [MeasurableSpace Ω] in
theorem homogeneous_of_hpde {ω : Ω}
    (hpdeω : ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ →
        tsupport ψ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} →
        -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => ψ (s, p.2)) p.1
          = (∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * Parking.contOp d (fun x => ψ (p.1, x)) p.2)
            + W (fun x => ∫ s : ℝ, ψ (s, x)) ω)
    (hWzero : W (fun _ => (0 : ℝ)) ω = 0)
    {φ : ℝ × (Fin d → ℝ) → ℝ} (hφ : IsSpaceTimeTest φ)
    (hφsupp : tsupport φ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2}) :
    -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => timeDeriv φ (s, p.2)) p.1
      = ∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * Parking.contOp d (fun x => timeDeriv φ (p.1, x)) p.2 := by
  have hdφ : IsSpaceTimeTest (timeDeriv φ) := isSpaceTimeTest_timeDeriv hφ
  have hdφsupp : tsupport (timeDeriv φ) ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} :=
    (tsupport_timeDeriv_subset φ).trans hφsupp
  have key := hpdeω (timeDeriv φ) hdφ hdφsupp
  have hzero : (fun x => ∫ s : ℝ, timeDeriv φ (s, x)) = fun _ => (0 : ℝ) :=
    funext fun x => integral_timeDeriv_slice_eq_zero hφ x
  rwa [hzero, hWzero, add_zero] at key

/-- **The almost-sure form of `Parking.homogeneous_of_hpde`.**  Given the frozen
continuum equation `hpde` (`Parking.Frozen.spatial_scaling`'s own shape, exactly
as it will be discharged once the joint-convergence clauses are built) and the
white-noise hypothesis `hW` (`Parking.External.SpatialOdometerScaling`'s own
`hW`, for whatever intensity `v` it carries), for almost every `ω`, `Uc ω` solves
the HOMOGENEOUS heat equation weakly on `{Uc ω > 0}` against every test function
that is itself the time-derivative of another test function supported there.
-/
theorem homogeneous_ae_of_hpde {v : ℝ} (hW : IsSpatialWhiteNoise d v Q W)
    (hpde : ∀ᵐ ω ∂Q, ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ →
        tsupport ψ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} →
        -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => ψ (s, p.2)) p.1
          = (∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * Parking.contOp d (fun x => ψ (p.1, x)) p.2)
            + W (fun x => ∫ s : ℝ, ψ (s, x)) ω) :
    ∀ᵐ ω ∂Q, ∀ φ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest φ →
      tsupport φ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} →
      -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => timeDeriv φ (s, p.2)) p.1
        = ∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * Parking.contOp d (fun x => timeDeriv φ (p.1, x)) p.2 := by
  filter_upwards [hpde, whiteNoise_apply_zero hW] with ω hpdeω hWzero φ hφ hφsupp
  exact homogeneous_of_hpde hpdeω hWzero hφ hφsupp

end Parking

end
