/-
Finite-dimensional convergence in law of the linear field alone, the field-only part of the
joint law of the scenery coordinates with the linear field's coordinates
(`Parking.tendsto_scenePair_fdd` and `Parking.External.LinearFieldScaling`, with the white noise
`W` it exhibits).  This module extracts, mechanically and unconditionally, the classical
finite-dimensional convergence of the continuum field `Z` at finitely many space-time points (a
genuine `ℝ^p`-valued convergence in law, tested against every bounded continuous
`g : ℝ^p → ℝ`), from `LinearFieldScaling`'s own "locally uniform" clause (tested against a
cutoff field bundled as a `BoundedContinuousFunction`).

The route: choose a single fixed cutoff `χ` (`Parking.IsSpaceTimeTest`, so compactly
supported and supported in positive times) with `χ ≡ 1` on a neighbourhood of every one of
the finitely many target points, via `exists_spaceTimeTest_eqOn_finite` below (a space-time
bump built from a spatial bump, `Parking.exists_testFun_ellOne`-style, and a time bump,
`Parking.exists_timeMollifier`-style, centred to keep the whole support in positive time
regardless of how far apart the target times are).  Since `Parking.cutoffBC χ f _ _ _ p =
χ p * f p` (`Parking.ofCompactSupport`'s coercion, definitional), `χ ≡ 1` at the target
points makes evaluating the cutoff field there READ OFF THE UNCUT FIELD exactly.  Composing
the finitely many evaluations with a bounded continuous `g : ℝ^p → ℝ`
(`BoundedContinuousFunction.compContinuous`) packages "the discrete field, evaluated at the
`p` points, tested against `g`" as one instance of `LinearFieldScaling`'s own `F`.

No scenery enters this module.  In particular, it does not identify the resulting limit's white
noise `W` with `Parking.tendsto_scenePair_fdd`'s own canonical `contW`, and it does not use the
cross-covariance between a scenery test-function pairing and a field point evaluation, both of
which a GENUINE joint statement with `scenePair` requires.  BP's own Theorem 1.3 (page 5 of the
PDF) states `u^{(R)} ⟹ 𝒰` alone, with no scenery-joint clause; the cross term is `parking.tex`'s
OWN addition, attributed in its proof (`parking.tex:1741-1744`, Step 1) to "the argument proving
the parabolic scaling limit in [BP], with the time variable and scenery retained" — i.e. an
extension of BP's PROOF, not of BP's stated theorems.  It therefore enters only through the
scenery-retained joint clause of `Parking.External.LinearFieldScaling`, which
`Parking/Support/SpatWJointLaw.lean` uses to state the joint convergence with `scenePair`.
-/
import Parking.Support.NearestMollifier
import Parking.Support.NearestTestFun
import Parking.External.LinearFieldScaling

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section
namespace Parking

variable {d : ℕ}

/-! ### A spatial test function equal to `1` at finitely many prescribed points -/

/-- **A test function equal to `1` at every one of finitely many prescribed points.** -/
theorem exists_testFun_eqOn_finite (d p : ℕ) (pts : Fin p → (Fin d → ℝ)) :
    ∃ φ : (Fin d → ℝ) → ℝ, IsTestFun φ ∧ ∀ j, φ (pts j) = 1 := by
  classical
  rcases Nat.eq_zero_or_pos p with hp0 | hp0
  · subst hp0
    obtain ⟨φ, hφ, -⟩ := exists_testFun_ellOne d (by norm_num : (0 : ℝ) < 1)
    exact ⟨φ, hφ, fun j => j.elim0⟩
  · set j0 : Fin p := ⟨0, hp0⟩ with hj0
    set c : Fin d → ℝ := pts j0 with hc
    set R : ℝ := Finset.univ.sup' ⟨j0, Finset.mem_univ _⟩ (fun j => ‖pts j - c‖) with hRdef
    have hRnn : 0 ≤ R := by
      rw [hRdef]
      exact le_trans (norm_nonneg _) (Finset.le_sup' (fun j => ‖pts j - c‖) (Finset.mem_univ j0))
    let f : ContDiffBump c := ⟨R + 1, R + 2, by linarith, by linarith⟩
    refine ⟨fun x => f x, ⟨f.contDiff, f.hasCompactSupport⟩, fun j => ?_⟩
    have hle : ‖pts j - c‖ ≤ R := by
      rw [hRdef]; exact Finset.le_sup' (fun j => ‖pts j - c‖) (Finset.mem_univ j)
    have hmemball : pts j ∈ Metric.closedBall c f.rIn := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      show ‖pts j - c‖ ≤ R + 1
      linarith
    exact f.one_of_mem_closedBall hmemball

/-! ### A time bump equal to `1` at finitely many prescribed positive times -/

/-- **A smooth, compactly supported, positive-time-supported function equal to `1` at every
one of finitely many prescribed positive times.** -/
theorem exists_timeBump_eqOn_finite (p : ℕ) (times : Fin p → ℝ) (hpos : ∀ j, 0 < times j) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧ (∀ s ∈ tsupport ρ, 0 < s) ∧
      ∀ j, ρ (times j) = 1 := by
  classical
  rcases Nat.eq_zero_or_pos p with hp0 | hp0
  · subst hp0
    obtain ⟨ρ, hρ1, hρ2, -, hρ4, -⟩ := exists_timeMollifier (h := 1) one_pos
    exact ⟨ρ, hρ1, hρ2, fun s hs => lt_of_lt_of_le one_pos (hρ4 hs).1, fun j => j.elim0⟩
  · set j0 : Fin p := ⟨0, hp0⟩ with hj0
    set m : ℝ := Finset.univ.inf' ⟨j0, Finset.mem_univ _⟩ times with hmdef
    set M : ℝ := Finset.univ.sup' ⟨j0, Finset.mem_univ _⟩ times with hMdef
    have hm : 0 < m := by
      rw [hmdef]; exact (Finset.lt_inf'_iff _).mpr fun j _ => hpos j
    have hbound : ∀ j, m ≤ times j ∧ times j ≤ M := fun j =>
      ⟨by rw [hmdef]; exact Finset.inf'_le times (Finset.mem_univ j),
        by rw [hMdef]; exact Finset.le_sup' times (Finset.mem_univ j)⟩
    have hmM : m ≤ M := le_trans (hbound j0).1 (hbound j0).2
    set c : ℝ := (m + M) / 2 with hcdef
    set rIn : ℝ := (M - m) / 2 + m / 3 with hrIndef
    set rOut : ℝ := (M - m) / 2 + 2 * m / 3 with hrOutdef
    let f : ContDiffBump c := ⟨rIn, rOut, by rw [hrIndef]; linarith, by rw [hrIndef, hrOutdef]; linarith⟩
    have htsupp : tsupport (fun s => f s) = Metric.closedBall c f.rOut := f.tsupport_eq
    refine ⟨fun s => f s, f.contDiff, f.hasCompactSupport, fun s hs => ?_, fun j => ?_⟩
    · rw [htsupp] at hs
      have hs2 : s ∈ Metric.closedBall c rOut := hs
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hs2
      have hpos2 : (0 : ℝ) < c - rOut := by rw [hcdef, hrOutdef]; linarith
      linarith [hs2.1]
    · have hd1 : m ≤ times j := (hbound j).1
      have hd2 : times j ≤ M := (hbound j).2
      have hmemball : times j ∈ Metric.closedBall c f.rIn := by
        show times j ∈ Metric.closedBall c rIn
        rw [Metric.mem_closedBall, Real.dist_eq, abs_le, hcdef, hrIndef]
        constructor <;> linarith
      exact f.one_of_mem_closedBall hmemball

/-! ### A space-time test function equal to `1` at finitely many prescribed positive-time
points -/

/-- **A space-time test function equal to `1` at every one of finitely many prescribed
points, all at positive times.** -/
theorem exists_spaceTimeTest_eqOn_finite (d p : ℕ) (sp : Fin p → ℝ × (Fin d → ℝ))
    (hpos : ∀ j, 0 < (sp j).1) :
    ∃ χ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest χ ∧ ∀ j, χ (sp j) = 1 := by
  obtain ⟨ρ, hρ1, hρ2, hρ3, hρ4⟩ := exists_timeBump_eqOn_finite p (fun j => (sp j).1) hpos
  obtain ⟨φ, hφ, hφ4⟩ := exists_testFun_eqOn_finite d p (fun j => (sp j).2)
  refine ⟨fun p => ρ p.1 * φ p.2, isSpaceTimeTest_mul hρ1 hρ2 hρ3 hφ, fun j => ?_⟩
  show ρ (sp j).1 * φ (sp j).2 = 1
  rw [hρ4 j, hφ4 j, one_mul]

/-! ### `cutoffBC` reads off the uncut field where the cutoff is `1` -/

theorem cutoffBC_apply {χ f : ℝ × (Fin d → ℝ) → ℝ} (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (hf : Continuous f) (p : ℝ × (Fin d → ℝ)) :
    cutoffBC χ f hχ hχc hf p = χ p * f p := rfl

/-! ### The finite-dimensional convergence of the linear field's point evaluations -/

/-- **The classical finite-dimensional convergence in law of the discrete, interpolated,
rescaled linear field, at finitely many space-time points, all at positive times**, extracted
from `Parking.External.LinearFieldScaling`'s "locally uniform" clause via a single fixed
cutoff equal to `1` at every one of the target points (`exists_spaceTimeTest_eqOn_finite`).
This is the field-only half of the joint law; the joint statement with `Parking.scenePair`
needs, in addition, the cross-covariance between a scenery test-function pairing and a field
point evaluation, which comes from the scenery-retained joint clause of `LinearFieldScaling`
rather than from the clause used here (see the module docstring and
`Parking/Support/SpatWJointLaw.lean`). -/
theorem tendsto_linHatInterp_fdd (d p : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ)
    (hν : CriticalLaw ν) (hLin : Parking.External.LinearFieldScaling)
    (sp : Fin p → ℝ × (Fin d → ℝ)) (hsp : ∀ j, 0 < (sp j).1) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q' : Measure Ω') (_ : IsProbabilityMeasure Q')
      (W : ((Fin d → ℝ) → ℝ) → Ω' → ℝ) (Z : Ω' → ℝ → (Fin d → ℝ) → ℝ),
      Parking.IsSpatialWhiteNoise d 1 Q' W ∧
      (∀ ω' t x, 0 ≤ t → Z ω' t x
          = Real.sqrt (variance (fun k : ℤ => (k : ℝ)) ν) *
            W (fun y => Parking.External.contFiniteGreen d t x y) ω') ∧
      ∀ g : BoundedContinuousFunction (Fin p → ℝ) ℝ,
        Tendsto (fun R : ℝ =>
            ∫ w : Data d, g (fun j => linHatInterp (fun y => (w.1 y : ℝ)) R (sp j))
              ∂(law d ν))
          atTop
          (𝓝 (∫ ω', g (fun j => Z ω' (sp j).1 (sp j).2) ∂Q')) := by
  obtain ⟨χ, hχ, hχeq⟩ := exists_spaceTimeTest_eqOn_finite d p sp hsp
  obtain ⟨Ω', mΩ', Q', hQ', W, Z, hZcont, hW, hWmeas, hpair, hZ0, hZmeas, hZcov, hFconv,
    _hcross, _hjoint⟩ := hLin d hd hd3 ν hν
  refine ⟨Ω', mΩ', Q', hQ', W, Z, hW, hpair, fun g => ?_⟩
  have hcont1 : Continuous
      (fun v : BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ => fun j => v (sp j)) :=
    continuous_pi fun j => continuous_eval_const (sp j)
  set F : BoundedContinuousFunction (BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ) ℝ :=
    g.compContinuous ⟨_, hcont1⟩ with hFdef
  have hFapp : ∀ v : BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ,
      F v = g (fun j => v (sp j)) := fun v => rfl
  have hconv := hFconv χ hχ F
  have heq1 : (fun R : ℝ =>
        ∫ w : Data d, F (Parking.cutoffBC χ (linHatInterp (fun y => (w.1 y : ℝ)) R)
            hχ.1.continuous hχ.2.1 (continuous_linHatInterp (fun y => (w.1 y : ℝ)) R))
          ∂(law d ν))
      = fun R : ℝ =>
        ∫ w : Data d, g (fun j => linHatInterp (fun y => (w.1 y : ℝ)) R (sp j))
          ∂(law d ν) := by
    funext R
    congr 1
    funext w
    rw [hFapp]
    congr 1
    funext j
    rw [cutoffBC_apply, hχeq j, one_mul]
  have heq2 : (∫ ω', F (Parking.cutoffBC χ (fun p => Z ω' p.1 p.2) hχ.1.continuous hχ.2.1
        (hZcont ω')) ∂Q')
      = ∫ ω', g (fun j => Z ω' (sp j).1 (sp j).2) ∂Q' := by
    congr 1
    funext ω'
    rw [hFapp]
    congr 1
    funext j
    rw [cutoffBC_apply, hχeq j, one_mul]
  rw [heq1, heq2] at hconv
  exact hconv

end Parking

end
