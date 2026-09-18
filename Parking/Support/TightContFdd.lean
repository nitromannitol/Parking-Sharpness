/-
The finite-dimensional characteristic function of the continuum noise field `Parking.contZ` at
finitely many box points, matched against the discrete limit of `TightFdd.lean`
(`parking.tex:3192-3203`, Stage 2 of the covariance-to-Gaussian step).

`Parking.contZ v T s x` is `√v` times the white-noise integral of `Parking.contNoiseTest T s
x`, so any finite linear combination `∑ t_l · contZ v T (u_l)` is `√v` times the white-noise
integral of the combined test function `∑ t_l · contNoiseTest T (u_l)`, which is a genuine
real-valued centred Gaussian by `LatticeProb.map_isoProc`.  Its variance is `v` times the
squared `L²` norm of the combined test function, which is exactly the same quadratic form of
`Parking.contOverlap` that `Parking.tendsto_charFun_orientedBoxReward_linearCombination`
computes for the discrete side (`LatticeProb.map_isoProc`'s Gaussian, at the standardized
variance `v = Var η(0)`), so the two characteristic-function limits agree termwise.
-/
import Parking.Support.TightFdd
import Parking.Support.ContOrientedLimit

open MeasureTheory LatticeProb ProbabilityTheory Filter Topology Finset

noncomputable section
namespace Parking

/-- **The white-noise integral of a square-integrable test function on the plane is a centred
Gaussian**, with variance its squared `L²` norm. This is the space-time analogue of
`Parking.map_whiteNoiseOf` (`ScalWhiteNoise.lean`, there for `Fin d → ℝ`), by the same
one-line argument from `LatticeProb.map_isoProc`. -/
theorem map_whiteNoiseOf_contNoise (φ : ℝ × ℝ → ℝ) :
    contNoiseLaw.map (LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) φ)
      = gaussianReal 0 (‖LatticeProb.toLpOrZero (volume : Measure (ℝ × ℝ)) φ‖ ^ 2).toNNReal := by
  rw [LatticeProb.whiteNoiseOf, contNoiseLaw, LatticeProb.whiteNoiseLaw, LatticeProb.whiteNoise]
  exact LatticeProb.map_isoProc (LatticeProb.l2HilbertBasis (volume : Measure (ℝ × ℝ)))
    (LatticeProb.toLpOrZero (volume : Measure (ℝ × ℝ)) φ)

/-- **The squared `L²` norm of the `L²` class of a square-integrable function on the plane is
the integral of its square.** The space-time analogue of `Parking.norm_toLpOrZero_sq`. -/
theorem norm_toLpOrZero_sq_contNoise (φ : ℝ × ℝ → ℝ) (hφ : MemLp φ 2 (volume : Measure (ℝ × ℝ))) :
    ‖LatticeProb.toLpOrZero (volume : Measure (ℝ × ℝ)) φ‖ ^ 2 = ∫ p : ℝ × ℝ, φ p ^ 2 := by
  rw [LatticeProb.toLpOrZero_of_memLp hφ, MeasureTheory.Lp.norm_toLp φ hφ,
    MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hφ]
  rw [ENNReal.toReal_ofReal (by positivity), ← Real.rpow_two, ← Real.rpow_mul (by positivity)]
  norm_num

/-- **Finite-sum linearity of the white-noise integral**: the white-noise integral of a finite
linear combination of test functions is almost everywhere the same combination of the
individual white-noise integrals. Proved by induction on the (finite) index. -/
theorem whiteNoiseOf_sum {ι : Type*} (S : Finset ι) (c : ι → ℝ) (φ : ι → ℝ × ℝ → ℝ)
    (hφ : ∀ i ∈ S, MemLp (φ i) 2 (volume : Measure (ℝ × ℝ))) :
    LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) (fun p => ∑ i ∈ S, c i * φ i p)
      =ᵐ[contNoiseLaw] fun ω => ∑ i ∈ S,
        c i * LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) (φ i) ω := by
  classical
  induction S using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      have hf : MemLp (fun _ : ℝ × ℝ => (0 : ℝ)) 2 (volume : Measure (ℝ × ℝ)) :=
        ⟨aestronglyMeasurable_zero, by rw [eLpNorm_zero']; exact ENNReal.zero_lt_top⟩
      have h := LatticeProb.whiteNoiseOf_smul (volume : Measure (ℝ × ℝ)) (0 : ℝ) hf
      simp only [zero_smul, zero_mul] at h
      filter_upwards [h] with ω hω
      exact hω
  | insert i S hiS ih =>
      have hmemS : ∀ j ∈ S, MemLp (φ j) 2 (volume : Measure (ℝ × ℝ)) := fun j hj =>
        hφ j (Finset.mem_insert_of_mem hj)
      have hmemi : MemLp (φ i) 2 (volume : Measure (ℝ × ℝ)) := hφ i (Finset.mem_insert_self i S)
      have hsumMem : MemLp (fun p => ∑ j ∈ S, c j * φ j p) 2 (volume : Measure (ℝ × ℝ)) :=
        memLp_finsetSum S fun j hj => (hmemS j hj).const_mul (c j)
      have hcongr : (fun p : ℝ × ℝ => ∑ j ∈ insert i S, c j * φ j p) =
          fun p => c i * φ i p + ∑ j ∈ S, c j * φ j p := by
        funext p
        rw [Finset.sum_insert hiS]
      rw [hcongr]
      have hciφ : MemLp (fun p => c i * φ i p) 2 (volume : Measure (ℝ × ℝ)) :=
        hmemi.const_mul (c i)
      filter_upwards [LatticeProb.whiteNoiseOf_add (volume : Measure (ℝ × ℝ)) hciφ hsumMem,
        LatticeProb.whiteNoiseOf_smul (volume : Measure (ℝ × ℝ)) (c i) hmemi,
        ih (fun j hj => hφ j (Finset.mem_insert_of_mem hj))] with ω h1 h2 h3
      show LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ))
          (fun p => c i * φ i p + ∑ j ∈ S, c j * φ j p) ω =
        ∑ j ∈ insert i S, c j * LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) (φ j) ω
      rw [show (fun p : ℝ × ℝ => c i * φ i p + ∑ j ∈ S, c j * φ j p)
          = (fun p => c i * φ i p) + fun p => ∑ j ∈ S, c j * φ j p from rfl, h1,
        Finset.sum_insert hiS]
      have hφi' : (fun p : ℝ × ℝ => c i * φ i p) = c i • φ i := by funext p; simp [smul_eq_mul]
      rw [hφi', h2, h3]

/-- **The squared `L²` norm of a finite linear combination of the space-time test functions is
the corresponding quadratic form of `Parking.contOverlap`.** -/
theorem integral_sq_sum_contNoiseTest {k : ℕ} (T : ℝ) (u : Fin k → Fin 2 → ℝ) (t : Fin k → ℝ) :
    (∫ p : ℝ × ℝ, (∑ l, t l * contNoiseTest T (u l 0) (u l 1) p) ^ 2) =
      ∑ l, ∑ l', t l * t l' * contOverlap T (u l) (u l') := by
  have hterm : ∀ l l' : Fin k, Integrable (fun p : ℝ × ℝ =>
      (t l * contNoiseTest T (u l 0) (u l 1) p) * (t l' * contNoiseTest T (u l' 0) (u l' 1) p))
      (volume : Measure (ℝ × ℝ)) := by
    intro l l'
    have h1 : MemLp (contNoiseTest T (u l 0) (u l 1)) 2 (volume : Measure (ℝ × ℝ)) :=
      memLp_contNoiseTest T (u l 0) (u l 1)
    have h2 : MemLp (contNoiseTest T (u l' 0) (u l' 1)) 2 (volume : Measure (ℝ × ℝ)) :=
      memLp_contNoiseTest T (u l' 0) (u l' 1)
    have hi := (h1.const_mul (t l)).integrable_mul (h2.const_mul (t l'))
    exact hi
  have hpt : ∀ p : ℝ × ℝ, (∑ l, t l * contNoiseTest T (u l 0) (u l 1) p) ^ 2 =
      ∑ l : Fin k, ∑ l' : Fin k,
        (t l * contNoiseTest T (u l 0) (u l 1) p) * (t l' * contNoiseTest T (u l' 0) (u l' 1) p) :=
    fun p => by rw [sq, Finset.sum_mul_sum]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun l' _ => hterm l l']
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_finsetSum _ fun l' _ => hterm l l']
  refine Finset.sum_congr rfl fun l' _ => ?_
  have hpt2 : ∀ p : ℝ × ℝ, (t l * contNoiseTest T (u l 0) (u l 1) p) *
      (t l' * contNoiseTest T (u l' 0) (u l' 1) p) =
      t l * t l' * (contNoiseTest T (u l 0) (u l 1) p * contNoiseTest T (u l' 0) (u l' 1) p) := by
    intro p; ring
  simp_rw [hpt2]
  rw [integral_const_mul, integral_contNoiseTest_mul_eq_contOverlap]
  have hueta : ∀ v : Fin 2 → ℝ, v = ![v 0, v 1] := fun v => by
    funext i; fin_cases i <;> rfl
  rw [← hueta (u l), ← hueta (u l')]

/-- **The finite-dimensional characteristic function of the continuum noise field**: any
weighted combination of `Parking.contZ` at finitely many box points is `√v` times a single
white-noise integral, hence a real centred Gaussian, with the same variance quadratic form
`Parking.tendsto_charFun_orientedBoxReward_linearCombination` computes on the discrete side. -/
theorem charFun_map_contZ_linearCombination (T : ℝ) {k : ℕ} (u : Fin k → Fin 2 → ℝ)
    (t : Fin k → ℝ) {σ2 : ℝ} (hσ2 : 0 ≤ σ2) :
    charFun (contNoiseLaw.map (fun ω => ∑ l, t l * contZ σ2 T (u l 0) (u l 1) ω)) 1 =
      Complex.exp (-(σ2 : ℂ) *
        ((∑ l, ∑ l', t l * t l' * contOverlap T (u l) (u l') : ℝ) : ℂ) / 2) := by
  set Ψ : ℝ × ℝ → ℝ := fun p => ∑ l, t l * contNoiseTest T (u l 0) (u l 1) p with hΨdef
  have hΨmem : MemLp Ψ 2 (volume : Measure (ℝ × ℝ)) :=
    memLp_finsetSum Finset.univ fun l _ => (memLp_contNoiseTest T (u l 0) (u l 1)).const_mul (t l)
  have hlin : LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) Ψ =ᵐ[contNoiseLaw]
      fun ω => ∑ l, t l *
        LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) (contNoiseTest T (u l 0) (u l 1)) ω :=
    whiteNoiseOf_sum Finset.univ t (fun l => contNoiseTest T (u l 0) (u l 1))
      (fun l _ => memLp_contNoiseTest T (u l 0) (u l 1))
  have hcombine : (fun ω => ∑ l, t l * contZ σ2 T (u l 0) (u l 1) ω) =ᵐ[contNoiseLaw]
      fun ω => Real.sqrt σ2 * LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) Ψ ω := by
    filter_upwards [hlin] with ω hω
    show (∑ l, t l * contZ σ2 T (u l 0) (u l 1) ω) =
        Real.sqrt σ2 * LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) Ψ ω
    rw [hω, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    show t l * contZ σ2 T (u l 0) (u l 1) ω =
        Real.sqrt σ2 * (t l * LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ))
          (contNoiseTest T (u l 0) (u l 1)) ω)
    unfold contZ
    ring
  have hcharEq : contNoiseLaw.map (fun ω => ∑ l, t l * contZ σ2 T (u l 0) (u l 1) ω) =
      contNoiseLaw.map
        (fun ω => Real.sqrt σ2 * LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) Ψ ω) :=
    Measure.map_congr hcombine
  rw [hcharEq]
  have hwm : AEMeasurable (LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) Ψ) contNoiseLaw :=
    (LatticeProb.measurable_whiteNoiseOf (volume : Measure (ℝ × ℝ)) Ψ).aemeasurable
  rw [charFun_map_mul_comp hwm (Real.sqrt σ2) 1, map_whiteNoiseOf_contNoise Ψ, charFun_gaussianReal]
  have hnn : (0 : ℝ) ≤ ‖LatticeProb.toLpOrZero (volume : Measure (ℝ × ℝ)) Ψ‖ ^ 2 := sq_nonneg _
  have hcast : ((‖LatticeProb.toLpOrZero (volume : Measure (ℝ × ℝ)) Ψ‖ ^ 2).toNNReal : ℝ) =
      ‖LatticeProb.toLpOrZero (volume : Measure (ℝ × ℝ)) Ψ‖ ^ 2 := Real.coe_toNNReal _ hnn
  have hnorm : ‖LatticeProb.toLpOrZero (volume : Measure (ℝ × ℝ)) Ψ‖ ^ 2 =
      ∑ l, ∑ l', t l * t l' * contOverlap T (u l) (u l') := by
    rw [norm_toLpOrZero_sq_contNoise Ψ hΨmem, hΨdef]
    exact integral_sq_sum_contNoiseTest T u t
  have hsq : Real.sqrt σ2 * Real.sqrt σ2 = σ2 := Real.mul_self_sqrt hσ2
  congr 1
  rw [hcast, hnorm, mul_one, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  have hsqc : ((Real.sqrt σ2 : ℝ) : ℂ) ^ 2 = (σ2 : ℂ) := by
    rw [← Complex.ofReal_pow, sq, hsq]
  rw [hsqc]
  push_cast
  ring

end Parking
end
