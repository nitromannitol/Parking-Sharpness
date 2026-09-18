/-
The law of the continuum noise field on the box `K = [0,T] x [-2A,2A]`
(`parking.tex:3192-3203`), as a genuine Borel probability measure on
`C(rewardBox T A, ℝ)`.

`Parking.contBoxLimitMap` reads the everywhere-continuous-on-the-box modification `Y` of
`contZ` (`Parking.exists_continuousOn_modification_contZ_box`, the module's `hgc`) as an
element of `C(rewardBox T A, ℝ)`, exactly as `Parking.boxToFin`/`Parking.boxToFin_mem_orientedBox`
of `Parking.Support.TightBoxLaw` let `Parking.boxRewardMap` read the discrete field.  Its
measurability is not derived from any general descriptive-set-theoretic fact about the Borel
σ-algebra of `C(K, ℝ)`: instead, `Parking.contBoxRewardMap` assembles, through the SAME
`Parking.boxFieldAssemble` used for the discrete field, a hat-interpolation of `Y` sampled on a
grid of mesh `1/n` in time and `1/√n` in space (`Parking.contGridPoint`, clamped into the box by
`Parking.boxPoint` exactly as `Parking.OrientedCutoffValue.rewardOfBox` clamps).  Since `Y(·,ω)`
is continuous on the compact box for EVERY `ω`, hence uniformly continuous, the interpolation
converges to it UNIFORMLY on the box as `n → ∞`, i.e. in the metric of `C(rewardBox T A, ℝ)`
(`Parking.tendsto_contBoxRewardMap`); a pointwise (in `ω`) limit of measurable maps into a metric
space is measurable (`measurable_of_tendsto_metrizable`), which gives
`Parking.measurable_contBoxLimitMap` and with it the law `Parking.contBoxRewardLaw`.
-/
import Parking.Support.TightBoxLaw
import Parking.Support.TightNoiseModification

open MeasureTheory LatticeProb Filter Topology

noncomputable section

namespace Parking

local instance (T A : ℝ) : MeasurableSpace C(rewardBox T A, ℝ) := borel _
local instance (T A : ℝ) : BorelSpace C(rewardBox T A, ℝ) := ⟨rfl⟩

/-! ### The convex-combination bound for the hat interpolation -/

/-- **`Parking.boxFieldAssemble` is the hat interpolation** of its table, read at the mapped
point of the plane: the same identity `Parking.boxRewardMap_eq_boxFieldAssemble` uses, in
reverse. -/
theorem boxFieldAssemble_eq_hatInterp (T : ℝ) (hT : 0 ≤ T) (A : ℝ) (hA : 0 ≤ A) (n : ℕ)
    (V : ℤ → ℤ → ℝ) (p : rewardBox T A) :
    boxFieldAssemble T hT A hA n V p =
      hatInterp V ((n : ℝ) * boxToFin T A p 0,
        Real.sqrt n * boxToFin T A p 1 + (n : ℝ) * boxToFin T A p 0 / 2) := by
  rw [hatInterp_eq_sum V _ (boxCornerM T n) (boxCornerJ T A n)
    (fun m hm => hat1_ne_zero_mem_boxCornerM T A hT n p hm)
    (fun j hj => hat1_ne_zero_mem_boxCornerJ T hT A hA n p hj)]
  simp only [boxFieldAssemble, ContinuousMap.coe_mk]

/-- **The hat interpolation is a convex combination of its four corner values**, so it lies
within any common bound on their distance to a fixed real. -/
theorem abs_hatInterp_sub_le (V : ℤ → ℤ → ℝ) (u : ℝ × ℝ) (c C : ℝ)
    (hC : ∀ m ∈ ({⌊u.1⌋, ⌊u.1⌋ + 1} : Finset ℤ), ∀ j ∈ ({⌊u.2⌋, ⌊u.2⌋ + 1} : Finset ℤ),
      |V m j - c| ≤ C) :
    |hatInterp V u - c| ≤ C := by
  set S₁ : Finset ℤ := {⌊u.1⌋, ⌊u.1⌋ + 1} with hS₁
  set S₂ : Finset ℤ := {⌊u.2⌋, ⌊u.2⌋ + 1} with hS₂
  have hw1 : ∀ m : ℤ, hat1 (u.1 - (m : ℝ)) ≠ 0 → m ∈ S₁ :=
    fun m hm => by simpa [hS₁, Finset.mem_insert, Finset.mem_singleton] using
      hat1_ne_zero_mem_floor_pair hm
  have hw2 : ∀ j : ℤ, hat1 (u.2 - (j : ℝ)) ≠ 0 → j ∈ S₂ :=
    fun j hj => by simpa [hS₂, Finset.mem_insert, Finset.mem_singleton] using
      hat1_ne_zero_mem_floor_pair hj
  have hsum1 : ∑ m ∈ S₁, ∑ j ∈ S₂, hat1 (u.1 - (m : ℝ)) * hat1 (u.2 - (j : ℝ)) = 1 :=
    hatInterp_weight_sum u S₁ S₂ hw1 hw2
  have heq : hatInterp V u = ∑ m ∈ S₁, ∑ j ∈ S₂, V m j *
      (hat1 (u.1 - (m : ℝ)) * hat1 (u.2 - (j : ℝ))) := hatInterp_eq_sum V u S₁ S₂ hw1 hw2
  have hconst : ∀ a : ℝ, (∑ m ∈ S₁, ∑ j ∈ S₂, a *
      (hat1 (u.1 - (m : ℝ)) * hat1 (u.2 - (j : ℝ)))) = a := by
    intro a
    have step1 : ∀ m : ℤ, (∑ j ∈ S₂, a * (hat1 (u.1 - (m : ℝ)) * hat1 (u.2 - (j : ℝ))))
        = a * ∑ j ∈ S₂, hat1 (u.1 - (m : ℝ)) * hat1 (u.2 - (j : ℝ)) :=
      fun m => (Finset.mul_sum S₂ (fun j => hat1 (u.1 - (m : ℝ)) * hat1 (u.2 - (j : ℝ))) a).symm
    rw [Finset.sum_congr rfl (fun m _ => step1 m),
      ← Finset.mul_sum S₁ (fun m => ∑ j ∈ S₂, hat1 (u.1 - (m : ℝ)) * hat1 (u.2 - (j : ℝ))) a,
      hsum1, mul_one]
  rw [heq, ← hconst c, ← Finset.sum_sub_distrib]
  calc |∑ m ∈ S₁, (∑ j ∈ S₂, V m j * (hat1 (u.1 - (m : ℝ)) * hat1 (u.2 - (j : ℝ)))
        - ∑ j ∈ S₂, c * (hat1 (u.1 - (m : ℝ)) * hat1 (u.2 - (j : ℝ))))|
      ≤ ∑ m ∈ S₁, |∑ j ∈ S₂, V m j * (hat1 (u.1 - (m : ℝ)) * hat1 (u.2 - (j : ℝ)))
          - ∑ j ∈ S₂, c * (hat1 (u.1 - (m : ℝ)) * hat1 (u.2 - (j : ℝ)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ m ∈ S₁, |∑ j ∈ S₂, (V m j - c) * (hat1 (u.1 - (m : ℝ)) * hat1 (u.2 - (j : ℝ)))| := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← Finset.sum_sub_distrib]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ ∑ m ∈ S₁, ∑ j ∈ S₂, |(V m j - c) * (hat1 (u.1 - (m : ℝ)) * hat1 (u.2 - (j : ℝ)))| := by
        refine Finset.sum_le_sum fun m _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ S₁, ∑ j ∈ S₂, C * (hat1 (u.1 - (m : ℝ)) * hat1 (u.2 - (j : ℝ))) := by
        refine Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun j hj => ?_
        rw [abs_mul, abs_of_nonneg (mul_nonneg (hat1_nonneg _) (hat1_nonneg _))]
        exact mul_le_mul_of_nonneg_right (hC m hm j hj) (mul_nonneg (hat1_nonneg _) (hat1_nonneg _))
    _ = C := hconst C

/-! ### The grid sampling of the continuum field -/

/-- The grid point at mesh `n`, corner `(m,j)`: inverts `Parking.boxRewardMap`'s own convention
`m = n u₀`, `j = √n u₁ + n u₀ / 2`. -/
def contGridPoint (n : ℕ) (m j : ℤ) : ℝ × ℝ :=
  ((m : ℝ) / n, ((j : ℝ) - (m : ℝ) / 2) / Real.sqrt n)

/-- The grid point, clamped into the box and read as a point of the plane. -/
def contBoxGridArg (T : ℝ) (hT : 0 ≤ T) (A : ℝ) (hA : 0 ≤ A) (n : ℕ) (m j : ℤ) : Fin 2 → ℝ :=
  boxToFin T A (boxPoint hT hA (contGridPoint n m j).1 (contGridPoint n m j).2)

/-- The grid table of a field on the plane, read at the clamped grid points. -/
def contZGrid (T : ℝ) (hT : 0 ≤ T) (A : ℝ) (hA : 0 ≤ A) (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (n : ℕ) (m j : ℤ) (ω : contNoiseSpace) : ℝ :=
  Y (contBoxGridArg T hT A hA n m j) ω

theorem measurable_contZGrid (T : ℝ) (hT : 0 ≤ T) (A : ℝ) (hA : 0 ≤ A)
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ) (hYmeas : ∀ z, Measurable (Y z)) (n : ℕ) (m j : ℤ) :
    Measurable (contZGrid T hT A hA Y n m j) := hYmeas _

/-- **The continuum box-reward field at scale `n`**, as an element of `C(rewardBox T A, ℝ)`:
the hat interpolation of the grid table, assembled exactly as `Parking.boxRewardMap` assembles
the discrete field. -/
def contBoxRewardMap (T : ℝ) (hT : 0 ≤ T) (A : ℝ) (hA : 0 ≤ A)
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ) (n : ℕ) (ω : contNoiseSpace) :
    C(rewardBox T A, ℝ) :=
  boxFieldAssemble T hT A hA n (fun m j => contZGrid T hT A hA Y n m j ω)

theorem measurable_contBoxRewardMap (T : ℝ) (hT : 0 ≤ T) (A : ℝ) (hA : 0 ≤ A)
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ) (hYmeas : ∀ z, Measurable (Y z)) (n : ℕ) :
    Measurable (contBoxRewardMap T hT A hA Y n) :=
  (continuous_boxFieldAssemble T hT A hA n).measurable.comp
    (measurable_pi_lambda _ fun m => measurable_pi_lambda _ fun j =>
      measurable_contZGrid T hT A hA Y hYmeas n m j)

/-- **The box-restriction of the everywhere-continuous modification**, as an element of
`C(rewardBox T A, ℝ)`. -/
def contBoxLimitMap (T : ℝ) (hT : 0 ≤ T) (A : ℝ) (hA : 0 ≤ A)
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (hYcont : ∀ ω, ContinuousOn (fun z => Y z ω) (orientedBox T A)) (ω : contNoiseSpace) :
    C(rewardBox T A, ℝ) :=
  ⟨fun p => Y (boxToFin T A p) ω,
    (hYcont ω).comp_continuous (continuous_boxToFin T A) (boxToFin_mem_orientedBox T hT A hA)⟩

end Parking

end
