/-
The continuum box-reward law: `Parking.contBoxRewardMap` converges, at every fixed noise
realization, to `Parking.contBoxLimitMap` uniformly on the box, because the modification `Y`
is continuous (hence uniformly continuous) on the compact box and the grid mesh of
`Parking.contBoxRewardMap` at scale `n` shrinks to `0` in both time and space as `n → ∞`.  A
pointwise limit of measurable maps into a metric space is measurable
(`measurable_of_tendsto_metrizable`), which is how `Parking.contBoxRewardLaw` is built as a
genuine Borel probability measure on `C(rewardBox T A, ℝ)`, with no descriptive-set-theoretic
fact about the σ-algebra of `C(K, ℝ)` needed.
-/
import Parking.Support.TightContBoxLaw

open MeasureTheory LatticeProb Filter Topology

noncomputable section

namespace Parking

local instance (T A : ℝ) : MeasurableSpace C(rewardBox T A, ℝ) := borel _
local instance (T A : ℝ) : BorelSpace C(rewardBox T A, ℝ) := ⟨rfl⟩

/-! ### The mesh of the grid shrinks to zero -/

/-- Either corner of a floor pair is within `1` of the real point. -/
theorem abs_sub_mem_floor_pair {x : ℝ} {m : ℤ} (hm : m ∈ ({⌊x⌋, ⌊x⌋ + 1} : Finset ℤ)) :
    |(m : ℝ) - x| ≤ 1 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  have h1 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have h2 : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
  rcases hm with rfl | rfl
  · rw [abs_le]; constructor <;> linarith
  · push_cast
    rw [abs_le]; constructor <;> linarith

/-- Clamping to an interval containing a point does not increase the distance to that
point. -/
theorem abs_projIcc_sub_of_mem {a b : ℝ} (h : a ≤ b) (s : ℝ) (x : ↥(Set.Icc a b)) :
    |(Set.projIcc a b h s : ℝ) - (x : ℝ)| ≤ |s - (x : ℝ)| := by
  have hk := Set.abs_projIcc_sub_projIcc h (c := s) (d := (x : ℝ))
  simpa [Set.projIcc_of_mem h x.2] using hk

/-- **The clamped grid point of a corner of `p`'s cell is within the mesh of `p` itself, in
each coordinate.** -/
theorem abs_contBoxGridArg_sub_le (T : ℝ) (hT : 0 ≤ T) (A : ℝ) (hA : 0 ≤ A) {n : ℕ} (hn : 1 ≤ n)
    (p : rewardBox T A) {m j : ℤ}
    (hm : m ∈ ({⌊(n : ℝ) * boxToFin T A p 0⌋, ⌊(n : ℝ) * boxToFin T A p 0⌋ + 1} : Finset ℤ))
    (hj : j ∈ ({⌊Real.sqrt n * boxToFin T A p 1 + (n : ℝ) * boxToFin T A p 0 / 2⌋,
        ⌊Real.sqrt n * boxToFin T A p 1 + (n : ℝ) * boxToFin T A p 0 / 2⌋ + 1} : Finset ℤ)) :
    |contBoxGridArg T hT A hA n m j 0 - boxToFin T A p 0| ≤ 1 / n + 3 / (2 * Real.sqrt n) ∧
    |contBoxGridArg T hT A hA n m j 1 - boxToFin T A p 1| ≤ 1 / n + 3 / (2 * Real.sqrt n) := by
  set u0 : ℝ := boxToFin T A p 0 with hu0
  set u1 : ℝ := boxToFin T A p 1 with hu1
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsn0 : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hm1 : |(m : ℝ) - (n : ℝ) * u0| ≤ 1 := abs_sub_mem_floor_pair hm
  have hj1 : |(j : ℝ) - (Real.sqrt n * u1 + (n : ℝ) * u0 / 2)| ≤ 1 := abs_sub_mem_floor_pair hj
  have hmem0 : u0 ∈ Set.Icc (0 : ℝ) T := p.1.2
  have hmem1 : u1 ∈ Set.Icc (-(2 * A)) (2 * A) := p.2.2
  have hc0 : contBoxGridArg T hT A hA n m j 0 = (Set.projIcc (0 : ℝ) T hT
      (contGridPoint n m j).1 : ℝ) := rfl
  have hc1 : contBoxGridArg T hT A hA n m j 1 = (Set.projIcc (-(2 * A)) (2 * A) (by linarith)
      (contGridPoint n m j).2 : ℝ) := rfl
  constructor
  · rw [hc0]
    have hb0 : |(Set.projIcc (0 : ℝ) T hT (contGridPoint n m j).1 : ℝ) - u0| ≤
        |(contGridPoint n m j).1 - u0| :=
      abs_projIcc_sub_of_mem hT (contGridPoint n m j).1 ⟨u0, hmem0⟩
    refine le_trans hb0 ?_
    have heq : (contGridPoint n m j).1 - u0 = ((m : ℝ) - (n : ℝ) * u0) / n := by
      show (m : ℝ) / n - u0 = ((m : ℝ) - (n : ℝ) * u0) / n
      field_simp
    rw [heq, abs_div, Nat.abs_cast]
    calc |(m : ℝ) - (n : ℝ) * u0| / n ≤ 1 / n := by
          apply div_le_div_of_nonneg_right hm1 hn0.le
      _ ≤ 1 / n + 3 / (2 * Real.sqrt n) := le_add_of_nonneg_right (by positivity)
  · rw [hc1]
    have hb1 : |(Set.projIcc (-(2 * A)) (2 * A) (by linarith : -(2 * A) ≤ 2 * A)
        (contGridPoint n m j).2 : ℝ) - u1| ≤ |(contGridPoint n m j).2 - u1| :=
      abs_projIcc_sub_of_mem (by linarith) (contGridPoint n m j).2 ⟨u1, hmem1⟩
    refine le_trans hb1 ?_
    have heq : (contGridPoint n m j).2 - u1 =
        (((j : ℝ) - (Real.sqrt n * u1 + (n : ℝ) * u0 / 2)) + ((n : ℝ) * u0 - (m : ℝ)) / 2)
          / Real.sqrt n := by
      show ((j : ℝ) - (m : ℝ) / 2) / Real.sqrt n - u1 = _
      have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
      field_simp
      nlinarith [hsn]
    rw [heq, abs_div, abs_of_pos hsn0]
    have hnum : |((j : ℝ) - (Real.sqrt n * u1 + (n : ℝ) * u0 / 2)) +
        ((n : ℝ) * u0 - (m : ℝ)) / 2| ≤ 1 + 1 / 2 := by
      refine le_trans (abs_add_le _ _) ?_
      have h2 : |((n : ℝ) * u0 - (m : ℝ)) / 2| ≤ 1 / 2 := by
        rw [abs_div]
        have hle2 : |(n : ℝ) * u0 - (m : ℝ)| ≤ 1 := by
          rw [abs_sub_comm]; exact hm1
        calc |(n : ℝ) * u0 - (m : ℝ)| / |(2 : ℝ)| ≤ 1 / |(2 : ℝ)| := by
              apply div_le_div_of_nonneg_right hle2 (by norm_num)
          _ = 1 / 2 := by norm_num
      linarith [hj1]
    calc |((j : ℝ) - (Real.sqrt n * u1 + (n : ℝ) * u0 / 2)) +
          ((n : ℝ) * u0 - (m : ℝ)) / 2| / Real.sqrt n
        ≤ (3 / 2) / Real.sqrt n := by
          apply div_le_div_of_nonneg_right (by linarith [hnum]) hsn0.le
      _ = 3 / (2 * Real.sqrt n) := by ring
      _ ≤ 1 / n + 3 / (2 * Real.sqrt n) := le_add_of_nonneg_left (by positivity)

/-- **The clamped grid point of a corner of `p`'s cell is within the mesh of `p` itself.** -/
theorem dist_contBoxGridArg_le (T : ℝ) (hT : 0 ≤ T) (A : ℝ) (hA : 0 ≤ A) {n : ℕ} (hn : 1 ≤ n)
    (p : rewardBox T A) {m j : ℤ}
    (hm : m ∈ ({⌊(n : ℝ) * boxToFin T A p 0⌋, ⌊(n : ℝ) * boxToFin T A p 0⌋ + 1} : Finset ℤ))
    (hj : j ∈ ({⌊Real.sqrt n * boxToFin T A p 1 + (n : ℝ) * boxToFin T A p 0 / 2⌋,
        ⌊Real.sqrt n * boxToFin T A p 1 + (n : ℝ) * boxToFin T A p 0 / 2⌋ + 1} : Finset ℤ)) :
    dist (contBoxGridArg T hT A hA n m j) (boxToFin T A p) ≤ 1 / n + 3 / (2 * Real.sqrt n) := by
  obtain ⟨h0, h1⟩ := abs_contBoxGridArg_sub_le T hT A hA hn p hm hj
  refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
  fin_cases i
  · rw [Real.dist_eq]; exact h0
  · rw [Real.dist_eq]; exact h1

/-- The mesh bound tends to zero. -/
theorem tendsto_contMeshBound :
    Tendsto (fun n : ℕ => 1 / (n : ℝ) + 3 / (2 * Real.sqrt n)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have h2 : Tendsto (fun n : ℕ => 3 / (2 * Real.sqrt n)) atTop (𝓝 0) := by
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      (Real.tendsto_sqrt_atTop).comp tendsto_natCast_atTop_atTop
    have h2sqrt : Tendsto (fun n : ℕ => 2 * Real.sqrt n) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num) hsqrt
    exact Tendsto.div_atTop tendsto_const_nhds h2sqrt
  simpa using h1.add h2

/-! ### The convergence in `C(K, ℝ)` -/

/-- **The continuum box-reward field converges, at every noise realization, to the box
restriction of the everywhere-continuous modification, uniformly on the box.** -/
theorem tendsto_contBoxRewardMap (T : ℝ) (hT : 0 ≤ T) (A : ℝ) (hA : 0 ≤ A)
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (hYcont : ∀ ω, ContinuousOn (fun z => Y z ω) (orientedBox T A)) (ω : contNoiseSpace) :
    Tendsto (fun n => contBoxRewardMap T hT A hA Y n ω) atTop
      (𝓝 (contBoxLimitMap T hT A hA Y hYcont ω)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set f : (Fin 2 → ℝ) → ℝ := fun z => Y z ω with hf
  have hfu : UniformContinuousOn f (orientedBox T A) :=
    (isCompact_Icc (a := (![0, -(2 * A)] : Fin 2 → ℝ)) (b := ![T, 2 * A])).uniformContinuousOn_of_continuous
      (hYcont ω)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.1 hfu (ε / 2) (by linarith)
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.1 tendsto_contMeshBound) δ hδ
  refine ⟨max N₀ 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right N₀ 1) hn
  have hnN0 : N₀ ≤ n := le_trans (le_max_left N₀ 1) hn
  have hmeshlt : 1 / (n : ℝ) + 3 / (2 * Real.sqrt n) < δ := by
    have hd := hN₀ n hnN0
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hd
    exact hd
  rw [ContinuousMap.dist_lt_iff hε]
  intro p
  rw [Real.dist_eq]
  have hassem : contBoxRewardMap T hT A hA Y n ω p =
      hatInterp (fun m j => contZGrid T hT A hA Y n m j ω)
        ((n : ℝ) * boxToFin T A p 0,
          Real.sqrt n * boxToFin T A p 1 + (n : ℝ) * boxToFin T A p 0 / 2) :=
    boxFieldAssemble_eq_hatInterp T hT A hA n _ p
  have hlimval : contBoxLimitMap T hT A hA Y hYcont ω p = f (boxToFin T A p) := rfl
  rw [hassem, hlimval]
  have hbound : |hatInterp (fun m j => contZGrid T hT A hA Y n m j ω)
      ((n : ℝ) * boxToFin T A p 0,
        Real.sqrt n * boxToFin T A p 1 + (n : ℝ) * boxToFin T A p 0 / 2)
      - f (boxToFin T A p)| ≤ ε / 2 := by
    apply abs_hatInterp_sub_le
    intro m hm j hj
    have hmemcorner : contBoxGridArg T hT A hA n m j ∈ orientedBox T A :=
      boxToFin_mem_orientedBox T hT A hA _
    have hmemp : boxToFin T A p ∈ orientedBox T A := boxToFin_mem_orientedBox T hT A hA p
    have hdlt : dist (contBoxGridArg T hT A hA n m j) (boxToFin T A p) < δ :=
      lt_of_le_of_lt (dist_contBoxGridArg_le T hT A hA hn1 p hm hj) hmeshlt
    have hkey := hmod (contBoxGridArg T hT A hA n m j) hmemcorner (boxToFin T A p) hmemp hdlt
    rw [Real.dist_eq] at hkey
    have heq : contZGrid T hT A hA Y n m j ω = f (contBoxGridArg T hT A hA n m j) := rfl
    rw [heq]
    exact hkey.le
  linarith

/-! ### The law -/

/-- **The box restriction of the everywhere-continuous modification is measurable** into
`C(rewardBox T A, ℝ)`: a pointwise limit of the measurable `Parking.contBoxRewardMap`. -/
theorem measurable_contBoxLimitMap (T : ℝ) (hT : 0 ≤ T) (A : ℝ) (hA : 0 ≤ A)
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ) (hYmeas : ∀ z, Measurable (Y z))
    (hYcont : ∀ ω, ContinuousOn (fun z => Y z ω) (orientedBox T A)) :
    Measurable (contBoxLimitMap T hT A hA Y hYcont) :=
  measurable_of_tendsto_metrizable (fun n => measurable_contBoxRewardMap T hT A hA Y hYmeas n)
    (tendsto_pi_nhds.2 (fun ω => tendsto_contBoxRewardMap T hT A hA Y hYcont ω))

/-- **The law of the continuum noise field on the box**: the pushforward of `contNoiseLaw`
along the box restriction of the everywhere-continuous modification, a genuine Borel
probability measure on `C(rewardBox T A, ℝ)`. -/
noncomputable def contBoxRewardLaw (T : ℝ) (hT : 0 ≤ T) (A : ℝ) (hA : 0 ≤ A)
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ) (_hYmeas : ∀ z, Measurable (Y z))
    (hYcont : ∀ ω, ContinuousOn (fun z => Y z ω) (orientedBox T A)) :
    Measure C(rewardBox T A, ℝ) :=
  contNoiseLaw.map (contBoxLimitMap T hT A hA Y hYcont)

/-- **The field law is a probability measure.** -/
instance (T : ℝ) (hT : 0 ≤ T) (A : ℝ) (hA : 0 ≤ A)
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ) (hYmeas : ∀ z, Measurable (Y z))
    (hYcont : ∀ ω, ContinuousOn (fun z => Y z ω) (orientedBox T A)) :
    IsProbabilityMeasure (contBoxRewardLaw T hT A hA Y hYmeas hYcont) :=
  Measure.isProbabilityMeasure_map
    (measurable_contBoxLimitMap T hT A hA Y hYmeas hYcont).aemeasurable

end Parking

end
