/-
A maximal inequality for the rescaled oriented walk's coordinate-difference partial sum
`Parking.walkPartialSum` (`TightWalk.lean`'s `S_k := ∑_{j<k} walkStepSign (p j).1`), uniform in
the horizon `n`: Doob's maximal inequality applied to the submartingale `S_k²`.  This is the
standard content `happ` needs: the walk's rescaled coordinate difference exits a window of
half-width `A` with probability at most `1/(16A²)`, uniformly in `n`.

The bridge from this repository's own `Parking.IsStoppingTimeLE` formalism to Mathlib's
`MeasureTheory.Filtration`/`Submartingale` framework goes through `Filtration.natural S hSm`
(the smallest filtration making `S` adapted): the increment `S_{k+1} - S_k = walkStepSign (p k).1`
is independent of the coordinates before `k` (`ProbabilityTheory.indep_iSup_of_disjoint`, fed by
`iIndepFun_infinitePi`), hence independent of `Filtration.natural S hSm k` (a coarser
σ-algebra), hence has conditional mean zero (`MeasureTheory.condExp_indep_eq`), which gives both
the martingale property of `S` and, directly, the exact conditional increment identity
`E[(S_{k+1})² - (S_k)² | 𝒢_k] = 1` that makes `S²` a submartingale.
-/
import Parking.Support.TightWalk
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ConditionalExpectation

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped NNReal ENNReal

noncomputable section

namespace Parking

/-- **The explicit partial sum** driving the rescaled walk's coordinate difference
(`Parking.orientedPath_coord_sub`). -/
def walkPartialSum (k : ℕ) (p : ℕ → Fin 2 × Bool) : ℝ :=
  ∑ j ∈ Finset.range k, walkStepSign (p j).1

theorem walkPartialSum_eq_orientedPath_coord_sub (k : ℕ) (p : ℕ → Fin 2 × Bool) :
    walkPartialSum k p = ((orientedPath (0 : Site 2) p k : Site 2) 1 : ℝ)
        - ((orientedPath (0 : Site 2) p k : Site 2) 0 : ℝ) :=
  (orientedPath_coord_sub k p).symm

theorem measurable_walkPartialSum (k : ℕ) : Measurable (walkPartialSum k) :=
  measurable_of_finite_dependence (d := 2) (by norm_num) k _
    (fun p q hpq => Finset.sum_congr rfl fun j hj => by
      rw [Finset.mem_range] at hj; rw [hpq j hj])

theorem stronglyMeasurable_walkPartialSum (k : ℕ) : StronglyMeasurable (walkPartialSum k) :=
  (measurable_walkPartialSum k).stronglyMeasurable

theorem abs_walkStepSign (c : Fin 2) : |walkStepSign c| = 1 := by
  fin_cases c <;> simp [walkStepSign]

theorem sq_walkStepSign (c : Fin 2) : (walkStepSign c) ^ 2 = 1 := by
  fin_cases c <;> norm_num [walkStepSign]

theorem abs_walkPartialSum_le (k : ℕ) (p : ℕ → Fin 2 × Bool) : |walkPartialSum k p| ≤ k := by
  calc |walkPartialSum k p| ≤ ∑ j ∈ Finset.range k, |walkStepSign (p j).1| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ _j ∈ Finset.range k, (1 : ℝ) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [abs_walkStepSign]
    _ = k := by rw [Finset.sum_const, Finset.card_range]; simp

/-- **The coordinate σ-algebras of the direction sequence are jointly independent.** -/
theorem iIndep_coord :
    iIndep (fun j : ℕ => MeasurableSpace.comap (fun p : ℕ → Fin 2 × Bool => p j) inferInstance)
      (walkLaw 2) := by
  haveI := stepLaw_isProbability (d := 2) (by norm_num)
  exact (iIndepFun_infinitePi (Ω := fun _ : ℕ => Fin 2 × Bool) (P := fun _ : ℕ => stepLaw 2)
    (X := fun (_ : ℕ) (b : Fin 2 × Bool) => b) (fun _ => Measurable.of_discrete)).iIndep

/-- **The natural filtration of `Parking.walkPartialSum`.** -/
def walkFiltration : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Fin 2 × Bool)) :=
  Filtration.natural walkPartialSum stronglyMeasurable_walkPartialSum

theorem stronglyAdapted_walkFiltration :
    StronglyAdapted walkFiltration walkPartialSum :=
  Filtration.stronglyAdapted_natural stronglyMeasurable_walkPartialSum

/-- **`walkFiltration k` sits inside the σ-algebra of the coordinates below `k`**: every
`walkPartialSum j` for `j ≤ k` is a finite sum of terms reading coordinates `< j ≤ k`. -/
theorem walkFiltration_le_iSup_coord (k : ℕ) :
    walkFiltration k ≤ ⨆ i ∈ Set.Iio k,
      MeasurableSpace.comap (fun p : ℕ → Fin 2 × Bool => p i) inferInstance := by
  set M : MeasurableSpace (ℕ → Fin 2 × Bool) :=
    ⨆ i ∈ Set.Iio k, MeasurableSpace.comap (fun p : ℕ → Fin 2 × Bool => p i) inferInstance
    with hMdef
  show (⨆ j ≤ k, MeasurableSpace.comap (walkPartialSum j) inferInstance) ≤ M
  refine iSup₂_le fun j hjk => ?_
  rw [← measurable_iff_comap_le]
  show Measurable[M] (fun p => ∑ i ∈ Finset.range j, walkStepSign (p i).1)
  refine Finset.measurable_sum (Finset.range j) fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hik : i ∈ Set.Iio k := lt_of_lt_of_le hi hjk
  have heval : Measurable[M] (fun p : ℕ → Fin 2 × Bool => p i) := by
    rw [hMdef]
    exact measurable_iff_comap_le.mpr
      (le_biSup (fun i => MeasurableSpace.comap (fun p : ℕ → Fin 2 × Bool => p i) inferInstance)
        hik)
  exact (Measurable.of_discrete (f := fun b : Fin 2 × Bool => walkStepSign b.1)).comp heval

/-- **The `k`-th coordinate is independent of `walkFiltration k`.** -/
theorem indep_coord_walkFiltration (k : ℕ) :
    Indep (MeasurableSpace.comap (fun p : ℕ → Fin 2 × Bool => p k) inferInstance)
      (walkFiltration k) (walkLaw 2) := by
  have h_le : ∀ j : ℕ, MeasurableSpace.comap (fun p : ℕ → Fin 2 × Bool => p j) inferInstance ≤
      (inferInstance : MeasurableSpace (ℕ → Fin 2 × Bool)) :=
    fun j => measurable_iff_comap_le.mp (measurable_pi_apply j)
  have hST : Disjoint (Set.Iio k) ({k} : Set ℕ) := by
    simp [Set.disjoint_singleton_right]
  have h1 := indep_iSup_of_disjoint h_le iIndep_coord hST
  rw [_root_.iSup_singleton] at h1
  exact indep_of_indep_of_le h1.symm le_rfl (walkFiltration_le_iSup_coord k)

/-- **A single step has mean zero.** -/
theorem integral_walkStepSign_eval (k : ℕ) :
    ∫ p : ℕ → Fin 2 × Bool, walkStepSign (p k).1 ∂(walkLaw 2) = 0 := by
  haveI := stepLaw_isProbability (d := 2) (by norm_num)
  have hmap : (walkLaw 2).map (fun p : ℕ → Fin 2 × Bool => p k) = stepLaw 2 :=
    Measure.infinitePi_map_eval _ _
  have hmeas : Measurable (fun b : Fin 2 × Bool => walkStepSign b.1) := Measurable.of_discrete
  have hpull : ∫ b, walkStepSign b.1 ∂((walkLaw 2).map (fun p : ℕ → Fin 2 × Bool => p k))
      = ∫ p : ℕ → Fin 2 × Bool, walkStepSign (p k).1 ∂(walkLaw 2) :=
    integral_map (measurable_pi_apply k).aemeasurable hmeas.aestronglyMeasurable
  have hrw : (∫ p : ℕ → Fin 2 × Bool, walkStepSign (p k).1 ∂(walkLaw 2))
      = ∫ b, walkStepSign b.1 ∂(stepLaw 2) := by
    rw [← hmap]; exact hpull.symm
  rw [hrw, integral_stepLaw (by norm_num), Fintype.sum_prod_type]
  norm_num [Fin.sum_univ_two, Fintype.sum_bool, walkStepSign]

/-- **The increment of `Parking.walkPartialSum` has conditional mean zero.** -/
theorem condExp_walkStepSign_walkFiltration (k : ℕ) :
    (walkLaw 2)[fun p => walkStepSign (p k).1 | walkFiltration k] =ᵐ[walkLaw 2] 0 := by
  haveI := stepLaw_isProbability (d := 2) (by norm_num)
  haveI : IsProbabilityMeasure (walkLaw 2) := by unfold walkLaw; infer_instance
  have hSM : StronglyMeasurable[MeasurableSpace.comap
      (fun p : ℕ → Fin 2 × Bool => p k) inferInstance] (fun p : ℕ → Fin 2 × Bool =>
      walkStepSign (p k).1) := by
    have heval : Measurable[MeasurableSpace.comap (fun p : ℕ → Fin 2 × Bool => p k)
        inferInstance] (fun p : ℕ → Fin 2 × Bool => p k) :=
      measurable_iff_comap_le.mpr le_rfl
    exact ((Measurable.of_discrete (f := fun b : Fin 2 × Bool => walkStepSign b.1)).comp
      heval).stronglyMeasurable
  have hle₁ : MeasurableSpace.comap (fun p : ℕ → Fin 2 × Bool => p k) inferInstance ≤
      (inferInstance : MeasurableSpace (ℕ → Fin 2 × Bool)) :=
    measurable_iff_comap_le.mp (measurable_pi_apply k)
  have h := condExp_indep_eq (μ := walkLaw 2) (m₁ := MeasurableSpace.comap
      (fun p : ℕ → Fin 2 × Bool => p k) inferInstance) (m₂ := walkFiltration k)
    hle₁ (walkFiltration.le k) hSM (indep_coord_walkFiltration k)
  filter_upwards [h] with p hp
  rw [hp]
  exact integral_walkStepSign_eval k

theorem integrable_walkPartialSum (k : ℕ) : Integrable (walkPartialSum k) (walkLaw 2) := by
  haveI := stepLaw_isProbability (d := 2) (by norm_num)
  haveI : IsProbabilityMeasure (walkLaw 2) := by unfold walkLaw; infer_instance
  exact Integrable.mono' (integrable_const (k : ℝ)) (measurable_walkPartialSum k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact abs_walkPartialSum_le k p)

theorem integrable_walkPartialSum_sq (k : ℕ) :
    Integrable (fun p => (walkPartialSum k p) ^ 2) (walkLaw 2) := by
  haveI := stepLaw_isProbability (d := 2) (by norm_num)
  haveI : IsProbabilityMeasure (walkLaw 2) := by unfold walkLaw; infer_instance
  refine Integrable.mono' (integrable_const ((k : ℝ) ^ 2))
    ((measurable_walkPartialSum k).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc (walkPartialSum k p) ^ 2 = |walkPartialSum k p| ^ 2 := (sq_abs _).symm
    _ ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (abs_walkPartialSum_le k p) 2

/-- **`Parking.walkPartialSum` is a martingale for its own natural filtration.** -/
theorem martingale_walkPartialSum : Martingale walkPartialSum walkFiltration (walkLaw 2) := by
  haveI := stepLaw_isProbability (d := 2) (by norm_num)
  haveI : IsProbabilityMeasure (walkLaw 2) := by unfold walkLaw; infer_instance
  refine martingale_of_condExp_sub_eq_zero_nat stronglyAdapted_walkFiltration
    integrable_walkPartialSum fun i => ?_
  have heq : (walkPartialSum (i + 1) - walkPartialSum i) = fun p => walkStepSign (p i).1 := by
    funext p
    simp only [Pi.sub_apply]
    show (∑ j ∈ Finset.range (i + 1), walkStepSign (p j).1)
        - (∑ j ∈ Finset.range i, walkStepSign (p j).1) = walkStepSign (p i).1
    rw [Finset.sum_range_succ]
    ring
  rw [heq]
  exact condExp_walkStepSign_walkFiltration i

/-- **The conditional increment of the squared partial sum is identically `1`.** -/
theorem condExp_sq_walkPartialSum_sub (i : ℕ) :
    (walkLaw 2)[fun p => (walkPartialSum (i + 1) p) ^ 2 - (walkPartialSum i p) ^ 2 |
        walkFiltration i] =ᵐ[walkLaw 2] fun _ => (1 : ℝ) := by
  haveI := stepLaw_isProbability (d := 2) (by norm_num)
  haveI : IsProbabilityMeasure (walkLaw 2) := by unfold walkLaw; infer_instance
  have hstepMeas : Measurable (fun p : ℕ → Fin 2 × Bool => walkStepSign (p i).1) :=
    (Measurable.of_discrete (f := fun b : Fin 2 × Bool => walkStepSign b.1)).comp
      (measurable_pi_apply i)
  have hpt : ∀ p : ℕ → Fin 2 × Bool, (walkPartialSum (i + 1) p) ^ 2 - (walkPartialSum i p) ^ 2
      = (2 * walkPartialSum i p) * walkStepSign (p i).1 + 1 := by
    intro p
    have hsucc : walkPartialSum (i + 1) p = walkPartialSum i p + walkStepSign (p i).1 := by
      show (∑ j ∈ Finset.range (i + 1), walkStepSign (p j).1)
          = (∑ j ∈ Finset.range i, walkStepSign (p j).1) + walkStepSign (p i).1
      rw [Finset.sum_range_succ]
    rw [hsucc]
    have hsq := sq_walkStepSign (p i).1
    nlinarith [hsq]
  have heq : (fun p => (walkPartialSum (i + 1) p) ^ 2 - (walkPartialSum i p) ^ 2)
      = (fun p => (2 * walkPartialSum i p) * walkStepSign (p i).1) + fun _ => (1 : ℝ) := by
    funext p
    rw [Pi.add_apply]
    exact hpt p
  rw [heq]
  have hle : walkFiltration i ≤ (inferInstance : MeasurableSpace (ℕ → Fin 2 × Bool)) :=
    walkFiltration.le i
  have hSMf : StronglyMeasurable[walkFiltration i] (fun p => 2 * walkPartialSum i p) :=
    stronglyMeasurable_const.mul (stronglyAdapted_walkFiltration i)
  have hfbound : ∀ᵐ p ∂(walkLaw 2), ‖2 * walkPartialSum i p‖ ≤ (2 * i : ℝ) := by
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left (abs_walkPartialSum_le i p) (by norm_num)
  have hgint : Integrable (fun p => walkStepSign (p i).1) (walkLaw 2) :=
    Integrable.mono' (integrable_const (1 : ℝ)) hstepMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]; exact (abs_walkStepSign _).le)
  have hmul := condExp_stronglyMeasurable_mul_of_bound hle hSMf hgint (2 * i) hfbound
  have hmulEq : (fun p => 2 * walkPartialSum i p) * (fun p => walkStepSign (p i).1)
      = fun p => 2 * walkPartialSum i p * walkStepSign (p i).1 := by
    funext p; rw [Pi.mul_apply]
  rw [hmulEq] at hmul
  have hint1 : Integrable (fun p => (2 * walkPartialSum i p) * walkStepSign (p i).1)
      (walkLaw 2) := by
    refine Integrable.mono' (integrable_const (2 * i : ℝ)) ?_
      (Filter.Eventually.of_forall fun p => ?_)
    · exact (((measurable_walkPartialSum i).const_mul 2).mul hstepMeas).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      have h1 : |2 * walkPartialSum i p| ≤ (2 * i : ℝ) := by
        rw [abs_mul, abs_two]
        exact mul_le_mul_of_nonneg_left (abs_walkPartialSum_le i p) (by norm_num)
      calc |2 * walkPartialSum i p| * |walkStepSign (p i).1|
          ≤ (2 * i : ℝ) * 1 :=
            mul_le_mul h1 (abs_walkStepSign _).le (abs_nonneg _) (by positivity)
        _ = 2 * i := mul_one _
  have hcombine := condExp_add hint1 (integrable_const (1 : ℝ)) (walkFiltration i)
  have hconst := condExp_const (μ := walkLaw 2) hle (1 : ℝ)
  filter_upwards [hcombine, hmul, condExp_walkStepSign_walkFiltration i] with p hp1 hp2 hp3
  rw [hp1]
  simp only [Pi.add_apply]
  rw [hp2]
  simp only [Pi.mul_apply, Pi.zero_apply] at hp3 ⊢
  rw [hp3]
  simp only [mul_zero, zero_add]
  rw [hconst]

/-- **`(Parking.walkPartialSum)²` is a submartingale for `Parking.walkFiltration`.** -/
theorem submartingale_walkPartialSum_sq :
    Submartingale (fun k p => (walkPartialSum k p) ^ 2) walkFiltration (walkLaw 2) := by
  haveI := stepLaw_isProbability (d := 2) (by norm_num)
  haveI : IsProbabilityMeasure (walkLaw 2) := by unfold walkLaw; infer_instance
  refine submartingale_of_condExp_sub_nonneg_nat
    (fun i => ((stronglyAdapted_walkFiltration i)).pow 2) integrable_walkPartialSum_sq
    fun i => ?_
  have heq : ((fun p => (walkPartialSum (i + 1) p) ^ 2) - fun p => (walkPartialSum i p) ^ 2)
      = fun p => (walkPartialSum (i + 1) p) ^ 2 - (walkPartialSum i p) ^ 2 := by
    funext p; simp only [Pi.sub_apply]
  rw [heq]
  filter_upwards [condExp_sq_walkPartialSum_sub i] with p hp
  rw [hp]; norm_num

/-- **`E[(S_n)²] ≤ n`**: the second moment of the partial sum, by induction on `n` using the
exact conditional increment and the tower property of conditional expectation. -/
theorem integral_walkPartialSum_sq_le (n : ℕ) :
    ∫ p, (walkPartialSum n p) ^ 2 ∂(walkLaw 2) ≤ n := by
  haveI := stepLaw_isProbability (d := 2) (by norm_num)
  haveI : IsProbabilityMeasure (walkLaw 2) := by unfold walkLaw; infer_instance
  induction n with
  | zero =>
    have : (fun p : ℕ → Fin 2 × Bool => (walkPartialSum 0 p) ^ 2) = fun _ => (0 : ℝ) := by
      funext p; show (walkPartialSum 0 p) ^ 2 = 0
      show (∑ _j ∈ Finset.range 0, walkStepSign (p _j).1) ^ 2 = 0
      simp
    rw [this]; simp
  | succ i ih =>
    have htower := integral_condExp (μ := walkLaw 2)
      (f := fun p => (walkPartialSum (i + 1) p) ^ 2 - (walkPartialSum i p) ^ 2)
      (walkFiltration.le i)
    have hrhs : (∫ p, (walkLaw 2)[fun p => (walkPartialSum (i + 1) p) ^ 2 -
        (walkPartialSum i p) ^ 2 | walkFiltration i] p ∂(walkLaw 2))
        = ∫ _p : ℕ → Fin 2 × Bool, (1 : ℝ) ∂(walkLaw 2) :=
      integral_congr_ae (condExp_sq_walkPartialSum_sub i)
    rw [hrhs] at htower
    haveI : IsProbabilityMeasure (walkLaw 2) := by unfold walkLaw; infer_instance
    rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul,
      mul_one] at htower
    have hsub : (∫ p, ((walkPartialSum (i + 1) p) ^ 2 - (walkPartialSum i p) ^ 2) ∂(walkLaw 2))
        = (∫ p, (walkPartialSum (i + 1) p) ^ 2 ∂(walkLaw 2))
          - ∫ p, (walkPartialSum i p) ^ 2 ∂(walkLaw 2) :=
      integral_sub (integrable_walkPartialSum_sq (i + 1)) (integrable_walkPartialSum_sq i)
    rw [hsub] at htower
    have : (∫ p, (walkPartialSum (i + 1) p) ^ 2 ∂(walkLaw 2))
        = 1 + ∫ p, (walkPartialSum i p) ^ 2 ∂(walkLaw 2) := by linarith
    rw [this]
    push_cast
    linarith

/-- **Doob's maximal inequality for the rescaled walk's coordinate difference, uniform in `n`.**
The event that the partial sum ever exits a window of half-width `4A√n` before time `n` has
probability at most `1/(16A²)`. This is exactly the maximal-displacement tail bound `happ`
needs. -/
theorem measureReal_sup_walkPartialSum_sq_le (n : ℕ) (hn : 1 ≤ n) {A : ℝ} (hA : 0 < A) :
    (walkLaw 2).real {p | ∃ k ≤ n, (4 * A * Real.sqrt n) ≤ |walkPartialSum k p|} ≤
      1 / (16 * A ^ 2) := by
  haveI := stepLaw_isProbability (d := 2) (by norm_num)
  haveI : IsProbabilityMeasure (walkLaw 2) := by unfold walkLaw; infer_instance
  set ε : ℝ≥0 := (16 * A ^ 2 * n : ℝ).toNNReal with hεdef
  have hεcoe : (ε : ℝ) = 16 * A ^ 2 * n := by
    rw [hεdef, Real.coe_toNNReal]
    positivity
  have hmax := maximal_ineq (ε := ε) submartingale_walkPartialSum_sq
    (fun k => fun p => sq_nonneg (walkPartialSum k p)) n
  have hset_eq : {ω : ℕ → Fin 2 × Bool | (ε : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => (walkPartialSum k ω) ^ 2}
      = {p | ∃ k ≤ n, (4 * A * Real.sqrt n) ≤ |walkPartialSum k p|} := by
    ext p
    simp only [Set.mem_setOf_eq]
    rw [Finset.le_sup'_iff]
    constructor
    · rintro ⟨k, hk, hkle⟩
      rw [Finset.mem_range] at hk
      refine ⟨k, by omega, ?_⟩
      have hsqrtn : (0:ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
      have h1 : ((4 * A * Real.sqrt n) : ℝ) ^ 2 ≤ (walkPartialSum k p) ^ 2 := by
        rw [hεcoe] at hkle
        have hn : Real.sqrt (n:ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
        nlinarith [hn]
      have h2 : (0:ℝ) ≤ 4 * A * Real.sqrt n := by positivity
      nlinarith [sq_abs (walkPartialSum k p), abs_nonneg (walkPartialSum k p),
        sq_nonneg (|walkPartialSum k p| - 4 * A * Real.sqrt n)]
    · rintro ⟨k, hk, hkle⟩
      refine ⟨k, by rw [Finset.mem_range]; omega, ?_⟩
      rw [hεcoe]
      have hn : Real.sqrt (n:ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
      nlinarith [sq_abs (walkPartialSum k p), hkle, Real.sqrt_nonneg (n:ℝ),
        mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hA.le) (Real.sqrt_nonneg (n:ℝ))]
  rw [hset_eq] at hmax
  have hbound : (∫ p in {p | ∃ k ≤ n, (4 * A * Real.sqrt n) ≤ |walkPartialSum k p|},
      (walkPartialSum n p) ^ 2 ∂(walkLaw 2)) ≤ (n : ℝ) := by
    calc (∫ p in {p | ∃ k ≤ n, (4 * A * Real.sqrt n) ≤ |walkPartialSum k p|},
          (walkPartialSum n p) ^ 2 ∂(walkLaw 2))
        ≤ ∫ p, (walkPartialSum n p) ^ 2 ∂(walkLaw 2) :=
          setIntegral_le_integral (integrable_walkPartialSum_sq n)
            (Filter.Eventually.of_forall fun p => sq_nonneg _)
      _ ≤ (n : ℝ) := integral_walkPartialSum_sq_le n
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hεpos : (0 : ℝ) < ε := by rw [hεcoe]; positivity
  have h1 : (ε : ℝ≥0∞) * (walkLaw 2) {p | ∃ k ≤ n, (4 * A * Real.sqrt n) ≤ |walkPartialSum k p|}
      ≤ ENNReal.ofReal (n : ℝ) := hmax.trans (ENNReal.ofReal_le_ofReal hbound)
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal (Nat.cast_nonneg n)] at h2
  rw [hεcoe] at h2
  rw [MeasureTheory.measureReal_def]
  have hA2 : (0 : ℝ) < 16 * A ^ 2 := by positivity
  rw [le_div_iff₀ hA2]
  nlinarith [h2, hnpos]

end Parking

end
