/-
The core conditional-expectation facts needed to show `signedM(φ) → 0` in probability, via the
martingale construction of `parking.tex:1758-1766`'s proof from `lem:exposure`
(`Parking.Frozen.exposure`) and `cor:growth` (`Parking.Frozen.growth`).  The filtration is
indexed by ROUNDS, with no shrinking box, unlike `Parking.Support.WMartingale`'s own
construction for a different target.  The argument proceeds by packaging
`single_core`/`double_core` into a countable-partition argument that upgrades a FIXED unread
index `j` to the `expFiltration d k`-measurable RANGE `Finset.Ico (U ω k y) (expOdometer d k ω y)`
the martingale increment of round `k` at site `y` needs, then assembling the round-indexed
martingale-difference sum-of-squares identity and closing with `Parking.Frozen.growth`,
`meanU_shift_invariant` and a box count via Chebyshev.

This file proves, unconditionally (no `External`):
- `walkOp_eq_sum_kern`: `walkOp` as the kernel-weighted sum over the neighbours.
- `single_core_measureReal`/`single_core`: the conditional mean, at a single unread
  instruction `(y,j)`, of a test function read there — `lem:exposure`'s second clause summed
  over the (a.s. finitely many) possible destinations.
- `double_core_measureReal`/`double_core`: the same for the JOINT law of TWO different unread
  instructions (same site or different), giving the cross-covariance-vanishing identity that
  makes the eventual martingale's quadratic variation additive.

The countable-partition assembly tool that upgrades a fixed unread index `j` to the
`expFiltration d k`-measurable RANDOM range this file's own increments need is stated for an
arbitrary probability space with an arbitrary sub-σ-algebra and mentions no object of this
repository's model, so it lives at
`Parking.Generic.CondExpPartition.condExp_of_countable_partition`; apply it with
`m := expFiltration d k`, `hm := expFiltration_le d k`, `μ := law d ν`.
-/
import Parking.Support.ExposureProduct
import Parking.Support.ErrorUnroll
import Parking.Support.UpperTarget
import Parking.Support.Equivariance
import Parking.Support.Invariance
import Parking.Generic.CondExpPartition

open MeasureTheory LatticeProb Finset Filter Topology
open scoped ENNReal

noncomputable section
namespace Parking

variable {d : ℕ}

/-! ### `walkOp` as a kernel sum -/

theorem walkOp_eq_sum_kern (ψ : Site d → ℝ) (y : Site d) :
    walkOp ψ y = ∑ z ∈ nbrFinset y, kern d y z * ψ z := by
  have h1 : (∑ z ∈ nbrFinset y, ψ z) = nbrSum ψ y := sum_nbrFinset_eq y ψ
  show nbrSum ψ y / (2 * d) = _
  rw [← h1, Finset.sum_div]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [kern, if_pos hz]
  ring

/-! ### The single-instruction conditional mean, at measure level -/

theorem single_core_measureReal (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (k : ℕ) (y : Site d) (j : ℕ) (x : Site d)
    {T : Set (Data d)} (hT : MeasurableSet[expFiltration d k] T)
    (hTsub : T ⊆ {ω | U ω k y ≤ j}) :
    (law d ν).real (T ∩ prescribedSet d {(y, j)} (fun _ => x))
      = kern d y x * (law d ν).real T := by
  classical
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  have hTeq : T ∩ unreadSet d k {(y, j)} = T := by
    refine Set.inter_eq_left.mpr fun ω hω q hq => ?_
    simp only [Finset.mem_singleton] at hq; subst hq; exact hTsub hω
  have hcore := exposure_core hd ν k {(y, j)} (fun _ => x) hT
  rw [hTeq] at hcore
  have hprod : (∏ q ∈ ({(y, j)} : Finset (Site d × ℕ)), kern d q.1 ((fun _ : Site d × ℕ => x) q))
      = kern d y x := by simp
  rw [hprod] at hcore
  have hTamb : MeasurableSet T := expFiltration_le d k T hT
  have hcomm : prescribedSet d {(y, j)} (fun _ => x) ∩ T
      = T ∩ prescribedSet d {(y, j)} (fun _ => x) := Set.inter_comm _ _
  rw [hcomm,
    integral_indicator_const (1 : ℝ) (hTamb.inter (measurableSet_prescribedSet _ _)),
    integral_indicator_const (1 : ℝ) hTamb, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at hcore
  exact hcore

/-! ### The two-instruction conditional joint law, at measure level -/

theorem double_core_measureReal (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (k : ℕ) (y y' : Site d) (j j' : ℕ) (hne : (y, j) ≠ (y', j')) (x x' : Site d)
    {T : Set (Data d)} (hT : MeasurableSet[expFiltration d k] T)
    (hTsub : T ⊆ {ω | U ω k y ≤ j} ∩ {ω | U ω k y' ≤ j'}) :
    (law d ν).real (T ∩
        prescribedSet d {(y, j), (y', j')} (fun q => if q = (y, j) then x else x'))
      = kern d y x * kern d y' x' * (law d ν).real T := by
  classical
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  have hTeq : T ∩ unreadSet d k {(y, j), (y', j')} = T := by
    refine Set.inter_eq_left.mpr fun ω hω q hq => ?_
    rw [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact (hTsub hω).1
    · exact (hTsub hω).2
  have hcore := exposure_core hd ν k {(y, j), (y', j')}
    (fun q => if q = (y, j) then x else x') hT
  rw [hTeq] at hcore
  have hprod : (∏ q ∈ ({(y, j), (y', j')} : Finset (Site d × ℕ)),
      kern d q.1 ((fun q => if q = (y, j) then x else x') q)) = kern d y x * kern d y' x' := by
    rw [Finset.prod_pair hne]
    show kern d y (if (y, j) = (y, j) then x else x')
        * kern d y' (if (y', j') = (y, j) then x else x') = kern d y x * kern d y' x'
    rw [if_pos rfl, if_neg (Ne.symm hne)]
  rw [hprod] at hcore
  have hTamb : MeasurableSet T := expFiltration_le d k T hT
  have hcomm : prescribedSet d {(y, j), (y', j')} (fun q => if q = (y, j) then x else x') ∩ T
      = T ∩ prescribedSet d {(y, j), (y', j')} (fun q => if q = (y, j) then x else x') :=
    Set.inter_comm _ _
  rw [hcomm,
    integral_indicator_const (1 : ℝ)
      (hTamb.inter (measurableSet_prescribedSet _ _)),
    integral_indicator_const (1 : ℝ) hTamb, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at hcore
  exact hcore

/-! ### The single-instruction conditional mean, as an integral -/

theorem single_core (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (k : ℕ) (y : Site d) (j : ℕ) (ψ : Site d → ℝ)
    {T : Set (Data d)} (hT : MeasurableSet[expFiltration d k] T)
    (hTsub : T ⊆ {ω | U ω k y ≤ j}) :
    ∫ ω, T.indicator (fun ω => ψ (ω.2.1 (y, j))) ω ∂(law d ν)
      = walkOp ψ y * (law d ν).real T := by
  classical
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  have hTamb : MeasurableSet T := expFiltration_le d k T hT
  have hpt : ∀ᵐ ω ∂(law d ν),
      T.indicator (fun ω => ψ (ω.2.1 (y, j))) ω
        = ∑ x ∈ nbrFinset y,
            (T ∩ prescribedSet d {(y, j)} (fun _ => x)).indicator (fun _ => ψ x) ω := by
    filter_upwards [ae_stack_nbr_law hd ν] with ω hω
    by_cases hωT : ω ∈ T
    · rw [Set.indicator_of_mem hωT]
      have hmem : ω.2.1 (y, j) ∈ nbrFinset y := hω (y, j)
      rw [Finset.sum_eq_single_of_mem (ω.2.1 (y, j)) hmem]
      · have hmem2 : ω ∈ T ∩ prescribedSet d {(y, j)} (fun _ => ω.2.1 (y, j)) := by
          refine ⟨hωT, ?_⟩
          intro q hq; simp only [Finset.mem_singleton] at hq; subst hq; rfl
        exact (Set.indicator_of_mem hmem2 (fun _ => ψ (ω.2.1 (y, j)))).symm
      · intro x _ hne
        apply Set.indicator_of_notMem
        rintro ⟨-, hc⟩
        exact hne ((hc (y, j) (Finset.mem_singleton_self _)).symm)
    · rw [Set.indicator_of_notMem hωT]
      refine (Finset.sum_eq_zero fun x _ => ?_).symm
      apply Set.indicator_of_notMem
      rintro ⟨hc, -⟩
      exact hωT hc
  have hIntegrable : ∀ x ∈ nbrFinset y,
      Integrable (fun ω => (T ∩ prescribedSet d {(y, j)} (fun _ => x)).indicator
        (fun _ => ψ x) ω) (law d ν) :=
    fun x _ => (integrable_const (ψ x)).indicator (hTamb.inter (measurableSet_prescribedSet _ _))
  rw [integral_congr_ae hpt, integral_finsetSum _ hIntegrable]
  have hterm : ∀ x ∈ nbrFinset y,
      ∫ ω, (T ∩ prescribedSet d {(y, j)} (fun _ => x)).indicator (fun _ => ψ x) ω ∂(law d ν)
        = ψ x * (kern d y x * (law d ν).real T) := by
    intro x _
    rw [integral_indicator_const (ψ x) (hTamb.inter (measurableSet_prescribedSet _ _)),
      smul_eq_mul, single_core_measureReal hd ν k y j x hT hTsub]
    ring
  rw [Finset.sum_congr rfl hterm, walkOp_eq_sum_kern, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

/-! ### The two-instruction conditional cross term, as an integral -/

theorem double_core (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (k : ℕ) (y y' : Site d) (j j' : ℕ) (hne : (y, j) ≠ (y', j')) (ψ ψ' : Site d → ℝ)
    {T : Set (Data d)} (hT : MeasurableSet[expFiltration d k] T)
    (hTsub : T ⊆ {ω | U ω k y ≤ j} ∩ {ω | U ω k y' ≤ j'}) :
    ∫ ω, T.indicator (fun ω => ψ (ω.2.1 (y, j)) * ψ' (ω.2.1 (y', j'))) ω ∂(law d ν)
      = walkOp ψ y * walkOp ψ' y' * (law d ν).real T := by
  classical
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  have hTamb : MeasurableSet T := expFiltration_le d k T hT
  have hpt : ∀ᵐ ω ∂(law d ν),
      T.indicator (fun ω => ψ (ω.2.1 (y, j)) * ψ' (ω.2.1 (y', j'))) ω
        = ∑ p ∈ nbrFinset y ×ˢ nbrFinset y',
            (T ∩ prescribedSet d {(y, j), (y', j')}
                (fun q => if q = (y, j) then p.1 else p.2)).indicator
              (fun _ => ψ p.1 * ψ' p.2) ω := by
    filter_upwards [ae_stack_nbr_law hd ν] with ω hω
    by_cases hωT : ω ∈ T
    · rw [Set.indicator_of_mem hωT]
      have hmem : (ω.2.1 (y, j), ω.2.1 (y', j')) ∈ nbrFinset y ×ˢ nbrFinset y' :=
        Finset.mk_mem_product (hω (y, j)) (hω (y', j'))
      rw [Finset.sum_eq_single_of_mem (ω.2.1 (y, j), ω.2.1 (y', j')) hmem]
      · have hmem2 : ω ∈ T ∩ prescribedSet d {(y, j), (y', j')}
            (fun q => if q = (y, j) then ω.2.1 (y, j) else ω.2.1 (y', j')) := by
          refine ⟨hωT, ?_⟩
          intro q hq
          rw [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl
          · show ω.2.1 (y, j) ∈ ({if (y, j) = (y, j) then ω.2.1 (y, j) else ω.2.1 (y', j')} :
              Set (Site d))
            rw [if_pos rfl]; rfl
          · show ω.2.1 (y', j') ∈ ({if (y', j') = (y, j) then ω.2.1 (y, j) else ω.2.1 (y', j')} :
              Set (Site d))
            rw [if_neg (Ne.symm hne)]; rfl
        exact (Set.indicator_of_mem hmem2
          (fun _ => ψ (ω.2.1 (y, j)) * ψ' (ω.2.1 (y', j')))).symm
      · intro p _ hnep
        apply Set.indicator_of_notMem
        rintro ⟨-, hc⟩
        apply hnep
        have h1 : ω.2.1 (y, j) ∈ ({if (y, j) = (y, j) then p.1 else p.2} : Set (Site d)) :=
          hc (y, j) (Finset.mem_insert_self _ _)
        have h2 : ω.2.1 (y', j') ∈ ({if (y', j') = (y, j) then p.1 else p.2} : Set (Site d)) :=
          hc (y', j') (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        rw [if_pos rfl] at h1
        rw [if_neg (Ne.symm hne)] at h2
        exact Prod.ext h1.symm h2.symm
    · rw [Set.indicator_of_notMem hωT]
      refine (Finset.sum_eq_zero fun p _ => ?_).symm
      apply Set.indicator_of_notMem
      rintro ⟨hc, -⟩
      exact hωT hc
  have hIntegrable : ∀ p ∈ nbrFinset y ×ˢ nbrFinset y',
      Integrable (fun ω => (T ∩ prescribedSet d {(y, j), (y', j')}
        (fun q => if q = (y, j) then p.1 else p.2)).indicator (fun _ => ψ p.1 * ψ' p.2) ω)
        (law d ν) :=
    fun p _ => (integrable_const (ψ p.1 * ψ' p.2)).indicator
      (hTamb.inter (measurableSet_prescribedSet _ _))
  rw [integral_congr_ae hpt, integral_finsetSum _ hIntegrable]
  have hterm : ∀ p ∈ nbrFinset y ×ˢ nbrFinset y',
      ∫ ω, (T ∩ prescribedSet d {(y, j), (y', j')}
          (fun q => if q = (y, j) then p.1 else p.2)).indicator (fun _ => ψ p.1 * ψ' p.2) ω
          ∂(law d ν)
        = ψ p.1 * ψ' p.2 * (kern d y p.1 * kern d y' p.2 * (law d ν).real T) := by
    intro p hp
    rw [Finset.mem_product] at hp
    rw [integral_indicator_const (ψ p.1 * ψ' p.2)
        (hTamb.inter (measurableSet_prescribedSet _ _)),
      smul_eq_mul, double_core_measureReal hd ν k y y' j j' hne p.1 p.2 hT hTsub]
    ring
  rw [Finset.sum_congr rfl hterm]
  have hval : (∑ p ∈ nbrFinset y ×ˢ nbrFinset y',
        ψ p.1 * ψ' p.2 * (kern d y p.1 * kern d y' p.2 * (law d ν).real T))
      = (∑ x ∈ nbrFinset y, kern d y x * ψ x)
          * (∑ x' ∈ nbrFinset y', kern d y' x' * ψ' x') * (law d ν).real T := by
    rw [Finset.sum_product, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x' _ => ?_
    show ψ x * ψ' x' * (kern d y x * kern d y' x' * (law d ν).real T)
        = kern d y x * ψ x * (kern d y' x' * ψ' x') * (law d ν).real T
    ring
  rw [hval, walkOp_eq_sum_kern ψ y, walkOp_eq_sum_kern ψ' y']

/-! ### `E[U_n(y)]` does not depend on the site `y` -/

/-- **The mean particle odometer does not depend on the site.**  From `U`'s translation
covariance (`Parking.U_shiftData`) and the pushforward invariance of the i.i.d. law under a
spatial shift (`Parking.law_map_shiftData`), the same shift-invariance argument
`Parking.law_discrepancy_shift` uses for the discrepancy event. -/
theorem meanU_shift_invariant (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (n : ℕ) (z : Site d) :
    ∫ ω, (U ω n z : ℝ) ∂(law d ν) = meanU (law d ν) n := by
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  have hmeas : Measurable fun ω : Data d => (U ω n z : ℝ) :=
    (measurable_from_countable' (fun m : ℕ => (m : ℝ))).comp (measurable_U n z)
  have hmap : (law d ν).map (shiftData (-z)) = law d ν := law_map_shiftData hd ν (-z)
  have h1 : ∫ ω, (U ω n z : ℝ) ∂(law d ν)
      = ∫ ω, (U ω n z : ℝ) ∂((law d ν).map (shiftData (-z))) := by rw [hmap]
  rw [h1, integral_map (measurable_shiftData (-z)).aemeasurable hmeas.aestronglyMeasurable]
  have h2 : ∀ ω : Data d, (U (shiftData (-z) ω) n z : ℝ) = (U ω n (0 : Site d) : ℝ) := by
    intro ω
    rw [U_shiftData (-z) ω n z]
    norm_num
  simp_rw [h2]
  rfl

end Parking

end
