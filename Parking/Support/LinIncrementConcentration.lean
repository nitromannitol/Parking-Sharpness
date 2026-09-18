/-
**The two-point, two-time concentration of the linear membrane field `V`**
(`Parking.linPotential`), PROVED (not cited) through the shared library's weighted
exponential concentration (`LatticeProb.weighted_exp_conc_tail`,
`LatticeProb.Prob.WeightedConc`), with the finite-marginal bridge the library needs
(`Parking.Support.FinsetReindex`, `Parking.Support.LinBox`).

This is the route that `parking.tex:1745-1747`'s own phrase "heat-kernel bounds and bounds
on translated kernel differences" describes for the LINEAR field, and it is the input that
BouRabeePanagiotis2026's Proposition 4.3 (the joint space-time convergence of the linear
membrane field) uses.  `Parking.linPotential_update` gives the EXACT (not merely one-sided)
coordinatewise response of `V` to a single scenery value, so `V_n(x;η) - V_m(y;η)`,
restricted to any finite box containing the supports of both `green d n (x - ·)` and
`green d m (y - ·)`, is an EXACTLY coordinate-Lipschitz function with influence vector
`z ↦ |green d n (x - z) - green d m (y - z)|`, and `LatticeProb.weighted_exp_conc_tail`
applies to it directly.
-/
import Parking.Support.LinBox
import Parking.Support.FinsetReindex
import LatticeProb.Prob.WeightedConc
import LatticeProb.Walk.GreenPointwise

noncomputable section

namespace Parking

open LatticeProb Finset MeasureTheory

variable {d : ℕ}

/-! ### The finite-box increment of `V` and its exact per-coordinate response -/

/-- The two-point, two-time increment of `V`, read on a finite box `s`. -/
def linIncrement (s : Finset (Site d)) (n m : ℕ) (x y : Site d) (ζ : s → ℝ) : ℝ :=
  linPotential (extendField s ζ) n x - linPotential (extendField s ζ) m y

/-- The influence vector of `Parking.linIncrement`: the translated-kernel difference of
`parking.tex:1745-1747`. -/
def linIncrementWeight (s : Finset (Site d)) (n m : ℕ) (x y : Site d) (i : s) : ℝ :=
  |green d n (x - (i : Site d)) - green d m (y - (i : Site d))|

theorem linIncrementWeight_nonneg (s : Finset (Site d)) (n m : ℕ) (x y : Site d) (i : s) :
    0 ≤ linIncrementWeight s n m x y i := abs_nonneg _

theorem measurable_linIncrement (hd : 1 ≤ d) (s : Finset (Site d)) (n m : ℕ) (x y : Site d) :
    Measurable (linIncrement s n m x y) :=
  ((lipschitzWith_linPotential_extendField hd s n x).continuous.sub
    (lipschitzWith_linPotential_extendField hd s m y).continuous).measurable

/-- **The exact coordinatewise response of the increment.**  From
`Parking.linPotential_update` applied at both `(n,x)` and `(m,y)`, transported through
`Parking.extendField_update`.  There is no "max instead of difference" obstruction, because
`V` is exactly linear. -/
theorem linIncrement_update (s : Finset (Site d)) (n m : ℕ) (x y : Site d)
    (ζ : s → ℝ) (i : s) (v : ℝ) :
    linIncrement s n m x y (Function.update ζ i v) - linIncrement s n m x y ζ
      = (v - ζ i) * (green d n (x - (i : Site d)) - green d m (y - (i : Site d))) := by
  unfold linIncrement
  rw [extendField_update]
  have hζi : extendField s ζ (i : Site d) = ζ i := by
    unfold extendField
    rw [dif_pos i.2]
  have h1 := linPotential_update (extendField s ζ) n x (i : Site d) v
  have h2 := linPotential_update (extendField s ζ) m y (i : Site d) v
  rw [hζi] at h1 h2
  linear_combination h1 - h2

/-- **The exact Lipschitz bound `LatticeProb.weighted_exp_conc_tail` needs.** -/
theorem abs_linIncrement_update_le (s : Finset (Site d)) (n m : ℕ) (x y : Site d)
    (ζ : s → ℝ) (i : s) (v : ℝ) :
    |linIncrement s n m x y ζ - linIncrement s n m x y (Function.update ζ i v)|
      = linIncrementWeight s n m x y i * |ζ i - v| := by
  have h := linIncrement_update s n m x y ζ i v
  have heq : linIncrement s n m x y ζ - linIncrement s n m x y (Function.update ζ i v)
      = (ζ i - v) * (green d n (x - (i : Site d)) - green d m (y - (i : Site d))) := by
    linarith
  rw [heq, abs_mul, linIncrementWeight, mul_comm]

/-! ### The box of the finite-marginal bridge, and vanishing of the weight outside it -/

/-- The box `s` of the finite-marginal bridge: large enough to contain the support of both
`green d n (x - ·)` and `green d m (y - ·)`. -/
def linIncrementBox (n m : ℕ) (x y : Site d) : Finset (Site d) :=
  boxFinset x n ∪ boxFinset y m

theorem boxFinset_x_subset_linIncrementBox (n m : ℕ) (x y : Site d) :
    boxFinset x n ⊆ linIncrementBox n m x y := Finset.subset_union_left

theorem boxFinset_y_subset_linIncrementBox (n m : ℕ) (x y : Site d) :
    boxFinset y m ⊆ linIncrementBox n m x y := Finset.subset_union_right

theorem green_eq_zero_of_not_mem_boxFinset {n : ℕ} {x z : Site d} (hz : z ∉ boxFinset x n) :
    green d n (x - z) = 0 := by
  refine green_eq_zero_of_le ?_
  have hsup : n < supNorm (z - x) := by
    by_contra hc
    have hc' : supNorm (z - x) ≤ n := not_lt.mp hc
    apply hz
    rw [mem_boxFinset_iff]
    intro i
    have h := supNorm_le_iff.mp hc' i
    simpa using h
  have heq : supNorm (x - z) = supNorm (z - x) := by
    unfold supNorm
    refine Finset.sup_congr rfl (fun i _ => ?_)
    have hswap : (z - x) i = -((x - z) i) := by simp only [Pi.sub_apply]; ring
    rw [hswap, Int.natAbs_neg]
  have hle : supNorm (x - z) ≤ graphNorm (x - z) := supNorm_le_graphNorm (x - z)
  omega

theorem linIncrementWeight_eq_zero_of_not_mem (n m : ℕ) (x y : Site d) {z : Site d}
    (hz : z ∉ linIncrementBox n m x y) :
    green d n (x - z) - green d m (y - z) = 0 := by
  unfold linIncrementBox at hz
  rw [Finset.mem_union, not_or] at hz
  rw [green_eq_zero_of_not_mem_boxFinset hz.1, green_eq_zero_of_not_mem_boxFinset hz.2]
  ring

/-- `V` at `(n,x)` and at `(m,y)`, read on `Parking.linIncrementBox`, reproduces the true
values on the infinite lattice. -/
theorem linIncrement_restrict (n m : ℕ) (x y : Site d) (η : Site d → ℝ) :
    linIncrement (linIncrementBox n m x y) n m x y
        ((linIncrementBox n m x y).restrict η)
      = linPotential η n x - linPotential η m y := by
  unfold linIncrement
  rw [← linPotential_eq_extendField_of_boxFinset_subset
      (boxFinset_x_subset_linIncrementBox n m x y) η,
    ← linPotential_eq_extendField_of_boxFinset_subset
      (boxFinset_y_subset_linIncrementBox n m x y) η]

/-! ### The concentration theorem -/

/-- **The two-point, two-time concentration of `V`.**  PROVED, not cited: the finite-marginal
transport of `LatticeProb.weighted_exp_conc_tail` along `Parking.linIncrement_update`'s EXACT
per-coordinate response. -/
theorem exists_linPotential_increment_concentration (hd : 1 ≤ d) (ν0 : Measure ℝ)
    [IsProbabilityMeasure ν0] (θ : ℝ) (hθ : 0 < θ)
    (hexp : Integrable (fun z : ℝ => Real.exp (θ * |z|)) ν0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n m : ℕ) (x y : Site d) (r : ℝ), 0 < r →
      (iidLaw d ν0)
          {η | r ≤ |(linPotential η n x - linPotential η m y)
              - ∫ η', (linPotential η' n x - linPotential η' m y) ∂(iidLaw d ν0)|}
        ≤ ENNReal.ofReal (C * Real.exp (-(c *
            min (r ^ 2 / (l2Norm (fun z => green d n (x - z) - green d m (y - z))) ^ 2)
              (r / supAbs (fun z => green d n (x - z) - green d m (y - z)))))) := by
  obtain ⟨c, C, hc, hC, hmain⟩ :=
    weighted_exp_conc_tail θ (∫ z, Real.exp (θ * |z|) ∂ν0) hθ
  refine ⟨c, C, hc, hC, ?_⟩
  intro n m x y r hr
  set s : Finset (Site d) := linIncrementBox n m x y with hsdef
  have hrestrict : ∀ η : Site d → ℝ,
      linPotential η n x - linPotential η m y = linIncrement s n m x y (s.restrict η) :=
    fun η => (linIncrement_restrict n m x y η).symm
  have hmeasR : Measurable (s.restrict : (Site d → ℝ) → (s → ℝ)) :=
    measurable_pi_lambda _ fun k => measurable_pi_apply (k : Site d)
  have hFm : Measurable (linIncrement s n m x y) := measurable_linIncrement hd s n m x y
  set mu : ℝ := ∫ ζ, linIncrement s n m x y ζ ∂(Measure.pi fun _ : s => ν0) with hmudef
  have hmean : (∫ η', (linPotential η' n x - linPotential η' m y) ∂(iidLaw d ν0)) = mu := by
    have hcongr : (∫ η', (linPotential η' n x - linPotential η' m y) ∂(iidLaw d ν0))
        = ∫ η', linIncrement s n m x y (s.restrict η') ∂(iidLaw d ν0) :=
      integral_congr_ae (Filter.Eventually.of_forall hrestrict)
    rw [hcongr, hmudef, ← iidLaw_map_restrict d ν0 s,
      integral_map hmeasR.aemeasurable hFm.aestronglyMeasurable]
  by_cases hex : ∃ i : s, linIncrementWeight s n m x y i ≠ 0
  · classical
    set N := Fintype.card s with hNdef
    set e := finEquivIndex s with hedef
    set F' : (Fin N → ℝ) → ℝ := (linIncrement s n m x y) ∘ e with hF'def
    set ℓ' : Fin N → ℝ :=
        fun j => linIncrementWeight s n m x y ((Fintype.equivFin s).symm j)
      with hℓ'def
    have hF'm : Measurable F' := hFm.comp measurable_finEquivIndex
    have hℓ'nonneg : ∀ j, 0 ≤ ℓ' j := fun j => linIncrementWeight_nonneg s n m x y _
    have hℓ'ne : ∃ j, ℓ' j ≠ 0 := by
      obtain ⟨i0, hi0⟩ := hex
      exact ⟨Fintype.equivFin s i0, by
        simp only [hℓ'def, Equiv.symm_apply_apply]; exact hi0⟩
    have hLip' : ∀ (ξ : Fin N → ℝ) (j : Fin N) (v : ℝ),
        |F' ξ - F' (Function.update ξ j v)| ≤ ℓ' j * |ξ j - v| := by
      intro ξ j v
      have hupd : e (Function.update ξ j v)
          = Function.update (e ξ) ((Fintype.equivFin s).symm j) v :=
        finEquivIndex_update ξ j v
      have heval : e ξ ((Fintype.equivFin s).symm j) = ξ j := by
        rw [finEquivIndex_apply, Equiv.apply_symm_apply]
      have hkey := abs_linIncrement_update_le s n m x y (e ξ) ((Fintype.equivFin s).symm j) v
      rw [heval] at hkey
      show |F' ξ - linIncrement s n m x y (e (Function.update ξ j v))| ≤ _
      rw [hupd]
      exact le_of_eq hkey
    have hbound := hmain N ν0 inferInstance hexp le_rfl F' hF'm ℓ' hℓ'nonneg hℓ'ne hLip' r hr.le
    have hmean' : (∫ ξ, F' ξ ∂(Measure.pi fun _ : Fin N => ν0)) = mu :=
      integral_finEquivIndex_comp ν0 (linIncrement s n m x y)
    rw [hmean'] at hbound
    have hpre : e ⁻¹' {ζ | r ≤ |linIncrement s n m x y ζ - mu|}
      = {ξ | r ≤ |F' ξ - mu|} := rfl
    have hTmeas : MeasurableSet {ζ : s → ℝ | r ≤ |linIncrement s n m x y ζ - mu|} :=
      measurableSet_le measurable_const (hFm.sub measurable_const).abs
    have hboxstep : (Measure.pi fun _ : s => ν0) {ζ | r ≤ |linIncrement s n m x y ζ - mu|}
        ≤ ENNReal.ofReal (C * Real.exp (-(c * min (r ^ 2 / lTwoNorm ℓ' ^ 2)
            (r / lInfNorm ℓ')))) := by
      rw [← measure_preimage_finEquivIndex ν0 hTmeas, hpre]
      exact hbound
    have hiid : (iidLaw d ν0)
          {η | r ≤ |(linPotential η n x - linPotential η m y)
              - ∫ η', (linPotential η' n x - linPotential η' m y) ∂(iidLaw d ν0)|}
        = (Measure.pi fun _ : s => ν0) {ζ | r ≤ |linIncrement s n m x y ζ - mu|} := by
      have hset : {η | r ≤ |(linPotential η n x - linPotential η m y)
            - ∫ η', (linPotential η' n x - linPotential η' m y) ∂(iidLaw d ν0)|}
          = s.restrict ⁻¹' {ζ | r ≤ |linIncrement s n m x y ζ - mu|} := by
        ext η
        simp only [Set.mem_setOf_eq, Set.mem_preimage]
        rw [hrestrict η, hmean]
      rw [hset, ← iidLaw_map_restrict d ν0 s, Measure.map_apply hmeasR hTmeas]
    have hnorm2 : l2Norm (fun z => green d n (x - z) - green d m (y - z)) = lTwoNorm ℓ' := by
      unfold l2Norm lTwoNorm
      congr 1
      have hzero : ∀ z ∉ s, (green d n (x - z) - green d m (y - z)) ^ 2 = 0 := fun z hz => by
        rw [linIncrementWeight_eq_zero_of_not_mem n m x y hz]; ring
      rw [tsum_eq_sum hzero,
        ← Finset.sum_coe_sort s (fun z => (green d n (x - z) - green d m (y - z)) ^ 2)]
      refine Fintype.sum_equiv (Fintype.equivFin s)
        (fun i : s => (green d n (x - (i : Site d)) - green d m (y - (i : Site d))) ^ 2)
        (fun j => ℓ' j ^ 2) (fun i => ?_)
      show (green d n (x - (i : Site d)) - green d m (y - (i : Site d))) ^ 2
        = linIncrementWeight s n m x y ((Fintype.equivFin s).symm (Fintype.equivFin s i)) ^ 2
      rw [Equiv.symm_apply_apply, linIncrementWeight, sq_abs]
    have hne' : s.Nonempty := by
      obtain ⟨i0, _⟩ := hex; exact ⟨(i0 : Site d), i0.2⟩
    haveI : Nonempty s := ⟨⟨hne'.choose, hne'.choose_spec⟩⟩
    have hnormInf : supAbs (fun z => green d n (x - z) - green d m (y - z)) = lInfNorm ℓ' := by
      unfold supAbs lInfNorm
      have hfnn : ∀ z : Site d, 0 ≤ |green d n (x - z) - green d m (y - z)| := fun z => abs_nonneg _
      have hfz : ∀ z ∉ s, |green d n (x - z) - green d m (y - z)| = 0 := fun z hz => by
        rw [linIncrementWeight_eq_zero_of_not_mem n m x y hz]; simp
      rw [ciSup_eq_ciSup_subtype_of_forall_not_mem_eq_zero hfnn hfz hne']
      have hbdd1 : BddAbove (Set.range ℓ') := Finite.bddAbove_range _
      have hbdd2 : BddAbove (Set.range (fun i : s =>
          |green d n (x - (i : Site d)) - green d m (y - (i : Site d))|)) :=
        Finite.bddAbove_range _
      refine le_antisymm (ciSup_le fun i => ?_) (ciSup_le fun j => ?_)
      · have hi : |green d n (x - (i : Site d)) - green d m (y - (i : Site d))|
            = ℓ' (Fintype.equivFin s i) := by
          simp only [hℓ'def, linIncrementWeight, Equiv.symm_apply_apply]
        rw [hi]; exact le_ciSup hbdd1 _
      · have hj : ℓ' j = |green d n (x - ((Fintype.equivFin s).symm j : Site d))
              - green d m (y - ((Fintype.equivFin s).symm j : Site d))| := by
          simp only [hℓ'def, linIncrementWeight]
        rw [hj]; exact le_ciSup hbdd2 _
    rw [hiid, hnorm2, hnormInf]
    exact hboxstep
  · have hex' : ∀ i : s, linIncrementWeight s n m x y i = 0 := fun i =>
      not_not.mp (not_exists.mp hex i)
    have hzall : ∀ z : Site d, green d n (x - z) - green d m (y - z) = 0 := by
      intro z
      by_cases hzs : z ∈ s
      · exact abs_eq_zero.mp (hex' ⟨z, hzs⟩)
      · exact linIncrementWeight_eq_zero_of_not_mem n m x y hzs
    have hupdconst : ∀ (ζ : s → ℝ) (i : s) (v : ℝ),
        linIncrement s n m x y (Function.update ζ i v) = linIncrement s n m x y ζ := by
      intro ζ i v
      have h := linIncrement_update s n m x y ζ i v
      rw [hzall (i : Site d), mul_zero] at h
      linarith
    have hchange : ∀ (t : Finset s) (ζ ζ' : s → ℝ),
        linIncrement s n m x y (fun i => if i ∈ t then ζ' i else ζ i)
          = linIncrement s n m x y ζ := by
      intro t
      induction t using Finset.induction_on with
      | empty => intro ζ ζ'; simp
      | @insert a t hat ih =>
          intro ζ ζ'
          have heq1 : (fun i => if i ∈ insert a t then ζ' i else ζ i)
              = Function.update (fun i => if i ∈ t then ζ' i else ζ i) a (ζ' a) := by
            funext i
            by_cases hia : i = a
            · subst hia; simp
            · simp [Finset.mem_insert, hia]
          rw [heq1, hupdconst]
          exact ih ζ ζ'
    have hconst : ∀ ζ ζ' : s → ℝ, linIncrement s n m x y ζ' = linIncrement s n m x y ζ := by
      intro ζ ζ'
      have h := hchange Finset.univ ζ ζ'
      simpa using h
    obtain ⟨ζ0, -⟩ : ∃ ζ0 : s → ℝ, True := ⟨fun _ => 0, trivial⟩
    have hallη : ∀ η : Site d → ℝ,
        linPotential η n x - linPotential η m y = linIncrement s n m x y ζ0 := by
      intro η
      rw [hrestrict η]
      exact hconst ζ0 (s.restrict η)
    have hmean0 : (∫ η', (linPotential η' n x - linPotential η' m y) ∂(iidLaw d ν0))
        = linIncrement s n m x y ζ0 := by
      haveI : IsProbabilityMeasure (iidLaw d ν0) := by unfold iidLaw; infer_instance
      rw [integral_congr_ae (Filter.Eventually.of_forall hallη), integral_const, probReal_univ,
        one_smul]
    have hempty : {η | r ≤ |(linPotential η n x - linPotential η m y)
          - ∫ η', (linPotential η' n x - linPotential η' m y) ∂(iidLaw d ν0)|} = ∅ := by
      ext η
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rw [hallη η, hmean0, sub_self, abs_zero]
      exact not_le.mpr hr
    rw [hempty, measure_empty]
    exact bot_le

end Parking

end
