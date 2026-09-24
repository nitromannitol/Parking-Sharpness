/-
**The `L^q`-moment form of the two-point, two-time concentration of `V`.**  The tail bound
`Parking.exists_linPotential_increment_concentration`
(`Parking/Support/LinIncrementConcentration.lean`) is a Bernstein-shaped tail bound, not
the `L^q`-moment bound that `Parking.Support.SpatField`'s Kolmogorov moment hypothesis needs
and `Parking.External.UConcentration` carries for `u`; this file proves the `L^q`-moment
bound for `V`.  `Parking.Support.SubGaussianMoment` supplies the general "tail-to-moment"
conversion (`weighted_exp_conc_Lq`, the `L^q`-moment analogue of the library's own
`LatticeProb.weighted_exp_conc_tail`); this file applies it to `V` through the SAME
finite-marginal reindexing bridge (`FinsetReindex.lean`, `LinBox.lean`) that the tail form
uses, reusing its norm computations.  The resulting bound is

    (∫ |(V_n(x) − V_m(y)) − E[V_n(x) − V_m(y)]|^q)^(1/q)
      ≤ C · (√q · ‖g_n(x−·) − g_m(y−·)‖₂ + q · ‖g_n(x−·) − g_m(y−·)‖_∞)

for every `q ≥ 1`, with ONE constant `C` uniform in `n, m, x, y, q` — the exact shape of
`Parking.External.UConcentration`, but PROVED for the linear field `V`, not cited.
-/
import Parking.Support.LinIncrementConcentration
import Parking.Support.SubGaussianMoment

noncomputable section

namespace Parking

open LatticeProb Finset MeasureTheory

variable {d : ℕ}

/-- **The `L^q`-moment bound for the two-point, two-time increment of `V`.**  PROVED,
not cited: the `L^q`-moment form (`Parking.weighted_exp_conc_Lq`) of the same
finite-marginal transport of `Parking.linIncrement_update`'s EXACT per-coordinate
response that `Parking.exists_linPotential_increment_concentration` uses for the tail
form. -/
theorem exists_linPotential_increment_moment (hd : 1 ≤ d) (ν0 : Measure ℝ)
    [IsProbabilityMeasure ν0] (θ : ℝ) (hθ : 0 < θ)
    (hexp : Integrable (fun z : ℝ => Real.exp (θ * |z|)) ν0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (x y : Site d) (q : ℝ), 1 ≤ q →
      (∫ η, |(linPotential η n x - linPotential η m y)
            - ∫ η', (linPotential η' n x - linPotential η' m y) ∂(iidLaw d ν0)| ^ q
          ∂(iidLaw d ν0)) ^ (1 / q)
        ≤ C * (Real.sqrt q * l2Norm (fun z => green d n (x - z) - green d m (y - z))
            + q * supAbs (fun z => green d n (x - z) - green d m (y - z))) := by
  obtain ⟨C, hC, hmain⟩ := weighted_exp_conc_Lq θ (∫ z, Real.exp (θ * |z|) ∂ν0) hθ
  refine ⟨C, hC, ?_⟩
  intro n m x y q hq
  have hq0 : 0 < q := by linarith
  set s : Finset (Site d) := linIncrementBox n m x y with hsdef
  have hrestrict : ∀ η : Site d → ℝ,
      linPotential η n x - linPotential η m y = linIncrement s n m x y (s.restrict η) :=
    fun η => (linIncrement_restrict n m x y η).symm
  have hmeasR : Measurable (s.restrict : (Site d → ℝ) → (s → ℝ)) :=
    measurable_pi_lambda _ fun k => measurable_pi_apply (k : Site d)
  have hFcont : Continuous (linIncrement s n m x y) :=
    (lipschitzWith_linPotential_extendField hd s n x).continuous.sub
      (lipschitzWith_linPotential_extendField hd s m y).continuous
  have hFm : Measurable (linIncrement s n m x y) := hFcont.measurable
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
    have hbound := hmain N ν0 inferInstance hexp le_rfl F' hF'm ℓ' hℓ'nonneg hℓ'ne hLip' q hq
    have hmean' : (∫ ξ, F' ξ ∂(Measure.pi fun _ : Fin N => ν0)) = mu :=
      integral_finEquivIndex_comp ν0 (linIncrement s n m x y)
    rw [hmean'] at hbound
    have hgcont : Continuous (fun ζ : s → ℝ => |linIncrement s n m x y ζ - mu| ^ q) :=
      ((hFcont.sub continuous_const).abs).rpow_const (fun _ => Or.inr hq0.le)
    have hgm : Measurable (fun ζ : s → ℝ => |linIncrement s n m x y ζ - mu| ^ q) :=
      hgcont.measurable
    have hgcongr : (∫ η, |(linPotential η n x - linPotential η m y)
          - ∫ η', (linPotential η' n x - linPotential η' m y) ∂(iidLaw d ν0)| ^ q
        ∂(iidLaw d ν0))
        = ∫ η, |linIncrement s n m x y (s.restrict η) - mu| ^ q ∂(iidLaw d ν0) := by
      apply integral_congr_ae
      filter_upwards with η
      rw [hrestrict η, hmean]
    have htransport : (∫ η, |linIncrement s n m x y (s.restrict η) - mu| ^ q ∂(iidLaw d ν0))
        = ∫ ζ, |linIncrement s n m x y ζ - mu| ^ q ∂(Measure.pi fun _ : s => ν0) := by
      rw [← iidLaw_map_restrict d ν0 s,
        integral_map hmeasR.aemeasurable hgm.aestronglyMeasurable]
    have hreindex : (∫ ζ, |linIncrement s n m x y ζ - mu| ^ q ∂(Measure.pi fun _ : s => ν0))
        = ∫ ξ, |F' ξ - mu| ^ q ∂(Measure.pi fun _ : Fin N => ν0) :=
      (integral_finEquivIndex_comp ν0
        (fun ζ : s → ℝ => |linIncrement s n m x y ζ - mu| ^ q)).symm
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
    rw [hgcongr, htransport, hreindex, hnorm2, hnormInf]
    exact hbound
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
    have hl2zero : l2Norm (fun z => green d n (x - z) - green d m (y - z)) = 0 := by
      unfold l2Norm
      have : (fun z => (green d n (x - z) - green d m (y - z)) ^ 2) = fun _ => (0:ℝ) := by
        funext z; rw [hzall z]; ring
      rw [this]
      simp
    have hInfzero : supAbs (fun z => green d n (x - z) - green d m (y - z)) = 0 := by
      unfold supAbs
      have : (fun z => |green d n (x - z) - green d m (y - z)|) = fun _ => (0:ℝ) := by
        funext z; rw [hzall z]; simp
      rw [this]
      exact ciSup_const
    have hintzero : (∫ η, |(linPotential η n x - linPotential η m y)
          - ∫ η', (linPotential η' n x - linPotential η' m y) ∂(iidLaw d ν0)| ^ q
        ∂(iidLaw d ν0)) = 0 := by
      have hzero : ∀ η, |(linPotential η n x - linPotential η m y)
          - ∫ η', (linPotential η' n x - linPotential η' m y) ∂(iidLaw d ν0)| ^ q = 0 := by
        intro η
        rw [hallη η, hmean0, sub_self, abs_zero, Real.zero_rpow hq0.ne']
      simp only [hzero]
      exact integral_zero _ _
    rw [hintzero, hl2zero, hInfzero, Real.zero_rpow (by positivity : (1:ℝ) / q ≠ 0)]
    positivity

end Parking

end
