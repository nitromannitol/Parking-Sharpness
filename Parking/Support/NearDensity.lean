/-
The lower bound of `thm:near` above dimension three (`parking.tex:2896-2912`).

"For `d ≥ 4`, take independent copies across sites of the coupling in
Theorem 1.7.  Applying Lemma 3.7 first to `min{η_δ, η_0}` and then to
`max{η_δ, η_0}` gives `S_t^δ ≥ S_t^0 - E|η_δ(0) - η_0(0)| ≥ S_t^0 - Cδ`."

The coupling of the two fields is the field of independent copies of the
one-site coupling, read through two coordinatewise maps.  Its marginals are the
two independent fields because a coordinatewise map of an independent field is
the independent field of the mapped law; it is invariant under the diagonal
translation because a coordinatewise map commutes with the translation; and the
field of minima is below each marginal at every site, which is the monotone
coupling `lem:density-compare` asks for.  One application of that lemma bounds
the survivor count of the minimum below the survivor count of the law of mean
`-δ`, and a second bounds the survivor count at the critical law above it by the
difference of the two means, which is at most the mean coupling distance because
`η_0(0) - min{η_δ(0), η_0(0)} ≤ |η_δ(0) - η_0(0)|` pointwise.
-/
import Parking.Frozen.DensityCompare
import Parking.Frozen.CriticalDensity
import Parking.Support.Near
import Parking.Support.CriticalChain
import Parking.Support.JointStopping

open MeasureTheory LatticeProb
open scoped ENNReal

noncomputable section
namespace Parking
variable {d : ℕ}

/-- A field of pairs read through a coordinatewise map. -/
def pairField (F : ℤ × ℤ → ℤ) (c : Site d → ℤ × ℤ) : Site d → ℤ := fun x => F (c x)

theorem measurable_pairField (F : ℤ × ℤ → ℤ) : Measurable (pairField (d := d) F) :=
  measurable_pi_lambda _ fun x =>
    (measurable_from_countable' F).comp (measurable_pi_apply x)

/-- The coupling of two configuration fields read off independent copies of a
one-site coupling `π` through two coordinatewise maps. -/
def pairCoupling (d : ℕ) (π : Measure (ℤ × ℤ)) (F G : ℤ × ℤ → ℤ) :
    Measure ((Site d → ℤ) × (Site d → ℤ)) :=
  (LatticeProb.iidLaw d π).map (fun c => (pairField F c, pairField G c))

theorem measurable_pairPair (F G : ℤ × ℤ → ℤ) :
    Measurable (fun c : Site d → ℤ × ℤ => (pairField F c, pairField G c)) :=
  (measurable_pairField F).prodMk (measurable_pairField G)

theorem pairCoupling_isProbability (π : Measure (ℤ × ℤ)) [IsProbabilityMeasure π]
    (F G : ℤ × ℤ → ℤ) : IsProbabilityMeasure (pairCoupling d π F G) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d π) := by
    unfold LatticeProb.iidLaw; infer_instance
  exact Measure.isProbabilityMeasure_map (measurable_pairPair F G).aemeasurable

theorem pairCoupling_map_fst (π : Measure (ℤ × ℤ)) [IsProbabilityMeasure π]
    (F G : ℤ × ℤ → ℤ) :
    (pairCoupling d π F G).map Prod.fst = LatticeProb.iidLaw d (π.map F) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d π) := by
    unfold LatticeProb.iidLaw; infer_instance
  rw [pairCoupling, Measure.map_map measurable_fst (measurable_pairPair F G)]
  exact LatticeProb.iidLaw_map_pi d π (measurable_from_countable' F)

theorem pairCoupling_map_snd (π : Measure (ℤ × ℤ)) [IsProbabilityMeasure π]
    (F G : ℤ × ℤ → ℤ) :
    (pairCoupling d π F G).map Prod.snd = LatticeProb.iidLaw d (π.map G) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d π) := by
    unfold LatticeProb.iidLaw; infer_instance
  rw [pairCoupling, Measure.map_map measurable_snd (measurable_pairPair F G)]
  exact LatticeProb.iidLaw_map_pi d π (measurable_from_countable' G)

theorem pairCoupling_translationInvariant (π : Measure (ℤ × ℤ))
    [IsProbabilityMeasure π] (F G : ℤ × ℤ → ℤ) (v : Site d) :
    (pairCoupling d π F G).map
        (fun c => (Parking.shiftConf v c.1, Parking.shiftConf v c.2))
      = pairCoupling d π F G := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d π) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hshift : Measurable (fun c : Site d → ℤ × ℤ => fun x => c (x + v)) :=
    measurable_pi_lambda _ fun x => measurable_pi_apply (x + v)
  have hmeasT : Measurable
      (fun p : (Site d → ℤ) × (Site d → ℤ) =>
        (Parking.shiftConf v p.1, Parking.shiftConf v p.2)) := by
    refine Measurable.prodMk ?_ ?_
    · exact (measurable_pi_lambda _ fun x => measurable_pi_apply (x + v)).comp measurable_fst
    · exact (measurable_pi_lambda _ fun x => measurable_pi_apply (x + v)).comp measurable_snd
  rw [pairCoupling, Measure.map_map hmeasT (measurable_pairPair F G)]
  have hcomp : (fun p : (Site d → ℤ) × (Site d → ℤ) =>
        (Parking.shiftConf v p.1, Parking.shiftConf v p.2))
      ∘ (fun c : Site d → ℤ × ℤ => (pairField F c, pairField G c))
      = (fun c : Site d → ℤ × ℤ => (pairField F c, pairField G c))
        ∘ (fun c : Site d → ℤ × ℤ => fun x => c (x + v)) := rfl
  rw [hcomp, ← Measure.map_map (measurable_pairPair F G) hshift,
    LatticeProb.iidLaw_map_shiftConf π v]

theorem pairCoupling_mono (π : Measure (ℤ × ℤ)) [IsProbabilityMeasure π]
    {F G : ℤ × ℤ → ℤ} (h : ∀ p : ℤ × ℤ, F p ≤ G p) :
    ∀ᵐ c ∂(pairCoupling d π F G), ∀ x, c.1 x ≤ c.2 x := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d π) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hset : MeasurableSet {p : (Site d → ℤ) × (Site d → ℤ) | ∀ x, p.1 x ≤ p.2 x} := by
    have : {p : (Site d → ℤ) × (Site d → ℤ) | ∀ x, p.1 x ≤ p.2 x}
        = ⋂ x : Site d, {p : (Site d → ℤ) × (Site d → ℤ) | p.1 x ≤ p.2 x} := by
      ext p; simp
    rw [this]
    refine MeasurableSet.iInter fun x => ?_
    exact measurableSet_le ((measurable_pi_apply x).comp measurable_fst)
      ((measurable_pi_apply x).comp measurable_snd)
  rw [pairCoupling]
  refine (ae_map_iff (measurable_pairPair F G).aemeasurable hset).mpr ?_
  exact Filter.Eventually.of_forall fun c x => h (c x)


/-- The coordinatewise minimum of a coupled pair. -/
def minPair (p : ℤ × ℤ) : ℤ := min p.1 p.2

theorem minPair_le_fst (p : ℤ × ℤ) : minPair p ≤ p.1 := min_le_left _ _

theorem minPair_le_snd (p : ℤ × ℤ) : minPair p ≤ p.2 := min_le_right _ _

theorem abs_minPair_le (p : ℤ × ℤ) :
    |((minPair p : ℤ) : ℝ)| ≤ |((p.1 : ℤ) : ℝ)| + |((p.2 : ℤ) : ℝ)| := by
  rcases min_choice p.1 p.2 with h | h <;> rw [minPair, h]
  · have := abs_nonneg (((p.2 : ℤ) : ℝ)); linarith
  · have := abs_nonneg (((p.1 : ℤ) : ℝ)); linarith

theorem snd_sub_minPair_le (p : ℤ × ℤ) :
    ((p.2 : ℤ) : ℝ) - ((minPair p : ℤ) : ℝ) ≤ |((p.1 : ℤ) : ℝ) - ((p.2 : ℤ) : ℝ)| := by
  rcases le_total p.1 p.2 with h | h
  · rw [minPair, min_eq_left h]
    have hc : ((p.1 : ℤ) : ℝ) ≤ ((p.2 : ℤ) : ℝ) := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [minPair, min_eq_right h]
    simp [abs_nonneg]

/-- Integrating a function of one coordinate of an independent field. -/
theorem integral_eval_iid {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {f : α → ℝ} (hf : AEStronglyMeasurable f ν) (z : Site d) :
    ∫ η, f (η z) ∂(LatticeProb.iidLaw d ν) = ∫ a, f a ∂ν := by
  have hmap : (LatticeProb.iidLaw d ν).map (fun η : Site d → α => η z) = ν :=
    Measure.infinitePi_map_eval _ z
  have h := integral_map (μ := LatticeProb.iidLaw d ν) (φ := fun η : Site d → α => η z)
    (f := f) (measurable_pi_apply z).aemeasurable (by rw [hmap]; exact hf)
  rw [hmap] at h
  exact h.symm

/-- **`S_t` at a law of mean `-δ` against `S_t` at the critical law**
(`parking.tex:2900-2907`).  Applying `lem:density-compare` to the coordinatewise
minimum of the coupled fields, first against one marginal and then against the
other, costs only the mean of the coupling distance. -/
theorem S_sub_couplingCost_le (hd : 1 ≤ d) (nd0 nc : Measure ℤ)
    [IsProbabilityMeasure nd0] [IsProbabilityMeasure nc]
    (hintd : Integrable (fun k : ℤ => |(k : ℝ)|) nd0)
    (hint0 : Integrable (fun k : ℤ => |(k : ℝ)|) nc)
    (pi : Measure (ℤ × ℤ)) (hpi : IsProbabilityMeasure pi)
    (hfst : pi.map Prod.fst = nd0) (hsnd : pi.map Prod.snd = nc) (t : ℕ) :
    Parking.S (Parking.law d nc) t - ∫ p, |((p.1 : ℤ) : ℝ) - ((p.2 : ℤ) : ℝ)| ∂pi
      ≤ Parking.S (Parking.law d nd0) t := by
  haveI := hpi
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d pi) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI hpd : IsProbabilityMeasure (LatticeProb.iidLaw d nd0) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI hpc : IsProbabilityMeasure (LatticeProb.iidLaw d nc) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hmnmeas : Measurable minPair := measurable_from_countable' minPair
  haveI hpm : IsProbabilityMeasure (pi.map minPair) :=
    Measure.isProbabilityMeasure_map hmnmeas.aemeasurable
  haveI hpim : IsProbabilityMeasure (LatticeProb.iidLaw d (pi.map minPair)) := by
    unfold LatticeProb.iidLaw; infer_instance
  -- integrability of the two coordinates and of the minimum under the coupling
  have hI1 : Integrable (fun p : ℤ × ℤ => |((p.1 : ℤ) : ℝ)|) pi := by
    refine (integrable_map_measure (g := fun k : ℤ => |(k : ℝ)|) (f := (Prod.fst : ℤ × ℤ → ℤ))
      (by rw [hfst]; exact hintd.aestronglyMeasurable) measurable_fst.aemeasurable).mp ?_
    rw [hfst]; exact hintd
  have hI2 : Integrable (fun p : ℤ × ℤ => |((p.2 : ℤ) : ℝ)|) pi := by
    refine (integrable_map_measure (g := fun k : ℤ => |(k : ℝ)|) (f := (Prod.snd : ℤ × ℤ → ℤ))
      (by rw [hsnd]; exact hint0.aestronglyMeasurable) measurable_snd.aemeasurable).mp ?_
    rw [hsnd]; exact hint0
  have hIm : Integrable (fun p : ℤ × ℤ => |((minPair p : ℤ) : ℝ)|) pi := by
    refine Integrable.mono' (hI1.add hI2)
      (measurable_from_countable' (fun p : ℤ × ℤ => |((minPair p : ℤ) : ℝ)|)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact abs_minPair_le p
  have hIdiff : Integrable (fun p : ℤ × ℤ => |((p.1 : ℤ) : ℝ) - ((p.2 : ℤ) : ℝ)|) pi := by
    refine Integrable.mono' (hI1.add hI2)
      (measurable_from_countable' (fun p : ℤ × ℤ =>
        |((p.1 : ℤ) : ℝ) - ((p.2 : ℤ) : ℝ)|)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact abs_sub _ _
  have hmint : Integrable (fun k : ℤ => |(k : ℝ)|) (pi.map minPair) :=
    (integrable_map_measure (g := fun k : ℤ => |(k : ℝ)|) (f := minPair)
      (measurable_from_countable' (fun k : ℤ => |(k : ℝ)|)).aestronglyMeasurable
      hmnmeas.aemeasurable).mpr hIm
  -- the same integrability in the field
  have hcfg : ∀ (lam : Measure ℤ), IsProbabilityMeasure lam →
      Integrable (fun k : ℤ => |(k : ℝ)|) lam →
      Integrable (fun eta : Site d → ℤ => |((eta 0 : ℤ) : ℝ)|) (LatticeProb.iidLaw d lam) := by
    intro lam hp hint
    haveI := hp
    exact integrable_eval_iid (d := d) lam hint 0
  have hmeanbridge : ∀ (lam : Measure ℤ), IsProbabilityMeasure lam →
      ∫ eta, ((eta 0 : ℤ) : ℝ) ∂(LatticeProb.iidLaw d lam) = ∫ k, (k : ℝ) ∂lam := by
    intro lam hp
    haveI := hp
    exact integral_eval_iid (d := d) lam
      (measurable_from_countable' (fun k : ℤ => (k : ℝ))).aestronglyMeasurable 0
  have hlaweq : ∀ lam : Measure ℤ,
      Parking.law d lam = Parking.dataLaw d (LatticeProb.iidLaw d lam) := fun _ => rfl
  have hintmap : ∀ F : ℤ × ℤ → ℤ, ∫ k, (k : ℝ) ∂(pi.map F) = ∫ p, ((F p : ℤ) : ℝ) ∂pi := by
    intro F
    exact integral_map (measurable_from_countable' F).aemeasurable
      (measurable_from_countable' (fun k : ℤ => (k : ℝ))).aestronglyMeasurable
  -- the minimum against the first marginal
  have happ1 := Parking.Frozen.density_compare d hd
    (LatticeProb.iidLaw d (pi.map minPair)) (LatticeProb.iidLaw d nd0) hpim hpd
    (hcfg _ hpm hmint) (hcfg _ inferInstance hintd)
    (pairCoupling d pi minPair Prod.fst)
    (pairCoupling_isProbability pi minPair Prod.fst)
    (pairCoupling_map_fst pi minPair Prod.fst)
    (by rw [pairCoupling_map_snd pi minPair Prod.fst, hfst])
    (fun v => pairCoupling_translationInvariant pi minPair Prod.fst v)
    (pairCoupling_mono pi (fun p => minPair_le_fst p)) t
  -- the minimum against the second marginal
  have happ2 := Parking.Frozen.density_compare d hd
    (LatticeProb.iidLaw d (pi.map minPair)) (LatticeProb.iidLaw d nc) hpim hpc
    (hcfg _ hpm hmint) (hcfg _ inferInstance hint0)
    (pairCoupling d pi minPair Prod.snd)
    (pairCoupling_isProbability pi minPair Prod.snd)
    (pairCoupling_map_fst pi minPair Prod.snd)
    (by rw [pairCoupling_map_snd pi minPair Prod.snd, hsnd])
    (fun v => pairCoupling_translationInvariant pi minPair Prod.snd v)
    (pairCoupling_mono pi (fun p => minPair_le_snd p)) t
  have h1 : Parking.S (Parking.dataLaw d (LatticeProb.iidLaw d (pi.map minPair))) t
      ≤ Parking.S (Parking.dataLaw d (LatticeProb.iidLaw d nd0)) t := by linarith [happ1.2.2.1]
  have h2 : Parking.S (Parking.dataLaw d (LatticeProb.iidLaw d nc)) t
        - Parking.S (Parking.dataLaw d (LatticeProb.iidLaw d (pi.map minPair))) t
      ≤ ∫ k, (k : ℝ) ∂nc - ∫ k, (k : ℝ) ∂(pi.map minPair) := by
    have h := happ2.2.2.2
    rw [hmeanbridge nc inferInstance, hmeanbridge (pi.map minPair) hpm] at h
    exact h
  have h3 : ∫ k, (k : ℝ) ∂nc - ∫ k, (k : ℝ) ∂(pi.map minPair)
      ≤ ∫ p, |((p.1 : ℤ) : ℝ) - ((p.2 : ℤ) : ℝ)| ∂pi := by
    have hc : nc = pi.map Prod.snd := hsnd.symm
    rw [hc, hintmap Prod.snd, hintmap minPair]
    have hI2' : Integrable (fun p : ℤ × ℤ => ((p.2 : ℤ) : ℝ)) pi := by
      refine Integrable.mono' hI2
        (measurable_from_countable' (fun p : ℤ × ℤ => ((p.2 : ℤ) : ℝ))).aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => ?_)
      rw [Real.norm_eq_abs]
    have hIm' : Integrable (fun p : ℤ × ℤ => ((minPair p : ℤ) : ℝ)) pi := by
      refine Integrable.mono' hIm
        (measurable_from_countable' (fun p : ℤ × ℤ => ((minPair p : ℤ) : ℝ))).aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => ?_)
      rw [Real.norm_eq_abs]
    rw [← integral_sub hI2' hIm']
    exact integral_mono (hI2'.sub hIm') hIdiff fun p => snd_sub_minPair_le p
  rw [hlaweq nd0, hlaweq nc]
  linarith

end Parking
end
