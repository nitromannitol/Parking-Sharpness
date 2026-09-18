/- The mass transport identity for the directed walk.

Lemma 3.5 of `parking.tex` is proved in `Parking.mean_activity_eq_survivors` for the law
of the simple random walk.  Its proof uses only three properties of the driving law: the
configuration marginal, the invariance under a translation of the whole data, and the fact
that an instruction is a neighbour of its site.  The directed law has all three, so the
identity `E U_n(0) = ∑_{s<n} S_s` holds for it as well.  That identity, with the
monotonicity of `S`, is what the last paragraph of Step 3 of the proof of
`thm:oriented-walk` (`parking.tex:3324-3331`) uses to pass from the asymptotic of the mean
to the asymptotic of the activity.
-/
import Parking.Support.MassTransport
import Parking.Support.OrientedInvariance
import Parking.Support.OrientedInstructionSupport
import Parking.Support.OrientedLaw
import Parking.Support.JointStopping
import Parking.Support.DensitySequence

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset

variable {d : ℕ}

/-! ### The transport for a general driving law -/

section General

variable {P : Measure (Data d)} {μ : Measure (Site d → ℤ)}

/-- An integrable function of the configuration alone is integrable on the data. -/
theorem integrable_of_conf' (hmap : P.map Prod.fst = μ) {f : (Site d → ℤ) → ℝ}
    (hf : Integrable f μ) : Integrable (fun ω : Data d => f ω.1) P := by
  have h1 : AEStronglyMeasurable f (P.map Prod.fst) := by
    rw [hmap]; exact hf.aestronglyMeasurable
  have h3 : Integrable f (P.map Prod.fst) := by rw [hmap]; exact hf
  exact (integrable_map_measure h1 measurable_fst.aemeasurable).mp h3

/-- Translating the data does not change an integral. -/
theorem integral_comp_shiftData' {v : Site d} (hshift : P.map (shiftData v) = P)
    {F : Data d → ℝ} (hF : AEStronglyMeasurable F P) :
    ∫ ω, F (shiftData v ω) ∂P = ∫ ω, F ω ∂P := by
  have h := integral_map (μ := P) (φ := shiftData v) (f := F)
    (measurable_shiftData v).aemeasurable (by rw [hshift]; exact hF)
  rw [hshift] at h
  exact h.symm

/-- The transported mass is integrable. -/
theorem integrable_sentTo' (hmap : P.map Prod.fst = μ)
    (hconf : ∀ a : Site d, Integrable (fun η : Site d → ℤ => (((η a).toNat : ℕ) : ℝ)) μ)
    (t : ℕ) (a b : Site d) :
    Integrable (fun ω : Data d => (sentTo ω t a b : ℝ)) P :=
  integrable_of_le_nat (measurable_sentTo t a b) (integrable_of_conf' hmap (hconf a))
    fun ω => by exact_mod_cast Nat.cast_le.mpr (sentTo_le ω t a b)

/-- The survivor count is integrable. -/
theorem integrable_survivorsFrom' (hmap : P.map Prod.fst = μ)
    (hconf : ∀ a : Site d, Integrable (fun η : Site d → ℤ => (((η a).toNat : ℕ) : ℝ)) μ)
    (t : ℕ) (a : Site d) :
    Integrable (fun ω : Data d => (survivorsFrom (toDriver ω) t a : ℝ)) P := by
  refine integrable_of_le_nat (measurable_survivorsFrom t a)
    (integrable_of_conf' hmap (hconf a)) fun ω => ?_
  have h : survivorsFrom (toDriver ω) t a ≤ (ω.1 a).toNat := by
    refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
    rw [Finset.card_range]
    exact le_rfl
  exact_mod_cast Nat.cast_le.mpr h

/-- The scenery of a box is integrable. -/
theorem integrable_boxSum' (hmap : P.map Prod.fst = μ)
    (hconf : ∀ a : Site d, Integrable (fun η : Site d → ℤ => (((η a).toNat : ℕ) : ℝ)) μ)
    (x : Site d) (r : ℕ) :
    Integrable (fun ω : Data d => ((∑ y ∈ boxFinset x r, (ω.1 y).toNat : ℕ) : ℝ)) P := by
  have hμ : Integrable
      (fun η : Site d → ℤ => ((∑ y ∈ boxFinset x r, (η y).toNat : ℕ) : ℝ)) μ := by
    have h := integrable_finsetSum (boxFinset x r)
      (fun y (_ : y ∈ boxFinset x r) => hconf y)
    simpa using h
  exact integrable_of_conf' hmap hμ

/-- The activity is integrable. -/
theorem integrable_A' (hmap : P.map Prod.fst = μ)
    (hconf : ∀ a : Site d, Integrable (fun η : Site d → ℤ => (((η a).toNat : ℕ) : ℝ)) μ)
    (t : ℕ) (x : Site d) :
    Integrable (fun ω : Data d => (Parking.A ω t x : ℝ)) P :=
  integrable_of_le_nat (measurable_A t x) (integrable_boxSum' hmap hconf x t)
    fun ω => by exact_mod_cast Nat.cast_le.mpr (activeCount_le ω t x)

/-- **The first identity of `eq:transport` for a general driving law.** -/
theorem mean_activity_eq_survivors' [IsProbabilityMeasure P] (hmap : P.map Prod.fst = μ)
    (hshift : ∀ v : Site d, P.map (shiftData v) = P)
    (hnbr : ∀ᵐ ω ∂P, ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1)
    (hconf : ∀ a : Site d, Integrable (fun η : Site d → ℤ => (((η a).toNat : ℕ) : ℝ)) μ)
    (t : ℕ) :
    ∫ ω, (Parking.A ω t 0 : ℝ) ∂P = Parking.S P t := by
  classical
  have hIsent : ∀ a b : Site d, Integrable (fun ω : Data d => (sentTo ω t a b : ℝ)) P :=
    fun a b => integrable_sentTo' hmap hconf t a b
  have hA : ∫ ω, (Parking.A ω t 0 : ℝ) ∂P
      = ∑ a ∈ boxFinset (0 : Site d) t, ∫ ω, (sentTo ω t a 0 : ℝ) ∂P := by
    rw [← integral_finsetSum _ fun a _ => hIsent a 0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have h := congrArg (fun n : ℕ => (n : ℝ)) (activeCount_eq_sum_sentTo ω t 0)
    push_cast at h
    exact h
  have hSsum : Parking.S P t
      = ∑ b ∈ boxFinset (0 : Site d) t, ∫ ω, (sentTo ω t 0 b : ℝ) ∂P := by
    rw [Parking.S, ← integral_finsetSum _ fun b _ => hIsent 0 b]
    refine integral_congr_ae (hnbr.mono fun ω hω => ?_)
    have h := congrArg (fun n : ℕ => (n : ℝ)) (survivorsFrom_eq_sum_sentTo hω t 0)
    push_cast at h
    exact h
  have htrans : ∀ a : Site d, ∫ ω, (sentTo ω t a 0 : ℝ) ∂P
      = ∫ ω, (sentTo ω t 0 (-a) : ℝ) ∂P := by
    intro a
    have hF : AEStronglyMeasurable (fun ω : Data d => (sentTo ω t a 0 : ℝ)) P :=
      ((measurable_from_countable' fun n : ℕ => (n : ℝ)).comp
        (measurable_sentTo t a 0)).aestronglyMeasurable
    have h := integral_comp_shiftData' (hshift (-a)) hF
    have hrw : ∀ ω : Data d, ((sentTo (shiftData (-a) ω) t a 0 : ℕ) : ℝ)
        = ((sentTo ω t 0 (-a) : ℕ) : ℝ) := by
      intro ω
      rw [sentTo_shiftData, show a + -a = (0 : Site d) by abel,
        show (0 : Site d) + -a = -a by abel]
    simp only [hrw] at h
    exact h.symm
  rw [hA, hSsum, Finset.sum_congr rfl fun a _ => htrans a]
  exact sum_neg_box t fun b : Site d => ∫ ω, (sentTo ω t 0 b : ℝ) ∂P

/-- **The second identity of `eq:transport` for a general driving law.** -/
theorem meanU_eq_sum_S' [IsProbabilityMeasure P] (hmap : P.map Prod.fst = μ)
    (hshift : ∀ v : Site d, P.map (shiftData v) = P)
    (hnbr : ∀ᵐ ω ∂P, ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1)
    (hconf : ∀ a : Site d, Integrable (fun η : Site d → ℤ => (((η a).toNat : ℕ) : ℝ)) μ)
    (n : ℕ) :
    Parking.meanU P n = ∑ s ∈ Finset.range n, Parking.S P s := by
  classical
  have hIA : ∀ s ∈ Finset.range n,
      Integrable (fun ω : Data d => (Parking.A ω s 0 : ℝ)) P :=
    fun s _ => integrable_A' hmap hconf s 0
  have hstep : Parking.meanU P n
      = ∫ ω, (∑ s ∈ Finset.range n, (Parking.A ω s 0 : ℝ)) ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have h := congrArg (fun m : ℕ => (m : ℝ)) (U_eq_sum_A ω n 0)
    push_cast at h
    exact h
  rw [hstep, integral_finsetSum _ hIA]
  exact Finset.sum_congr rfl fun s _ => mean_activity_eq_survivors' hmap hshift hnbr hconf s

end General

/-! ### The directed law -/

/-- The directed instructions are neighbours of their sites. -/
theorem ae_orientedLaw_nbr (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    ∀ᵐ ω ∂(orientedLaw d ν), ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1 := by
  filter_upwards [orientedLaw_ae_forward hd ν] with ω hω q
  obtain ⟨i, hi⟩ := hω q
  rw [hi]
  exact mem_nbrFinset_iff.mpr ⟨i, Or.inl rfl⟩

/-- The positive part of the configuration is integrable at every site under the
directed law's configuration marginal. -/
theorem integrable_toNat_iid (ν : Measure ℤ) (hν : CriticalLaw ν)
    (a : Site d) :
    Integrable (fun η : Site d → ℤ => (((η a).toNat : ℕ) : ℝ)) (iidLaw d ν) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  exact integrable_toNat_eta (fun v => iidLaw_map_shiftConf' ν v)
    (integrable_eval_iid (d := d) ν hν.integrable_abs 0) a

/-- **`E U_n(0) = ∑_{s<n} S_s` for the directed walk.** -/
theorem meanU_eq_sum_S_oriented (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν) (n : ℕ) :
    Parking.meanU (orientedLaw d ν) n
      = ∑ s ∈ Finset.range n, Parking.S (orientedLaw d ν) s := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (orientedLaw d ν) := orientedLaw_isProbability hd ν
  exact meanU_eq_sum_S' (μ := iidLaw d ν) (orientedLaw_map_conf hd ν)
    (fun v => orientedLaw_map_shiftData hd ν v) (ae_orientedLaw_nbr hd ν)
    (integrable_toNat_iid ν hν) n

/-- **The activity of the directed walk decreases.** -/
theorem S_antitone_oriented (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν) :
    Antitone (Parking.S (orientedLaw d ν)) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (orientedLaw d ν) := orientedLaw_isProbability hd ν
  intro s t hst
  exact integral_mono
    (integrable_survivorsFrom' (orientedLaw_map_conf hd ν) (integrable_toNat_iid ν hν) t 0)
    (integrable_survivorsFrom' (orientedLaw_map_conf hd ν) (integrable_toNat_iid ν hν) s 0)
    (fun ω => Nat.cast_le.mpr (survivorsFrom_antitone (toDriver ω) 0 hst))

end Parking
end
