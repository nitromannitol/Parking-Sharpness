/-
The averaged identities of Section 3 of `parking.tex`.

Everything here rests on two facts already available: the pathwise signed count
`A_t(x) - H_t(x) = η(x) + ∑_{y ∼ x} I_{y,x}(U_t(y)) - U_t(x)`, and the
translation equivariance of the process together with the invariance of the law
of the data.  What the equivariance buys is the one identity the paper's proof
needs and that is not pathwise: the expected number of arrivals at the origin
from a neighbour `y` is the expected number of departures from the origin
towards `-y`, so the whole arrival term averages to `E U_t(0)` and cancels the
departure term.

The integrability everything is read against comes from one bound: after `t`
rounds only the particles that started within sup-distance `t` of a site can be
there, so every count in sight is dominated by a finite sum of `η(y)⁺`, whose
mean does not depend on `y`.
-/
import Parking.Support.Invariance
import Parking.Support.Comparison

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-! ### Integrating a function of the configuration alone -/

theorem dataLaw_map_fst (hd : 1 ≤ d) (μ : Measure (Site d → ℤ)) [IsProbabilityMeasure μ] :
    (dataLaw d μ).map Prod.fst = μ := by
  haveI := stackRankLaw_isProbability (d := d) hd
  exact Measure.fst_prod

theorem integrable_of_conf (hd : 1 ≤ d) {μ : Measure (Site d → ℤ)} [IsProbabilityMeasure μ]
    {f : (Site d → ℤ) → ℝ} (hf : Integrable f μ) :
    Integrable (fun ω : Data d => f ω.1) (dataLaw d μ) := by
  have hmap : (dataLaw d μ).map Prod.fst = μ := dataLaw_map_fst hd μ
  have h1 : AEStronglyMeasurable f ((dataLaw d μ).map Prod.fst) := by
    rw [hmap]; exact hf.aestronglyMeasurable
  have h3 : Integrable f ((dataLaw d μ).map Prod.fst) := by rw [hmap]; exact hf
  exact (integrable_map_measure h1 measurable_fst.aemeasurable).mp h3

theorem integral_of_conf (hd : 1 ≤ d) {μ : Measure (Site d → ℤ)} [IsProbabilityMeasure μ]
    {f : (Site d → ℤ) → ℝ} (hf : AEStronglyMeasurable f μ) :
    ∫ ω, f ω.1 ∂(dataLaw d μ) = ∫ η, f η ∂μ := by
  have hmap : (dataLaw d μ).map Prod.fst = μ := dataLaw_map_fst hd μ
  have h := integral_map (μ := dataLaw d μ) (φ := Prod.fst) (f := f)
    measurable_fst.aemeasurable (by rw [hmap]; exact hf)
  rw [hmap] at h
  exact h.symm

/-! ### The mean of the configuration does not depend on the site -/

theorem integrable_comp_shiftConf {μ : Measure (Site d → ℤ)} (hti : TranslationInvariant μ)
    {f : (Site d → ℤ) → ℝ} (hf : Integrable f μ) (v : Site d) :
    Integrable (fun η => f (shiftConf v η)) μ := by
  have hmap : μ.map (shiftConf v) = μ := hti v
  have h1 : AEStronglyMeasurable f (μ.map (shiftConf v)) := by
    rw [hmap]; exact hf.aestronglyMeasurable
  have h3 : Integrable f (μ.map (shiftConf v)) := by rw [hmap]; exact hf
  exact (integrable_map_measure h1 (measurable_shiftConf v).aemeasurable).mp h3

theorem integrable_abs_eta {μ : Measure (Site d → ℤ)} (hti : TranslationInvariant μ)
    (hint : Integrable (fun η : Site d → ℤ => |((η 0 : ℤ) : ℝ)|) μ) (y : Site d) :
    Integrable (fun η : Site d → ℤ => |((η y : ℤ) : ℝ)|) μ := by
  have := integrable_comp_shiftConf hti hint y
  simpa [shiftConf] using this

theorem integrable_toNat_eta {μ : Measure (Site d → ℤ)} [IsProbabilityMeasure μ]
    (hti : TranslationInvariant μ)
    (hint : Integrable (fun η : Site d → ℤ => |((η 0 : ℤ) : ℝ)|) μ) (y : Site d) :
    Integrable (fun η : Site d → ℤ => (((η y).toNat : ℕ) : ℝ)) μ := by
  refine Integrable.mono' (integrable_abs_eta hti hint y) ?_ ?_
  · exact ((measurable_from_countable' fun z : ℤ => ((z.toNat : ℕ) : ℝ)).comp
      (measurable_pi_apply y)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun η => ?_
    have hz : ((η y).toNat : ℤ) ≤ |η y| := by
      rcases abs_cases (η y) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    have : ((η y).toNat : ℝ) ≤ |((η y : ℤ) : ℝ)| := by
      calc ((η y).toNat : ℝ) = (((η y).toNat : ℤ) : ℝ) := by push_cast; ring
        _ ≤ ((|η y| : ℤ) : ℝ) := by exact_mod_cast hz
        _ = |((η y : ℤ) : ℝ)| := by rw [Int.cast_abs]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact this

/-! ### Domination -/

theorem integrable_boxSum (hd : 1 ≤ d) {μ : Measure (Site d → ℤ)} [IsProbabilityMeasure μ]
    (hti : TranslationInvariant μ)
    (hint : Integrable (fun η : Site d → ℤ => |((η 0 : ℤ) : ℝ)|) μ) (x : Site d) (r : ℕ) :
    Integrable (fun ω : Data d => ((∑ y ∈ boxFinset x r, (ω.1 y).toNat : ℕ) : ℝ))
      (dataLaw d μ) := by
  have hμ : Integrable (fun η : Site d → ℤ => ((∑ y ∈ boxFinset x r, (η y).toNat : ℕ) : ℝ)) μ := by
    have := integrable_finsetSum (boxFinset x r)
      (fun y (_ : y ∈ boxFinset x r) => integrable_toNat_eta hti hint y)
    simpa using this
  exact integrable_of_conf hd hμ

theorem integrable_uBound (hd : 1 ≤ d) {μ : Measure (Site d → ℤ)} [IsProbabilityMeasure μ]
    (hti : TranslationInvariant μ)
    (hint : Integrable (fun η : Site d → ℤ => |((η 0 : ℤ) : ℝ)|) μ) (x : Site d) (n : ℕ) :
    Integrable (fun ω : Data d => ((uBound ω.1 n x : ℕ) : ℝ)) (dataLaw d μ) := by
  have : ∀ ω : Data d, ((uBound ω.1 n x : ℕ) : ℝ)
      = ∑ s ∈ Finset.range n, ((∑ y ∈ boxFinset x s, (ω.1 y).toNat : ℕ) : ℝ) := by
    intro ω; rw [uBound]; push_cast; ring
  simp only [this]
  exact integrable_finsetSum _ fun s _ => integrable_boxSum hd hti hint x s

/-- A nonnegative integer-valued measurable observable dominated by an
integrable one is integrable. -/
theorem integrable_of_le_nat {P : Measure (Data d)} {f : Data d → ℕ} {g : Data d → ℝ}
    (hf : Measurable f) (hg : Integrable g P) (hle : ∀ ω, (f ω : ℝ) ≤ g ω) :
    Integrable (fun ω => (f ω : ℝ)) P := by
  refine Integrable.mono' hg ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact ((measurable_from_countable' fun n : ℕ => (n : ℝ)).comp hf).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hle ω

/-! ### Measurability of the arrival counts -/

theorem measurable_arrivalsU (t : ℕ) (y x : Site d) :
    Measurable fun ω : Data d => arrivals ω.2.1 y x (U ω t y) := by
  classical
  refine measurable_of_countable_partition (fun ω : Data d => U ω t y) (measurable_U t y) _
    (fun m ω => arrivals ω.2.1 y x m) (fun m => ?_) fun _ => rfl
  have hsum : ∀ ω : Data d, arrivals ω.2.1 y x m
      = ∑ j ∈ Finset.range m, if ω.2.1 (y, j) = x then 1 else 0 := by
    intro ω; rw [arrivals, Finset.card_filter]
  simp only [hsum]
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (measurable_from_countable' fun z : Site d => if z = x then 1 else 0).comp
    ((measurable_pi_apply (y, j)).comp (measurable_fst.comp measurable_snd))

/-! ### The integrable observables -/

variable {μ : Measure (Site d → ℤ)}

theorem integrable_eta_at (hd : 1 ≤ d) [IsProbabilityMeasure μ]
    (hti : TranslationInvariant μ)
    (hint : Integrable (fun η : Site d → ℤ => |((η 0 : ℤ) : ℝ)|) μ) (y : Site d) :
    Integrable (fun ω : Data d => ((ω.1 y : ℤ) : ℝ)) (dataLaw d μ) := by
  have hμ : Integrable (fun η : Site d → ℤ => ((η y : ℤ) : ℝ)) μ := by
    refine Integrable.mono' (integrable_abs_eta hti hint y) ?_ ?_
    · exact ((measurable_from_countable' fun z : ℤ => ((z : ℤ) : ℝ)).comp
        (measurable_pi_apply y)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun η => le_of_eq (Real.norm_eq_abs _)
  exact integrable_of_conf hd hμ

theorem integrable_A_data (hd : 1 ≤ d) [IsProbabilityMeasure μ]
    (hti : TranslationInvariant μ)
    (hint : Integrable (fun η : Site d → ℤ => |((η 0 : ℤ) : ℝ)|) μ) (t : ℕ) (x : Site d) :
    Integrable (fun ω : Data d => (A ω t x : ℝ)) (dataLaw d μ) :=
  integrable_of_le_nat (measurable_A t x) (integrable_boxSum hd hti hint x t) fun ω => by
    exact_mod_cast Nat.cast_le.mpr (activeCount_le ω t x)

theorem integrable_U_data (hd : 1 ≤ d) [IsProbabilityMeasure μ]
    (hti : TranslationInvariant μ)
    (hint : Integrable (fun η : Site d → ℤ => |((η 0 : ℤ) : ℝ)|) μ) (t : ℕ) (x : Site d) :
    Integrable (fun ω : Data d => (U ω t x : ℝ)) (dataLaw d μ) :=
  integrable_of_le_nat (measurable_U t x) (integrable_uBound hd hti hint x t) fun ω => by
    exact_mod_cast Nat.cast_le.mpr (U_le_uBound ω t x)

theorem integrable_arrivalsU_data (hd : 1 ≤ d) [IsProbabilityMeasure μ]
    (hti : TranslationInvariant μ)
    (hint : Integrable (fun η : Site d → ℤ => |((η 0 : ℤ) : ℝ)|) μ) (t : ℕ) (y x : Site d) :
    Integrable (fun ω : Data d => (arrivals ω.2.1 y x (U ω t y) : ℝ)) (dataLaw d μ) := by
  refine integrable_of_le_nat (measurable_arrivalsU t y x) (integrable_uBound hd hti hint y t)
    fun ω => ?_
  have h1 : arrivals ω.2.1 y x (U ω t y) ≤ U ω t y := by
    refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
    rw [Finset.card_range]
  exact_mod_cast Nat.cast_le.mpr (le_trans h1 (U_le_uBound ω t y))

theorem holeCount_le_initial (ω : Data d) (t : ℕ) (x : Site d) :
    H ω t x ≤ (-(ω.1 x)).toNat := by
  have := holeCount_antitone (toDriver ω) x (Nat.zero_le t)
  exact this

theorem integrable_H_data (hd : 1 ≤ d) [IsProbabilityMeasure μ]
    (hti : TranslationInvariant μ)
    (hint : Integrable (fun η : Site d → ℤ => |((η 0 : ℤ) : ℝ)|) μ) (t : ℕ) (x : Site d) :
    Integrable (fun ω : Data d => (H ω t x : ℝ)) (dataLaw d μ) := by
  have hg : Integrable (fun ω : Data d => |((ω.1 x : ℤ) : ℝ)|) (dataLaw d μ) :=
    integrable_of_conf hd (integrable_abs_eta hti hint x)
  refine integrable_of_le_nat (measurable_H t x) hg fun ω => ?_
  have h1 : ((-(ω.1 x)).toNat : ℤ) ≤ |ω.1 x| := by
    rcases abs_cases (ω.1 x) with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> omega
  have h2 : ((H ω t x : ℕ) : ℤ) ≤ |ω.1 x| :=
    le_trans (Int.ofNat_le.mpr (holeCount_le_initial ω t x)) h1
  calc ((H ω t x : ℕ) : ℝ) = (((H ω t x : ℕ) : ℤ) : ℝ) := by push_cast; ring
    _ ≤ ((|ω.1 x| : ℤ) : ℝ) := by exact_mod_cast h2
    _ = |((ω.1 x : ℤ) : ℝ)| := by rw [Int.cast_abs]

/-! ### Transporting an integral by a translation -/

theorem integral_comp_shiftData (hd : 1 ≤ d) [IsProbabilityMeasure μ]
    (hti : TranslationInvariant μ) (v : Site d)
    {F : Data d → ℝ} (hF : AEStronglyMeasurable F (dataLaw d μ)) :
    ∫ ω, F (shiftData v ω) ∂(dataLaw d μ) = ∫ ω, F ω ∂(dataLaw d μ) := by
  have hmap := dataLaw_map_shiftData hd hti v
  have h := integral_map (μ := dataLaw d μ) (φ := shiftData v) (f := F)
    (measurable_shiftData v).aemeasurable (by rw [hmap]; exact hF)
  rw [hmap] at h
  exact h.symm

theorem arrivals_shiftData (v : Site d) (ω : Data d) (y x : Site d) (m : ℕ) :
    arrivals (shiftData v ω).2.1 y x m = arrivals ω.2.1 (y + v) (x + v) m := by
  classical
  unfold arrivals
  congr 1
  refine Finset.filter_congr fun j _ => ?_
  show ((shiftData v ω).2.1 (y, j) = x) ↔ (ω.2.1 (y + v, j) = x + v)
  show (ω.2.1 (y + v, j) - v = x) ↔ (ω.2.1 (y + v, j) = x + v)
  exact sub_eq_iff_eq_add

theorem arrivalsU_shiftData (v : Site d) (ω : Data d) (t : ℕ) (y x : Site d) :
    arrivals (shiftData v ω).2.1 y x (U (shiftData v ω) t y)
      = arrivals ω.2.1 (y + v) (x + v) (U ω t (y + v)) := by
  rw [arrivals_shiftData, U_shiftData]

/-- The expected number of arrivals at the origin from a neighbour `y` is the
expected number of departures from the origin towards `-y`. -/
theorem integral_arrivals_transport (hd : 1 ≤ d) [IsProbabilityMeasure μ]
    (hti : TranslationInvariant μ) (t : ℕ) (y : Site d) :
    ∫ ω, (arrivals ω.2.1 y 0 (U ω t y) : ℝ) ∂(dataLaw d μ)
      = ∫ ω, (arrivals ω.2.1 0 (-y) (U ω t 0) : ℝ) ∂(dataLaw d μ) := by
  have hF : AEStronglyMeasurable (fun ω : Data d => (arrivals ω.2.1 y 0 (U ω t y) : ℝ))
      (dataLaw d μ) :=
    ((measurable_from_countable' fun n : ℕ => (n : ℝ)).comp
      (measurable_arrivalsU t y 0)).aestronglyMeasurable
  have h := integral_comp_shiftData hd hti (-y) hF
  have hrw : ∀ ω : Data d, (arrivals (shiftData (-y) ω).2.1 y 0 (U (shiftData (-y) ω) t y) : ℝ)
      = (arrivals ω.2.1 0 (-y) (U ω t 0) : ℝ) := by
    intro ω
    rw [arrivalsU_shiftData, show y + -y = (0 : Site d) by abel,
      show (0 : Site d) + -y = -y by abel]
  simp only [hrw] at h
  exact h.symm

/-! ### The arrivals sum to the departures -/

theorem neg_mem_nbrFinset_zero {y : Site d} (hy : y ∈ nbrFinset (0 : Site d)) :
    -y ∈ nbrFinset (0 : Site d) := by
  rw [mem_nbrFinset_iff] at hy ⊢
  obtain ⟨i, hi | hi⟩ := hy
  · exact ⟨i, Or.inr (by rw [hi]; abel)⟩
  · exact ⟨i, Or.inl (by rw [hi]; abel)⟩

theorem nbrFinset_zero_neg :
    (nbrFinset (0 : Site d)).image (fun y => -y) = nbrFinset (0 : Site d) := by
  ext z
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact neg_mem_nbrFinset_zero hy
  · intro hz
    exact ⟨-z, neg_mem_nbrFinset_zero hz, by simp⟩

theorem sum_neg_nbr {M : Type*} [AddCommMonoid M] (f : Site d → M) :
    ∑ y ∈ nbrFinset (0 : Site d), f (-y) = ∑ y ∈ nbrFinset (0 : Site d), f y := by
  classical
  conv_rhs => rw [← nbrFinset_zero_neg]
  rw [Finset.sum_image (fun a _ b _ h => neg_injective h)]

/-- Every departure from a site goes to one of its neighbours, so the
departures split into the arrivals at the neighbours. -/
theorem sum_arrivals_nbr {σ : Site d × ℕ → Site d} (h : ∀ q : Site d × ℕ, σ q ∈ nbrFinset q.1)
    (y : Site d) (m : ℕ) : ∑ x ∈ nbrFinset y, arrivals σ y x m = m := by
  classical
  unfold arrivals
  rw [← Finset.card_eq_sum_card_fiberwise
    (f := fun j : ℕ => σ (y, j)) (t := nbrFinset y) fun j _ => h (y, j), Finset.card_range]

/-! ### The averaged identity -/

theorem ae_stack_nbr (hd : 1 ≤ d) (μ : Measure (Site d → ℤ)) [IsProbabilityMeasure μ] :
    ∀ᵐ ω ∂(dataLaw d μ), ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1 := by
  haveI := stackLaw_isProbability (d := d) hd
  haveI := rankLaw_isProbability d
  have h1 : ∀ᵐ s ∂(stackRankLaw d), ∀ q : Site d × ℕ, s.1 q ∈ nbrFinset q.1 :=
    (Measure.quasiMeasurePreserving_fst).ae (stackLaw_ae_nbr hd)
  exact (Measure.quasiMeasurePreserving_snd).ae h1

/-- Lemma 3.6 of `parking.tex`: the expected activity minus the expected number
of unfilled holes at the origin is the mean of the configuration. -/
theorem activity_holes_main (hd : 1 ≤ d) [IsProbabilityMeasure μ]
    (hti : TranslationInvariant μ)
    (hint : Integrable (fun η : Site d → ℤ => |((η 0 : ℤ) : ℝ)|) μ) (t : ℕ) :
    ∫ ω, (Parking.A ω t 0 : ℝ) ∂(dataLaw d μ)
        - ∫ ω, (Parking.H ω t 0 : ℝ) ∂(dataLaw d μ)
      = ∫ η, ((η 0 : ℤ) : ℝ) ∂μ := by
  classical
  haveI := stackRankLaw_isProbability (d := d) hd
  have hae := ae_stack_nbr hd μ
  have hIA := integrable_A_data hd hti hint t (0 : Site d)
  have hIH := integrable_H_data hd hti hint t (0 : Site d)
  have hIU := integrable_U_data hd hti hint t (0 : Site d)
  have hIe := integrable_eta_at hd hti hint (0 : Site d)
  have hIarr : ∀ y ∈ nbrFinset (0 : Site d),
      Integrable (fun ω : Data d => (arrivals ω.2.1 y 0 (U ω t y) : ℝ)) (dataLaw d μ) :=
    fun y _ => integrable_arrivalsU_data hd hti hint t y 0
  have hsumint : Integrable
      (fun ω : Data d => ∑ y ∈ nbrFinset (0 : Site d), (arrivals ω.2.1 y 0 (U ω t y) : ℝ))
      (dataLaw d μ) := integrable_finsetSum _ hIarr
  have hpath : ∀ᵐ ω ∂(dataLaw d μ), (Parking.A ω t 0 : ℝ) - (Parking.H ω t 0 : ℝ)
      = ((ω.1 0 : ℤ) : ℝ)
        + (∑ y ∈ nbrFinset (0 : Site d), (arrivals ω.2.1 y 0 (U ω t y) : ℝ))
        - (U ω t 0 : ℝ) := by
    refine hae.mono fun ω hω => ?_
    have h := signed_count (ω := ω) hω t 0
    have h' := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at h'
    exact h'
  have hstep : ∫ ω, ((Parking.A ω t 0 : ℝ) - (Parking.H ω t 0 : ℝ)) ∂(dataLaw d μ)
      = ∫ ω, (((ω.1 0 : ℤ) : ℝ)
          + (∑ y ∈ nbrFinset (0 : Site d), (arrivals ω.2.1 y 0 (U ω t y) : ℝ))
          - (U ω t 0 : ℝ)) ∂(dataLaw d μ) := integral_congr_ae hpath
  have hIadd : Integrable (fun ω : Data d => ((ω.1 0 : ℤ) : ℝ)
      + ∑ y ∈ nbrFinset (0 : Site d), (arrivals ω.2.1 y 0 (U ω t y) : ℝ)) (dataLaw d μ) :=
    hIe.add hsumint
  rw [integral_sub hIA hIH, integral_sub hIadd hIU, integral_add hIe hsumint,
    integral_finsetSum _ hIarr] at hstep
  have hkey : ∑ y ∈ nbrFinset (0 : Site d),
      ∫ ω, (arrivals ω.2.1 y 0 (U ω t y) : ℝ) ∂(dataLaw d μ)
      = ∫ ω, (U ω t 0 : ℝ) ∂(dataLaw d μ) := by
    have h1 : ∀ y ∈ nbrFinset (0 : Site d),
        ∫ ω, (arrivals ω.2.1 y 0 (U ω t y) : ℝ) ∂(dataLaw d μ)
          = ∫ ω, (arrivals ω.2.1 0 (-y) (U ω t 0) : ℝ) ∂(dataLaw d μ) :=
      fun y _ => integral_arrivals_transport hd hti t y
    have hIarr' : ∀ y ∈ nbrFinset (0 : Site d),
        Integrable (fun ω : Data d => (arrivals ω.2.1 0 (-y) (U ω t 0) : ℝ)) (dataLaw d μ) :=
      fun y _ => integrable_arrivalsU_data hd hti hint t 0 (-y)
    rw [Finset.sum_congr rfl h1, ← integral_finsetSum _ hIarr']
    refine integral_congr_ae (hae.mono fun ω hω => ?_)
    have hsum : ∑ y ∈ nbrFinset (0 : Site d), (arrivals ω.2.1 0 (-y) (U ω t 0) : ℕ)
        = U ω t 0 := by
      rw [sum_neg_nbr (fun z : Site d => arrivals ω.2.1 0 z (U ω t 0))]
      exact sum_arrivals_nbr hω 0 (U ω t 0)
    have := congrArg (fun n : ℕ => (n : ℝ)) hsum
    push_cast at this
    exact this
  rw [hkey] at hstep
  have hmeas0 : AEStronglyMeasurable (fun η : Site d → ℤ => ((η 0 : ℤ) : ℝ)) μ :=
    ((measurable_from_countable' fun z : ℤ => ((z : ℤ) : ℝ)).comp
      (measurable_pi_apply (0 : Site d))).aestronglyMeasurable
  have hconf : ∫ ω : Data d, ((ω.1 0 : ℤ) : ℝ) ∂(dataLaw d μ) = ∫ η, ((η 0 : ℤ) : ℝ) ∂μ :=
    integral_of_conf hd hmeas0
  rw [hconf] at hstep
  linarith [hstep]

end Parking

end
