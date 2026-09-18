/-
The mass transport principle of `parking.tex` Lemma 3.5.

Send every particle that is still active after round `t` from its starting site
to where it stands.  Write `sentTo ω t a b` for the mass that goes from `a` to
`b`.  Then the mass received at a site is its activity and the mass sent from a
site is its survivor count:

    A_t(b) = ∑_a sentTo t a b,    survivorsFrom t a = ∑_b sentTo t a b,

both sums being over a box of radius `t`, because after `t` rounds a particle
is within sup-distance `t` of where it started.  The transport is equivariant,
`sentTo (shiftData v ω) t a b = sentTo ω t (a + v) (b + v)`, and the law of the
data is translation invariant, so the expected mass received at the origin is
the expected mass sent from it.  That is `E A_t(0) = S_t`; summing it over the
rounds gives `E U_n(0) = ∑_{s < n} S_s`.
-/
import Parking.Support.ActivityHoles

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-- The particles that started at `a`, are still active after round `t`, and
stand at `b`. -/
def sentTo (ω : Data d) (t : ℕ) (a b : Site d) : ℕ :=
  ((Finset.range (ω.1 a).toNat).filter fun i =>
    (state (toDriver ω) t).active (a, i) ∧ (state (toDriver ω) t).pos (a, i) = b).card

theorem sentTo_le (ω : Data d) (t : ℕ) (a b : Site d) : sentTo ω t a b ≤ (ω.1 a).toNat := by
  refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
  rw [Finset.card_range]

/-! ### The mass received -/

/-- A count over the candidates of a site splits into the counts over the
particles that started at each site of the box. -/
theorem card_filter_candidates_eq_sum (η : Site d → ℤ) (z : Site d) (r : ℕ)
    (P : Label d → Prop) [DecidablePred P] :
    ((candidates η z r).filter P).card
      = ∑ a ∈ boxFinset z r, ((Finset.range (η a).toNat).filter fun i => P (a, i)).card := by
  classical
  have hmem : ∀ p ∈ (candidates η z r).filter P, p.1 ∈ boxFinset z r := by
    intro p hp
    have := mem_candidates_iff.mp (Finset.mem_filter.mp hp).1
    exact mem_boxFinset_iff.mpr this.1
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hset : (((candidates η z r).filter P).filter fun p => p.1 = a)
      = ((Finset.range (η a).toNat).filter fun i => P (a, i)).map
        ⟨fun i => (a, i), by intro u v h; simpa using h⟩ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_range,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨hc, hP⟩, hfst⟩
      refine ⟨p.2, ⟨?_, ?_⟩, ?_⟩
      · have := (mem_candidates_iff.mp hc).2
        rwa [hfst] at this
      · rwa [← hfst, Prod.mk.eta]
      · rw [← hfst, Prod.mk.eta]
    · rintro ⟨i, ⟨hi, hP⟩, rfl⟩
      refine ⟨⟨mem_candidates (mem_boxFinset_iff.mp ha) hi, hP⟩, rfl⟩
  rw [hset, Finset.card_map]

/-- The activity at a site is the mass received there. -/
theorem activeCount_eq_sum_sentTo (ω : Data d) (t : ℕ) (b : Site d) :
    Parking.A ω t b = ∑ a ∈ boxFinset b t, sentTo ω t a b := by
  classical
  show (activeAt (toDriver ω) (state (toDriver ω) t) t b).card = _
  rw [activeAt, card_filter_candidates_eq_sum]
  rfl

/-! ### The mass sent -/

/-- The survivor count of a site is the mass sent from it. -/
theorem survivorsFrom_eq_sum_sentTo {ω : Data d}
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1) (t : ℕ) (a : Site d) :
    survivorsFrom (toDriver ω) t a = ∑ b ∈ boxFinset a t, sentTo ω t a b := by
  classical
  have hD : StepsToNeighbour (toDriver ω) := stepsToNeighbour_of_mem hstep
  have hmem : ∀ i ∈ (Finset.range ((toDriver ω).eta a).toNat).filter
      (fun i => (state (toDriver ω) t).active (a, i) = true),
      (state (toDriver ω) t).pos (a, i) ∈ boxFinset a t := by
    intro i _
    refine mem_boxFinset_iff.mpr fun j => ?_
    exact abs_pos_sub_start_le hD t (a, i) j
  rw [survivorsFrom, Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sentTo, Finset.filter_filter]
  rfl

/-! ### The transport is equivariant -/

theorem sentTo_shiftData (v : Site d) (ω : Data d) (t : ℕ) (a b : Site d) :
    sentTo (shiftData v ω) t a b = sentTo ω t (a + v) (b + v) := by
  classical
  have hS := state_shiftData v ω t
  unfold sentTo
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  have hact := hS.active (a, i)
  have hpos := hS.pos (a, i)
  simp only [shiftLabel] at hact hpos
  constructor
  · rintro ⟨hi, h1, h2⟩
    refine ⟨hi, ?_, ?_⟩
    · rw [← hact]; exact h1
    · rw [hpos] at h2; exact sub_eq_iff_eq_add.mp h2
  · rintro ⟨hi, h1, h2⟩
    refine ⟨hi, ?_, ?_⟩
    · rw [hact]; exact h1
    · rw [hpos]; exact sub_eq_iff_eq_add.mpr h2

/-! ### The box is symmetric -/

theorem neg_mem_boxFinset_zero {r : ℕ} {x : Site d} (hx : x ∈ boxFinset (0 : Site d) r) :
    -x ∈ boxFinset (0 : Site d) r := by
  rw [mem_boxFinset_iff] at hx ⊢
  intro i
  have := hx i
  simpa [abs_sub_comm] using this

theorem boxFinset_zero_neg (r : ℕ) :
    (boxFinset (0 : Site d) r).image (fun x => -x) = boxFinset (0 : Site d) r := by
  ext z
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact neg_mem_boxFinset_zero hx
  · intro hz
    exact ⟨-z, neg_mem_boxFinset_zero hz, by simp⟩

theorem sum_neg_box {M : Type*} [AddCommMonoid M] (r : ℕ) (f : Site d → M) :
    ∑ x ∈ boxFinset (0 : Site d) r, f (-x) = ∑ x ∈ boxFinset (0 : Site d) r, f x := by
  classical
  conv_rhs => rw [← boxFinset_zero_neg r]
  rw [Finset.sum_image (fun a _ b _ h => neg_injective h)]

/-! ### Measurability and integrability of the transport -/

theorem measurable_sentTo (t : ℕ) (a b : Site d) :
    Measurable fun ω : Data d => sentTo ω t a b := by
  classical
  obtain ⟨hact, hpos, -, -⟩ := measurable_state (d := d) t
  refine measurable_of_countable_partition (fun ω : Data d => (ω.1 a).toNat)
    ((measurable_from_countable' fun z : ℤ => z.toNat).comp
      ((measurable_pi_apply a).comp measurable_fst)) _
    (fun N ω => ((Finset.range N).filter fun i =>
      (state (toDriver ω) t).active (a, i) ∧ (state (toDriver ω) t).pos (a, i) = b).card)
    (fun N => ?_) fun _ => rfl
  have hsum : ∀ ω : Data d, ((Finset.range N).filter fun i =>
      (state (toDriver ω) t).active (a, i) ∧ (state (toDriver ω) t).pos (a, i) = b).card
      = ∑ i ∈ Finset.range N, if (state (toDriver ω) t).active (a, i)
          ∧ (state (toDriver ω) t).pos (a, i) = b then 1 else 0 := by
    intro ω; rw [Finset.card_filter]
  simp only [hsum]
  refine Finset.measurable_sum _ fun i _ => ?_
  have hfun : (fun ω : Data d => if ((state (toDriver ω) t).active (a, i) = true)
        ∧ (state (toDriver ω) t).pos (a, i) = b then (1 : ℕ) else 0)
      = fun ω : Data d => (fun z : Bool × Site d =>
          if z.1 = true ∧ z.2 = b then (1 : ℕ) else 0)
        ((state (toDriver ω) t).active (a, i), (state (toDriver ω) t).pos (a, i)) := by
    funext ω; rfl
  rw [hfun]
  exact (measurable_from_countable' fun z : Bool × Site d =>
    if z.1 = true ∧ z.2 = b then (1 : ℕ) else 0).comp ((hact (a, i)).prodMk (hpos (a, i)))

variable {μ : Measure (Site d → ℤ)}

theorem integrable_sentTo (hd : 1 ≤ d) [IsProbabilityMeasure μ]
    (hti : TranslationInvariant μ)
    (hint : Integrable (fun η : Site d → ℤ => |((η 0 : ℤ) : ℝ)|) μ) (t : ℕ) (a b : Site d) :
    Integrable (fun ω : Data d => (sentTo ω t a b : ℝ)) (dataLaw d μ) := by
  refine integrable_of_le_nat (measurable_sentTo t a b)
    (integrable_of_conf hd (integrable_toNat_eta hti hint a)) fun ω => ?_
  exact_mod_cast Nat.cast_le.mpr (sentTo_le ω t a b)

theorem integrable_survivorsFrom_data (hd : 1 ≤ d) [IsProbabilityMeasure μ]
    (hti : TranslationInvariant μ)
    (hint : Integrable (fun η : Site d → ℤ => |((η 0 : ℤ) : ℝ)|) μ) (t : ℕ) (a : Site d) :
    Integrable (fun ω : Data d => (survivorsFrom (toDriver ω) t a : ℝ)) (dataLaw d μ) := by
  refine integrable_of_le_nat (measurable_survivorsFrom t a)
    (integrable_of_conf hd (integrable_toNat_eta hti hint a)) fun ω => ?_
  have h : survivorsFrom (toDriver ω) t a ≤ (ω.1 a).toNat := by
    refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
    rw [Finset.card_range]
    exact le_rfl
  exact_mod_cast Nat.cast_le.mpr h

/-! ### The mass transport identity -/

/-- The first identity of `eq:transport`: the expected activity at the origin is
the expected number of particles that started there and are still active. -/
theorem mean_activity_eq_survivors (hd : 1 ≤ d) [IsProbabilityMeasure μ]
    (hti : TranslationInvariant μ)
    (hint : Integrable (fun η : Site d → ℤ => |((η 0 : ℤ) : ℝ)|) μ) (t : ℕ) :
    ∫ ω, (Parking.A ω t 0 : ℝ) ∂(dataLaw d μ) = Parking.S (dataLaw d μ) t := by
  classical
  haveI := stackRankLaw_isProbability (d := d) hd
  have hae := ae_stack_nbr hd μ
  have hIsent : ∀ a b : Site d,
      Integrable (fun ω : Data d => (sentTo ω t a b : ℝ)) (dataLaw d μ) :=
    fun a b => integrable_sentTo hd hti hint t a b
  -- the received mass
  have hA : ∫ ω, (Parking.A ω t 0 : ℝ) ∂(dataLaw d μ)
      = ∑ a ∈ boxFinset (0 : Site d) t, ∫ ω, (sentTo ω t a 0 : ℝ) ∂(dataLaw d μ) := by
    rw [← integral_finsetSum _ fun a _ => hIsent a 0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have := congrArg (fun n : ℕ => (n : ℝ)) (activeCount_eq_sum_sentTo ω t 0)
    push_cast at this
    exact this
  -- the sent mass
  have hS : Parking.S (dataLaw d μ) t
      = ∑ b ∈ boxFinset (0 : Site d) t, ∫ ω, (sentTo ω t 0 b : ℝ) ∂(dataLaw d μ) := by
    rw [Parking.S, ← integral_finsetSum _ fun b _ => hIsent 0 b]
    refine integral_congr_ae (hae.mono fun ω hω => ?_)
    have := congrArg (fun n : ℕ => (n : ℝ)) (survivorsFrom_eq_sum_sentTo hω t 0)
    push_cast at this
    exact this
  -- the transport
  have htrans : ∀ a : Site d, ∫ ω, (sentTo ω t a 0 : ℝ) ∂(dataLaw d μ)
      = ∫ ω, (sentTo ω t 0 (-a) : ℝ) ∂(dataLaw d μ) := by
    intro a
    have hF : AEStronglyMeasurable (fun ω : Data d => (sentTo ω t a 0 : ℝ)) (dataLaw d μ) :=
      ((measurable_from_countable' fun n : ℕ => (n : ℝ)).comp
        (measurable_sentTo t a 0)).aestronglyMeasurable
    have h := integral_comp_shiftData hd hti (-a) hF
    have hrw : ∀ ω : Data d, ((sentTo (shiftData (-a) ω) t a 0 : ℕ) : ℝ)
        = ((sentTo ω t 0 (-a) : ℕ) : ℝ) := by
      intro ω
      rw [sentTo_shiftData, show a + -a = (0 : Site d) by abel,
        show (0 : Site d) + -a = -a by abel]
    simp only [hrw] at h
    exact h.symm
  rw [hA, hS, Finset.sum_congr rfl fun a _ => htrans a]
  exact sum_neg_box t fun b : Site d => ∫ ω, (sentTo ω t 0 b : ℝ) ∂(dataLaw d μ)

/-- The second identity of `eq:transport`: the expected odometer at the origin
is the sum of the survivor counts over the rounds. -/
theorem meanU_eq_sum_S (hd : 1 ≤ d) [IsProbabilityMeasure μ]
    (hti : TranslationInvariant μ)
    (hint : Integrable (fun η : Site d → ℤ => |((η 0 : ℤ) : ℝ)|) μ) (n : ℕ) :
    Parking.meanU (dataLaw d μ) n = ∑ s ∈ Finset.range n, Parking.S (dataLaw d μ) s := by
  classical
  have hIA : ∀ s ∈ Finset.range n,
      Integrable (fun ω : Data d => (Parking.A ω s 0 : ℝ)) (dataLaw d μ) :=
    fun s _ => integrable_A_data hd hti hint s 0
  have hstep : Parking.meanU (dataLaw d μ) n
      = ∫ ω, (∑ s ∈ Finset.range n, (Parking.A ω s 0 : ℝ)) ∂(dataLaw d μ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have := congrArg (fun m : ℕ => (m : ℝ)) (U_eq_sum_A ω n 0)
    push_cast at this
    exact this
  rw [hstep, integral_finsetSum _ hIA]
  exact Finset.sum_congr rfl fun s _ => mean_activity_eq_survivors hd hti hint s

end Parking

end
