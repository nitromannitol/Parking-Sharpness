/-
The round martingale behind `signedM(φ) → 0` in `(law d ν)`-probability, following the proof of
`parking.tex:1758-1766`.

The key step of this file is a measurability statement.  `signedM`'s round-`k` increment, built
from a `expFiltration d k`-measurable RANDOM RANGE of raw stack reads, is in general only ALMOST
SURELY, not PATHWISE, `expFiltration d (k+1)`-measurable — the exact same obstruction
`Parking.Frozen.exposure`'s own docstring records for `U_{k+1}` itself.  Rather than force
pathwise per-increment measurability (impossible without the a.s. neighbour hypothesis, which
would make `ξ` conditional on an event outside the filtration), this file proves what the
round martingale square-function bound (`Parking.Generic.RoundMartingale.
integral_sq_sum_eq_sum_integral_sq`) actually needs: the PARTIAL SUM `∑_{k<t} ξ k` is
`expFiltration d t`-measurable PATHWISE, at every horizon `t`, by a SINGLE gated-read argument
at that horizon (`readGate`/`measurable_readGate`, mirroring `Parking.measurable_arrivals_
expFiltration`'s own generator technique one level up: a countable union, over the destination
`x`, of the exposure filtration's own generators `{ω | j+1 ≤ U ω t y ∧ ω.2.1 (y,j) = x}`), not
round by round.  The round-by-round decomposition of the partial sum into `ξ k`'s, needed for
the martingale orthogonality argument (`single_core`/`double_core`), is then a
PURELY ALGEBRAIC telescoping fact (`Parking.U_mono_time`, `U ω 0 y = 0`), needing no
measurability of the individual pieces at all.
-/
import Parking.Support.SpatWMartingaleCore
import Parking.Support.SpatWSignedDecomp
import Parking.Support.NearTailSum
import Parking.Support.DensitySequence
import Parking.Generic.RoundMartingale

open MeasureTheory LatticeProb Finset Filter Topology
open scoped ENNReal

noncomputable section
namespace Parking

variable {d : ℕ}

/-- The discrete measurable structure on `Option (Site d)`, needed to route the exposure
filtration's own countable-partition technique through a "was it read, and to where" selector. -/
instance : MeasurableSpace (Option (Site d)) := ⊤

instance : MeasurableSingletonClass (Option (Site d)) := ⟨fun _ => trivial⟩

/-! ### The gated read: genuinely `expFiltration d t`-measurable, not merely a.e. -/

/-- **The `t`-gated destination of instruction `(y,j)`**: `some (ρ_j(y))` if `(y,j)` was read
by round `t`, else `none`.  Countable-valued, and genuinely `expFiltration d t`-measurable
(unlike the raw read `ω.2.1 (y,j)`), via the exposure filtration's own generators. -/
def readSel (t : ℕ) (y : Site d) (j : ℕ) (ω : Data d) : Option (Site d) :=
  if j + 1 ≤ U ω t y then some (ω.2.1 (y, j)) else none

theorem measurable_readSel {t : ℕ} (ht : 1 ≤ t) (y : Site d) (j : ℕ) :
    Measurable[expFiltration d t] (readSel t y j) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  refine @measurable_to_countable' (Option (Site d)) (Data d) _ _ (expFiltration d (k + 1)) _
    fun o => ?_
  cases o with
  | none =>
    have hset : (readSel (k + 1) y j) ⁻¹' {none}
        = (⋃ x : Site d, {ω : Data d | j + 1 ≤ U ω (k + 1) y ∧ ω.2.1 (y, j) = x})ᶜ := by
      ext ω
      constructor
      · intro hω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, readSel] at hω
        simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq]
        rintro ⟨x, hx1, hx2⟩
        rw [if_pos hx1] at hω
        exact Option.some_ne_none _ hω
      · intro hω
        simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at hω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, readSel]
        by_cases h : j + 1 ≤ U ω (k + 1) y
        · exact absurd (And.intro h rfl) (hω (ω.2.1 (y, j)))
        · rw [if_neg h]
    rw [hset]
    exact (MeasurableSet.iUnion fun x => measurableSet_generator k y x j).compl
  | some x =>
    have hset : (readSel (k + 1) y j) ⁻¹' {some x}
        = {ω : Data d | j + 1 ≤ U ω (k + 1) y ∧ ω.2.1 (y, j) = x} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, readSel, Set.mem_setOf_eq]
      by_cases h : j + 1 ≤ U ω (k + 1) y
      · rw [if_pos h]
        constructor
        · intro heq; exact ⟨h, Option.some.inj heq⟩
        · rintro ⟨-, heq⟩; rw [heq]
      · rw [if_neg h]
        constructor
        · intro heq; exact absurd heq.symm (Option.some_ne_none x)
        · rintro ⟨hc, -⟩; exact absurd hc h
    rw [hset]
    exact measurableSet_generator k y x j

/-- **The `t`-gated read of instruction `(y,j)`**: `ψ(ρ_j(y))` if `(y,j)` was read by round
`t`, else `0`.  Unlike the raw read `ω.2.1 (y,j)` (only ambiently measurable), this is
genuinely `expFiltration d t`-measurable. -/
def readGate (d t : ℕ) (y : Site d) (j : ℕ) (ψ : Site d → ℝ) (ω : Data d) : ℝ :=
  (readSel t y j ω).elim 0 ψ

theorem measurable_readGate {t : ℕ} (ht : 1 ≤ t) (y : Site d) (j : ℕ) (ψ : Site d → ℝ) :
    Measurable[expFiltration d t] (readGate d t y j ψ) :=
  (measurable_from_countable' (fun o : Option (Site d) => o.elim (0 : ℝ) ψ)).comp
    (measurable_readSel ht y j)

theorem readGate_eq_of_lt {t : ℕ} {y : Site d} {j : ℕ} {ψ : Site d → ℝ} {ω : Data d}
    (h : j < U ω t y) : readGate d t y j ψ ω = ψ (ω.2.1 (y, j)) := by
  unfold readGate readSel
  rw [if_pos (by omega : j + 1 ≤ U ω t y)]
  rfl

/-! ### The `expFiltration d t`-measurability of the partial sum -/

/-- **A per-site sum over a `expFiltration d t`-measurable random range of gated reads is
`expFiltration d t`-measurable.**  Countable-partition on the value of `U ω t y` (itself
`expFiltration d t`-measurable, `Parking.measurable_U_expFiltration`), reducing each piece to a
FIXED finite sum of the (unconditionally `expFiltration d t`-measurable) `readGate`. -/
theorem measurable_sum_range_readGate {t : ℕ} (ht : 1 ≤ t) (y : Site d) (ψ : Site d → ℝ) :
    Measurable[expFiltration d t]
      (fun ω : Data d => ∑ j ∈ Finset.range (U ω t y), readGate d t y j ψ ω) := by
  classical
  refine @measurable_of_countable_partition (Data d) ℝ ℕ (expFiltration d t) _ _ _ _
    (fun ω => U ω t y) (measurable_U_expFiltration t y)
    (fun ω => ∑ j ∈ Finset.range (U ω t y), readGate d t y j ψ ω)
    (fun M ω => ∑ j ∈ Finset.range M, readGate d t y j ψ ω) ?_ (fun _ => rfl)
  intro M
  exact Finset.measurable_sum _ fun j _ => measurable_readGate ht y j ψ

/-- **The partial sum `signedM` reduces to is `expFiltration d t`-measurable at every positive
horizon.** -/
theorem measurable_sn (φR : Site d → ℝ) (box' : Finset (Site d)) {t : ℕ} (ht : 1 ≤ t) :
    Measurable[expFiltration d t] (fun ω : Data d =>
      ∑ y ∈ box', (∑ j ∈ Finset.range (U ω t y), readGate d t y j φR ω
        - (U ω t y : ℝ) * walkOp φR y)) := by
  classical
  refine Finset.measurable_sum box' fun y _ => ?_
  refine Measurable.sub ?_ ?_
  · exact measurable_sum_range_readGate ht y φR
  · exact ((measurable_from_countable' (fun n : ℕ => (n : ℝ))).comp
      (measurable_U_expFiltration t y)).mul measurable_const

/-! ### The round increment, and the telescoping identity -/

/-- **The round-`k` martingale increment at site `y`**: the paper's own formula
`φ_R(ρ_j(y))-(Pφ_R)(y)` summed over the instructions newly read between round `k` and round
`k+1`. -/
def roundInc (φR : Site d → ℝ) (k : ℕ) (y : Site d) (ω : Data d) : ℝ :=
  ∑ j ∈ Finset.Ico (U ω k y) (U ω (k + 1) y), (φR (ω.2.1 (y, j)) - walkOp φR y)

/-- **The box-summed round-`k` increment.** -/
def xiRound (φR : Site d → ℝ) (box' : Finset (Site d)) (k : ℕ) (ω : Data d) : ℝ :=
  ∑ y ∈ box', roundInc φR k y ω

/-- **Telescoping**: the partial sum of the round increments, at horizon `t`, is exactly the
closed form `signedM` reduces to. -/
theorem sum_range_xiRound_eq (φR : Site d → ℝ) (box' : Finset (Site d)) (t : ℕ) (ω : Data d) :
    (∑ k ∈ Finset.range t, xiRound φR box' k ω)
      = ∑ y ∈ box', (∑ j ∈ Finset.range (U ω t y), φR (ω.2.1 (y, j))
          - (U ω t y : ℝ) * walkOp φR y) := by
  unfold xiRound
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  have htele : ∀ n : ℕ, (∑ k ∈ Finset.range n, roundInc φR k y ω)
      = ∑ j ∈ Finset.range (U ω n y), (φR (ω.2.1 (y, j)) - walkOp φR y) := by
    intro n
    induction n with
    | zero =>
      have h0 : U ω 0 y = 0 := rfl
      simp [h0]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      unfold roundInc
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        ← Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 0 (U ω n y) (U ω (n + 1) y)),
        Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (U_mono_time ω y (Nat.le_succ n))]
  rw [htele t, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **`sum_range_xiRound_eq`, rewritten with the reads gated (so it matches
`measurable_sn`'s own closed form).** -/
theorem sum_range_xiRound_eq_gated (φR : Site d → ℝ) (box' : Finset (Site d)) {t : ℕ}
    (ω : Data d) :
    (∑ k ∈ Finset.range t, xiRound φR box' k ω)
      = ∑ y ∈ box', (∑ j ∈ Finset.range (U ω t y), readGate d t y j φR ω
          - (U ω t y : ℝ) * walkOp φR y) := by
  rw [sum_range_xiRound_eq]
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [readGate_eq_of_lt (Finset.mem_range.mp hj)]

/-- **`Measurable[expFiltration d t]` for the partial sum of round increments**, at every
positive horizon. -/
theorem measurable_sum_range_xiRound (φR : Site d → ℝ) (box' : Finset (Site d)) {t : ℕ}
    (ht : 1 ≤ t) :
    Measurable[expFiltration d t]
      (fun ω : Data d => ∑ k ∈ Finset.range t, xiRound φR box' k ω) := by
  have heq : (fun ω : Data d => ∑ k ∈ Finset.range t, xiRound φR box' k ω)
      = fun ω => ∑ y ∈ box', (∑ j ∈ Finset.range (U ω t y), readGate d t y j φR ω
          - (U ω t y : ℝ) * walkOp φR y) :=
    funext fun ω => sum_range_xiRound_eq_gated φR box' ω
  rw [heq]
  exact measurable_sn φR box' ht

/-! ### The round-`k` increment has conditional mean zero -/

/-- **`single_core`, summed over a fixed finite range of unread instructions.**  The range's
endpoints are FIXED naturals `a ≤ b` (not the random `U ω k y`/`expOdometer d k ω y`
themselves); this is exactly the per-piece fact `Parking.Generic.CondExpPartition.
condExp_of_countable_partition` needs after conditioning on the value of that pair. -/
theorem sum_single_core (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (k : ℕ) (y : Site d) (a b : ℕ) (ψ : Site d → ℝ) {M : ℝ} (hbound : ∀ x, |ψ x| ≤ M)
    {T : Set (Data d)} (hT : MeasurableSet[expFiltration d k] T)
    (hTsub : T ⊆ {ω | U ω k y = a}) :
    ∫ ω, T.indicator (fun ω => ∑ j ∈ Finset.Ico a b, ψ (ω.2.1 (y, j))) ω ∂(law d ν)
      = ((b - a : ℕ) : ℝ) * walkOp ψ y * (law d ν).real T := by
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  have hTamb : MeasurableSet T := expFiltration_le d k T hT
  have hind : (fun ω : Data d => T.indicator (fun ω => ∑ j ∈ Finset.Ico a b, ψ (ω.2.1 (y, j))) ω)
      = fun ω => ∑ j ∈ Finset.Ico a b, T.indicator (fun ω => ψ (ω.2.1 (y, j))) ω := by
    funext ω
    by_cases h : ω ∈ T
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  rw [hind]
  have hmeasj : ∀ j : ℕ, Measurable (fun ω : Data d => ψ (ω.2.1 (y, j))) := fun j =>
    (measurable_from_countable' ψ).comp
      ((measurable_pi_apply (y, j)).comp (measurable_fst.comp measurable_snd))
  have hintg : ∀ j ∈ Finset.Ico a b,
      Integrable (fun ω => T.indicator (fun ω => ψ (ω.2.1 (y, j))) ω) (law d ν) := by
    intro j _
    refine Integrable.indicator ?_ hTamb
    exact Integrable.mono' (integrable_const M) (hmeasj j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hbound _)
  rw [integral_finsetSum _ hintg]
  have hterm : ∀ j ∈ Finset.Ico a b,
      ∫ ω, T.indicator (fun ω => ψ (ω.2.1 (y, j))) ω ∂(law d ν)
        = walkOp ψ y * (law d ν).real T := by
    intro j hj
    have hTsub' : T ⊆ {ω | U ω k y ≤ j} := fun ω hω => by
      show U ω k y ≤ j
      have ha : U ω k y = a := hTsub hω
      rw [ha]; exact (Finset.mem_Ico.mp hj).1
    exact single_core hd ν k y j ψ hT hTsub'
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
  ring

/-- **The `expOdometer`-gated round-`k` increment at a single site has conditional mean
zero.** -/
theorem condExp_siteExp_eq_zero (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (k : ℕ) (y : Site d) {φR : Site d → ℝ} {M : ℝ} (hbound : ∀ x, |φR x| ≤ M) :
    (law d ν)[fun ω : Data d =>
        ∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y)
      | expFiltration d k] =ᵐ[law d ν] (fun _ => (0 : ℝ)) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  classical
  set sel : Data d → ℕ × ℕ := fun ω => (U ω k y, expOdometer d k ω y) with hseldef
  have hsel : Measurable[expFiltration d k] sel :=
    (measurable_U_expFiltration k y).prodMk (measurable_expOdometer k y)
  have hΦeq : (fun ω : Data d =>
      ∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y))
      = fun ω => ∑ j ∈ Finset.Ico (sel ω).1 (sel ω).2, (φR (ω.2.1 (y, j)) - walkOp φR y) := rfl
  have hMbound : ∀ x, |φR x - walkOp φR y| ≤ M + |walkOp φR y| := fun x => by
    calc |φR x - walkOp φR y| ≤ |φR x| + |walkOp φR y| := abs_sub _ _
      _ ≤ M + |walkOp φR y| := by linarith [hbound x]
  have hmeasΦ : Measurable (fun ω : Data d =>
      ∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y)) := by
    have hmeasrange : Measurable fun ω : Data d => (U ω k y, expOdometer d k ω y) :=
      ((measurable_U_expFiltration k y).mono (expFiltration_le d k) le_rfl).prodMk
        ((measurable_expOdometer k y).mono (expFiltration_le d k) le_rfl)
    have hmeasj : ∀ j : ℕ, Measurable (fun ω : Data d => φR (ω.2.1 (y, j)) - walkOp φR y) :=
      fun j => ((measurable_from_countable' φR).comp
        ((measurable_pi_apply (y, j)).comp (measurable_fst.comp measurable_snd))).sub
        measurable_const
    exact measurable_of_countable_partition (fun ω => (U ω k y, expOdometer d k ω y))
      hmeasrange _ (fun c ω => ∑ j ∈ Finset.Ico c.1 c.2, (φR (ω.2.1 (y, j)) - walkOp φR y))
      (fun c => Finset.measurable_sum _ fun j _ => hmeasj j) (fun _ => rfl)
  have hIΦ : Integrable (fun ω : Data d =>
      ∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y))
      (law d ν) := by
    have hInt2 : Integrable (fun ω : Data d => (expOdometer d k ω y : ℝ)) (law d ν) := by
      have hcong : (fun ω : Data d => (expOdometer d k ω y : ℝ))
          =ᵐ[law d ν] fun ω => (U ω (k + 1) y : ℝ) := by
        filter_upwards [U_succ_ae_eq_expOdometer hd ν k y] with ω hω
        exact_mod_cast hω.symm
      exact (integrable_U_law hd ν hν.integrable_abs (k + 1) y).congr hcong.symm
    have hM0 : 0 ≤ M := le_trans (abs_nonneg (φR (0 : Site d))) (hbound (0 : Site d))
    have h0 : 0 ≤ M + |walkOp φR y| := by linarith [abs_nonneg (walkOp φR y)]
    refine Integrable.mono' ((hInt2.add (integrable_U_law hd ν hν.integrable_abs k y)).const_mul
      (M + |walkOp φR y|)) hmeasΦ.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    show |∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y)|
      ≤ (M + |walkOp φR y|) * ((expOdometer d k ω y : ℝ) + (U ω k y : ℝ))
    calc |∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y)|
        ≤ ∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (M + |walkOp φR y|) :=
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ => hMbound (ω.2.1 (y, j)))
      _ = ((Finset.Ico (U ω k y) (expOdometer d k ω y)).card : ℝ) * (M + |walkOp φR y|) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (expOdometer d k ω y : ℝ) * (M + |walkOp φR y|) := by
          have hcard : (Finset.Ico (U ω k y) (expOdometer d k ω y)).card ≤ expOdometer d k ω y := by
            rw [Nat.card_Ico]; omega
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) h0
      _ ≤ (M + |walkOp φR y|) * ((expOdometer d k ω y : ℝ) + (U ω k y : ℝ)) := by
          have hUnn : (0 : ℝ) ≤ (U ω k y : ℝ) := Nat.cast_nonneg _
          nlinarith
  refine Parking.Generic.CondExpPartition.condExp_of_countable_partition
    (μ := law d ν) (expFiltration_le d k) sel hsel _ (fun _ => 0) hIΦ measurable_const
    (integrable_const 0) ?_
  rintro ⟨a, b⟩ S hS hSsub
  have hpiece : ∀ ω ∈ S, U ω k y = a ∧ expOdometer d k ω y = b := by
    intro ω hω
    have heq : (U ω k y, expOdometer d k ω y) = (a, b) := hSsub hω
    injection heq with h1 h2
    exact ⟨h1, h2⟩
  have hSsub' : S ⊆ {ω | U ω k y = a} := fun ω hω => (hpiece ω hω).1
  set ψ : Site d → ℝ := fun x => φR x - walkOp φR y with hψdef
  have hψbound : ∀ x, |ψ x| ≤ M + |walkOp φR y| := fun x => hMbound x
  have hcore := sum_single_core hd ν k y a b ψ hψbound hS hSsub'
  have hψwalk : walkOp ψ y = 0 := by rw [hψdef, walkOp_sub_const hd, sub_self]
  have heqS : (fun ω : Data d => S.indicator
        (fun ω => ∑ j ∈ Finset.Ico a b, ψ (ω.2.1 (y, j))) ω)
      = fun ω => S.indicator (fun ω =>
          ∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y))
        ω := by
    funext ω
    by_cases h : ω ∈ S
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, (hpiece ω h).1, (hpiece ω h).2]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
  rw [← heqS, hcore, hψwalk, mul_zero, zero_mul]
  simp

end Parking

end
