/-
Two things the moment bound of `prop:w-moment` needs of the error field and
that no earlier module has: the error is a measurable function of the data and
its law is translation invariant, and it is bounded pathwise by a function of
the configuration alone.

The pathwise bound is what makes the moments of the statement finite.  It is
`eq:apriori-finite` carried through the error recursion: the odometer after `k`
rounds at `y` is at most `k` times the configuration summed over the box of
radius `k` around `y`, because every particle counted there began within `k` of
`y`; the error recursion adds one average of the error at the neighbours to one
sum of at most `2d` such odometers, so the box grows by two at each round and
the coefficient grows quadratically.  With the box of radius `2k` around the
site the bound is

  `|w_k(x)| ≤ 2dk² ∑_{|z-x| ≤ 2k} η(z)⁺`,

and the same for `w^\star`, where the walk has moved the site by at most `n`.
-/
import Parking.Support.GreenIncrement
import Parking.Support.ActivityHoles
import Parking.Support.Comparison

noncomputable section

namespace Parking

open LatticeProb Finset MeasureTheory

variable {d : ℕ}

/-! ### The neighbours of a translated site -/

theorem nbrFinset_add (x v : Site d) :
    nbrFinset (x + v) = (nbrFinset x).image (fun y => y + v) := by
  classical
  ext w
  simp only [nbrFinset, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_image]
  constructor
  · rintro ⟨i, hi | hi⟩
    · exact ⟨w - v, ⟨i, Or.inl (by rw [hi]; abel)⟩, by abel⟩
    · exact ⟨w - v, ⟨i, Or.inr (by rw [hi]; abel)⟩, by abel⟩
  · rintro ⟨y, ⟨i, hi | hi⟩, rfl⟩
    · exact ⟨i, Or.inl (by rw [hi]; abel)⟩
    · exact ⟨i, Or.inr (by rw [hi]; abel)⟩

/-- A neighbour of `x` lies in the box of radius one about `x`. -/
theorem mem_boxFinset_one_of_nbr {x y : Site d} (h : y ∈ nbrFinset x) :
    y ∈ boxFinset x 1 := by
  classical
  rw [nbrFinset, Finset.mem_biUnion] at h
  obtain ⟨i, -, hi⟩ := h
  rw [Finset.mem_insert, Finset.mem_singleton] at hi
  rw [mem_boxFinset_iff]
  intro j
  rcases hi with rfl | rfl
  · simp only [Pi.add_apply, add_sub_cancel_left, unit, Pi.single_apply]
    split <;> norm_num
  · simp only [Pi.sub_apply, sub_sub_cancel_left, unit, Pi.single_apply, abs_neg]
    split <;> norm_num

theorem walkOp_shift (v : Site d) (f : Site d → ℝ) (x : Site d) :
    walkOp (fun z => f (z + v)) x = walkOp f (x + v) := by
  rw [walkOp, walkOp, nbrSum, nbrSum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : x + unit i + v = x + v + unit i := by abel
  have h2 : x - unit i + v = x + v - unit i := by abel
  rw [h1, h2]

/-- **The error field is translation equivariant.**  Translating the data
translates the error, exactly as it translates the odometer. -/
theorem wErr_shiftData (v : Site d) (ω : Data d) (k : ℕ) (x : Site d) :
    wErr (shiftData v ω) k x = wErr ω k (x + v) := by
  classical
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      have hfun : wErr (shiftData v ω) k = fun z => wErr ω k (z + v) := funext ih
      have hL : wErr (shiftData v ω) (k + 1) x
          = walkOp (wErr (shiftData v ω) k) x +
            ∑ y ∈ nbrFinset x,
              ((arrivals (shiftData v ω).2.1 y x (U (shiftData v ω) k y) : ℝ)
                - (U (shiftData v ω) k y : ℝ) / (2 * (d : ℝ))) := rfl
      have hR : wErr ω (k + 1) (x + v)
          = walkOp (wErr ω k) (x + v) +
            ∑ y ∈ nbrFinset (x + v),
              ((arrivals ω.2.1 y (x + v) (U ω k y) : ℝ)
                - (U ω k y : ℝ) / (2 * (d : ℝ))) := rfl
      rw [hL, hR, hfun, walkOp_shift v (wErr ω k) x, nbrFinset_add x v]
      congr 1
      rw [Finset.sum_image (fun a _ b _ h => by exact add_right_cancel h)]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [arrivalsU_shiftData v ω k y x, U_shiftData]

/-! ### The error field is measurable -/

theorem measurable_wErr (k : ℕ) (x : Site d) :
    Measurable fun ω : Data d => wErr ω k x := by
  classical
  induction k generalizing x with
  | zero => exact measurable_const
  | succ k ih =>
      have hcast : ∀ (t : ℕ) (y z : Site d),
          Measurable fun ω : Data d => ((arrivals ω.2.1 y z (U ω t y) : ℕ) : ℝ) :=
        fun t y z => (measurable_from_countable' fun m : ℕ => (m : ℝ)).comp
          (measurable_arrivalsU t y z)
      have hU : ∀ (t : ℕ) (y : Site d),
          Measurable fun ω : Data d => ((U ω t y : ℕ) : ℝ) :=
        fun t y => (measurable_from_countable' fun m : ℕ => (m : ℝ)).comp (measurable_U t y)
      have hwalk : Measurable fun ω : Data d => walkOp (wErr ω k) x := by
        have : (fun ω : Data d => walkOp (wErr ω k) x)
            = fun ω : Data d =>
              (∑ i : Fin d, (wErr ω k (x + unit i) + wErr ω k (x - unit i))) / (2 * (d : ℝ)) :=
          rfl
        rw [this]
        exact (Finset.measurable_sum _ fun i _ => (ih (x + unit i)).add (ih (x - unit i))).div_const _
      have hsum : Measurable fun ω : Data d =>
          ∑ y ∈ nbrFinset x,
            ((arrivals ω.2.1 y x (U ω k y) : ℝ) - (U ω k y : ℝ) / (2 * (d : ℝ))) :=
        Finset.measurable_sum _ fun y _ => (hcast k y x).sub ((hU k y).div_const _)
      exact hwalk.add hsum

/-! ### The configuration summed over a box -/

/-- `∑_{|z - x| ≤ r} η(z)⁺`, the a priori bound of `eq:apriori-finite`. -/
def confBox (ω : Data d) (x : Site d) (r : ℕ) : ℝ :=
  ((∑ z ∈ boxFinset x r, (ω.1 z).toNat : ℕ) : ℝ)

theorem confBox_nonneg (ω : Data d) (x : Site d) (r : ℕ) : 0 ≤ confBox ω x r :=
  Nat.cast_nonneg _

theorem confBox_mono (ω : Data d) (x : Site d) {r r' : ℕ} (h : r ≤ r') :
    confBox ω x r ≤ confBox ω x r' := by
  refine Nat.cast_le.mpr (Finset.sum_le_sum_of_subset ?_)
  exact boxFinset_mono h

theorem confBox_le_of_mem (ω : Data d) {x c : Site d} {a : ℕ} (hc : c ∈ boxFinset x a) (b : ℕ) :
    confBox ω c b ≤ confBox ω x (a + b) := by
  refine Nat.cast_le.mpr (Finset.sum_le_sum_of_subset fun w hw => ?_)
  exact mem_boxFinset_add hc hw

/-- **The odometer against the configuration.**  Every particle that has left
`y` by round `k` began within `k` of `y`, and there are at most `k` rounds. -/
theorem U_le_confBox (ω : Data d) (k : ℕ) (y : Site d) :
    ((U ω k y : ℕ) : ℝ) ≤ (k : ℝ) * confBox ω y k := by
  have hle : U ω k y ≤ uBound ω.1 k y := U_le_uBound ω k y
  have hub : ((uBound ω.1 k y : ℕ) : ℝ)
      = ∑ s ∈ Finset.range k, ((∑ z ∈ boxFinset y s, (ω.1 z).toNat : ℕ) : ℝ) := by
    rw [uBound]; push_cast; ring
  have hterm : ∀ s ∈ Finset.range k,
      ((∑ z ∈ boxFinset y s, (ω.1 z).toNat : ℕ) : ℝ) ≤ confBox ω y k := by
    intro s hs
    exact confBox_mono ω y (Nat.le_of_lt (Finset.mem_range.mp hs))
  calc ((U ω k y : ℕ) : ℝ) ≤ ((uBound ω.1 k y : ℕ) : ℝ) := by exact_mod_cast hle
    _ = ∑ s ∈ Finset.range k, ((∑ z ∈ boxFinset y s, (ω.1 z).toNat : ℕ) : ℝ) := hub
    _ ≤ ∑ _s ∈ Finset.range k, confBox ω y k := Finset.sum_le_sum hterm
    _ = (k : ℝ) * confBox ω y k := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### The pathwise bound on the error -/

/-- The coefficient of the pathwise bound: `2dk²`. -/
def wCoef (d : ℕ) (k : ℕ) : ℝ := 2 * (d : ℝ) * (k : ℝ) ^ 2

theorem wCoef_nonneg (d k : ℕ) : 0 ≤ wCoef d k := by
  rw [wCoef]; positivity

theorem wCoef_mono (d : ℕ) {k k' : ℕ} (h : k ≤ k') : wCoef d k ≤ wCoef d k' := by
  rw [wCoef, wCoef]
  have hk : (k : ℝ) ≤ (k' : ℝ) := by exact_mod_cast h
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hdn : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
  have hsq : (k : ℝ) ^ 2 ≤ (k' : ℝ) ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_left hsq hdn

/-- **The error is bounded by the configuration over a box.**  This is
`eq:apriori-finite` carried through the error recursion. -/
theorem abs_wErr_le (hd : 1 ≤ d) (ω : Data d) (k : ℕ) (x : Site d) :
    |wErr ω k x| ≤ wCoef d k * confBox ω x (2 * k) := by
  classical
  have hdpos : (0 : ℝ) < 2 * (d : ℝ) := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  induction k generalizing x with
  | zero =>
      have h0 : wErr ω 0 x = 0 := rfl
      rw [h0, wCoef]
      simp
  | succ k ih =>
      set M : ℝ := confBox ω x (2 * (k + 1)) with hM
      have hM0 : 0 ≤ M := confBox_nonneg ω x _
      -- the walk-operator term
      have hnbr : ∀ z : Site d, z ∈ boxFinset x 1 →
          |wErr ω k z| ≤ wCoef d k * M := by
        intro z hz
        refine le_trans (ih z) ?_
        refine mul_le_mul_of_nonneg_left ?_ (wCoef_nonneg d k)
        refine le_trans (confBox_le_of_mem ω hz (2 * k)) ?_
        exact confBox_mono ω x (by omega)
      have hmem_add : ∀ i : Fin d, x + unit i ∈ boxFinset x 1 := fun i =>
        mem_boxFinset_one_of_nbr (mem_nbrFinset_add x i)
      have hmem_sub : ∀ i : Fin d, x - unit i ∈ boxFinset x 1 := fun i =>
        mem_boxFinset_one_of_nbr (mem_nbrFinset_sub x i)
      have hwalk : |walkOp (wErr ω k) x| ≤ wCoef d k * M := by
        rw [walkOp, nbrSum, abs_div, abs_of_pos hdpos, div_le_iff₀ hdpos]
        have hterms : ∀ i : Fin d,
            |wErr ω k (x + unit i) + wErr ω k (x - unit i)| ≤ 2 * (wCoef d k * M) := by
          intro i
          refine le_trans (abs_add_le _ _) ?_
          have h1 := hnbr _ (hmem_add i)
          have h2 := hnbr _ (hmem_sub i)
          linarith
        calc |∑ i : Fin d, (wErr ω k (x + unit i) + wErr ω k (x - unit i))|
            ≤ ∑ i : Fin d, |wErr ω k (x + unit i) + wErr ω k (x - unit i)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin d, 2 * (wCoef d k * M) := Finset.sum_le_sum fun i _ => hterms i
          _ = (d : ℝ) * (2 * (wCoef d k * M)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ = wCoef d k * M * (2 * (d : ℝ)) := by ring
      -- the arrival term
      have harr : |∑ y ∈ nbrFinset x,
          ((arrivals ω.2.1 y x (U ω k y) : ℝ) - (U ω k y : ℝ) / (2 * (d : ℝ)))|
            ≤ 4 * (d : ℝ) * (k : ℝ) * M := by
        have hterm : ∀ y ∈ nbrFinset x,
            |((arrivals ω.2.1 y x (U ω k y) : ℝ) - (U ω k y : ℝ) / (2 * (d : ℝ)))|
              ≤ 2 * ((k : ℝ) * M) := by
          intro y hy
          have hymem : y ∈ boxFinset x 1 := mem_boxFinset_one_of_nbr hy
          have hUle : ((U ω k y : ℕ) : ℝ) ≤ (k : ℝ) * M := by
            refine le_trans (U_le_confBox ω k y) ?_
            refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
            refine le_trans (confBox_le_of_mem ω hymem k) ?_
            exact confBox_mono ω x (by omega)
          have harr_le : ((arrivals ω.2.1 y x (U ω k y) : ℕ) : ℝ) ≤ ((U ω k y : ℕ) : ℝ) := by
            refine Nat.cast_le.mpr ?_
            refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
            rw [Finset.card_range]
          have hdiv : ((U ω k y : ℕ) : ℝ) / (2 * (d : ℝ)) ≤ ((U ω k y : ℕ) : ℝ) := by
            rw [div_le_iff₀ hdpos]
            have h1 : (0 : ℝ) ≤ ((U ω k y : ℕ) : ℝ) := Nat.cast_nonneg _
            nlinarith [show (1 : ℝ) ≤ (d : ℝ) from by exact_mod_cast hd]
          have hd0 : (0 : ℝ) ≤ ((arrivals ω.2.1 y x (U ω k y) : ℕ) : ℝ) := Nat.cast_nonneg _
          have hd1 : (0 : ℝ) ≤ ((U ω k y : ℕ) : ℝ) / (2 * (d : ℝ)) := by positivity
          rw [abs_le]
          constructor <;> linarith
        calc |∑ y ∈ nbrFinset x,
              ((arrivals ω.2.1 y x (U ω k y) : ℝ) - (U ω k y : ℝ) / (2 * (d : ℝ)))|
            ≤ ∑ y ∈ nbrFinset x,
              |((arrivals ω.2.1 y x (U ω k y) : ℝ) - (U ω k y : ℝ) / (2 * (d : ℝ)))| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _y ∈ nbrFinset x, 2 * ((k : ℝ) * M) := Finset.sum_le_sum hterm
          _ = ((nbrFinset x).card : ℝ) * (2 * ((k : ℝ) * M)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ = 4 * (d : ℝ) * (k : ℝ) * M := by
              rw [LatticeProb.Graph.Zd.card_nbrFinset]
              push_cast
              ring
      have hcoef : wCoef d k + 4 * (d : ℝ) * (k : ℝ) ≤ wCoef d (k + 1) := by
        rw [wCoef, wCoef]
        have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
        push_cast
        nlinarith
      have hfinal : |wErr ω (k + 1) x| ≤ (wCoef d k + 4 * (d : ℝ) * (k : ℝ)) * M := by
        have hexp : wErr ω (k + 1) x
            = walkOp (wErr ω k) x +
              ∑ y ∈ nbrFinset x,
                ((arrivals ω.2.1 y x (U ω k y) : ℝ) - (U ω k y : ℝ) / (2 * (d : ℝ))) := rfl
        rw [hexp, add_mul]
        exact le_trans (abs_add_le _ _) (add_le_add hwalk harr)
      refine le_trans hfinal ?_
      exact mul_le_mul_of_nonneg_right hcoef hM0

end Parking

end
