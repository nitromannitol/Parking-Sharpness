/- The directed error field regrouped by INSTRUCTION.

`Parking.wErrOriented_eq_sum_finiteRoute` writes the directed error at the origin
as a sum over ROUNDS, each round contributing the routing discrepancies of every
instruction alive at that round, read at the horizon left in that round.  The
martingale estimate of `parking.tex:3252-3272` needs the opposite grouping: each
instruction is a fresh independent coordinate and must be read once, with the
cumulative discrepancy `Parking.orientedCumDisc` over the horizons it is alive
for.  The two groupings agree because the odometer is nondecreasing in the round,
so the rounds at which an instruction is alive form a final segment of
`{0, …, n-1}`, and reflecting the round index turns it into the initial segment
`{0, …, alive - 1}` of horizons.
-/
import Parking.Support.OrientedCumulative
import Parking.Support.OrientedUnroll
import Parking.Support.OrientedParticleMoment

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
open scoped Classical
variable {d : ℕ}

/-- A predicate that fails upward cuts `range n` at its own cardinality. -/
theorem filter_range_eq_range_card {n : ℕ} (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ a b : ℕ, a ≤ b → P b → P a) :
    (range n).filter P = range (((range n).filter P).card) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.range_add_one, filter_insert]
      by_cases hPn : P n
      · have hall : (range n).filter P = range n := by
          refine filter_eq_self.mpr fun m hm => hP m n (le_of_lt (mem_range.mp hm)) hPn
        rw [if_pos hPn, hall, card_insert_of_notMem (by simp), card_range, ← Finset.range_add_one]
      · rw [if_neg hPn]
        exact ih

/-- The number of rounds before `n` at which instruction `(y,j)` is alive. -/
def orientedAlive (η : Site d → ℤ) (σ : Site d × ℕ → Site d) (n : ℕ) (y : Site d) (j : ℕ) : ℕ :=
  ((range n).filter fun m => j < orientedOdometer η σ (n - 1 - m) y).card

theorem orientedAlive_le (η : Site d → ℤ) (σ : Site d × ℕ → Site d) (n : ℕ) (y : Site d)
    (j : ℕ) : orientedAlive η σ n y j ≤ n := by
  refine le_trans (card_filter_le _ _) ?_
  rw [card_range]

/-- **One instruction, read once.**  Summing the routing discrepancies of the
instruction `(y,j)` over the rounds `k < n` at which it is alive gives the
cumulative discrepancy over the horizons `0, …, alive - 1`. -/
theorem sum_rounds_eq_orientedCumDisc (η : Site d → ℤ) (σ : Site d × ℕ → Site d)
    (n : ℕ) (y : Site d) (j : ℕ) (z : Site d) :
    (∑ k ∈ range n, if j < orientedOdometer η σ k y then
        orientedRouteDisc (n - (k + 1)) y z else 0)
      = orientedCumDisc (orientedAlive η σ n y j) y z := by
  have hrefl : (∑ k ∈ range n, if j < orientedOdometer η σ k y then
      orientedRouteDisc (n - (k + 1)) y z else 0)
      = ∑ m ∈ range n, if j < orientedOdometer η σ (n - 1 - m) y then
        orientedRouteDisc m y z else 0 := by
    rw [← Finset.sum_range_reflect
      (fun m => if j < orientedOdometer η σ (n - 1 - m) y then
        orientedRouteDisc m y z else 0) n]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k < n := mem_range.mp hk
    have h1 : n - 1 - (n - 1 - k) = k := by omega
    rw [h1]
    have h2 : n - 1 - k = n - (k + 1) := by omega
    rw [h2]
  rw [hrefl, ← sum_filter]
  have hanti : ∀ a b : ℕ, a ≤ b → j < orientedOdometer η σ (n - 1 - b) y →
      j < orientedOdometer η σ (n - 1 - a) y := by
    intro a b hab h
    exact lt_of_lt_of_le h (orientedOdometer_mono_time η σ y (by omega : n - 1 - b ≤ n - 1 - a))
  rw [filter_range_eq_range_card _ hanti]
  rfl

/-- **The directed error at the origin, regrouped by instruction.**  Each
instruction of the box of radius `n + 1` is read once, at the cumulative horizon
it is alive for. -/
theorem wErrOriented_eq_instructionSum (η : Site d → ℤ) (σ : Site d × ℕ → Site d)
    (hσ : ∀ q : Site d × ℕ, ∃ i : Fin d, σ q = q.1 + unit i) (n : ℕ) :
    wErrOriented η σ n 0 =
      ∑ y ∈ boxFinset (0 : Site d) (n + 1),
        ∑ j ∈ range (orientedOdometer η σ (n - 1) y),
          orientedCumDisc (orientedAlive η σ n y j) y (σ (y, j)) := by
  rw [wErrOriented_eq_sum_finiteRoute η σ hσ n]
  simp only [orientedFiniteRoute]
  have hpad : ∀ k ∈ range n, ∀ y : Site d,
      (∑ j ∈ range (orientedOdometer η σ k y), orientedRouteDisc (n - (k + 1)) y (σ (y, j)))
        = ∑ j ∈ range (orientedOdometer η σ (n - 1) y),
            if j < orientedOdometer η σ k y then
              orientedRouteDisc (n - (k + 1)) y (σ (y, j)) else 0 := by
    intro k hk y
    have hk' : k < n := mem_range.mp hk
    have hle : orientedOdometer η σ k y ≤ orientedOdometer η σ (n - 1) y :=
      orientedOdometer_mono_time η σ y (by omega : k ≤ n - 1)
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [mem_filter, mem_range]
    omega
  have hstep : (∑ k ∈ range n, ∑ y ∈ boxFinset (0 : Site d) (n + 1),
        ∑ j ∈ range (orientedOdometer η σ k y),
          orientedRouteDisc (n - (k + 1)) y (σ (y, j)))
      = ∑ k ∈ range n, ∑ y ∈ boxFinset (0 : Site d) (n + 1),
          ∑ j ∈ range (orientedOdometer η σ (n - 1) y),
            if j < orientedOdometer η σ k y then
              orientedRouteDisc (n - (k + 1)) y (σ (y, j)) else 0 :=
    sum_congr rfl fun k hk => sum_congr rfl fun y _ => hpad k hk y
  rw [hstep, Finset.sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  exact sum_congr rfl fun j _ => sum_rounds_eq_orientedCumDisc η σ n y j (σ (y, j))

end Parking
end
