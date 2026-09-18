/-
`Parking.boxToFin` is an isometry from `rewardBox T A` (the product of two real intervals) to
`Fin 2 → ℝ` (the sup metric): both metrics are the max of the same two coordinate distances.
This lets `Parking.orientedBoxReward_modulusInProbability`'s equicontinuity-in-probability
bound, stated on `Fin 2 → ℝ`, be read directly as the `htight` hypothesis of
`LatticeProb.tendsto_integral_of_fdd_of_equicontinuous'` on the compact metric space
`rewardBox T A` itself.
-/
import Parking.Support.TightEquicont
import Parking.Support.TightFddAssembly
import Parking.Support.TightContBoxLimit
import LatticeProb.Prob.FddTight

open MeasureTheory LatticeProb Filter Topology

noncomputable section

namespace Parking

local instance (T A : ℝ) : MeasurableSpace C(rewardBox T A, ℝ) := borel _
local instance (T A : ℝ) : BorelSpace C(rewardBox T A, ℝ) := ⟨rfl⟩

/-- **`Parking.boxToFin` does not increase distances.** -/
theorem dist_boxToFin_le (T A : ℝ) (p q : rewardBox T A) :
    dist (boxToFin T A p) (boxToFin T A q) ≤ dist p q := by
  refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
  fin_cases i
  · show dist (p.1 : ℝ) (q.1 : ℝ) ≤ dist p q
    rw [Prod.dist_eq]; exact le_max_left _ _
  · show dist (p.2 : ℝ) (q.2 : ℝ) ≤ dist p q
    rw [Prod.dist_eq]; exact le_max_right _ _

/-! ### The McShane lift of a bounded Lipschitz functional off `C(K, ℝ)`

`LatticeProb.tendsto_integral_of_fdd_of_equicontinuous'` tests a functional `Φ` that must be
globally defined, bounded and "uniformly continuous" (in the elementary sense
`∀ z ∈ K, |v z - w z| ≤ δ → |Φ v - Φ w| ≤ ε`) on EVERY function `v : E → ℝ`, continuous or not,
whereas a test functional `Φ0` of `hlaw` is defined only on `C(rewardBox T A, ℝ)`.  A junk-valued
lift (`Φ0` where the restriction is continuous, `0` elsewhere) fails: the junk value is unrelated
to nearby continuous values, so no modulus bound can hold globally.  The fix, for Lipschitz `Φ0`,
is a genuine (McShane) Lipschitz extension, built here directly as an infimal convolution against
the UNIT-CAPPED distance `Parking.capDist`, rather than through a registered `PseudoMetricSpace`
instance on the whole function space. -/

/-- The unit cap is subadditive on nonnegative reals: `min 1` of a sum of nonnegatives is at
most the sum of the individual caps. -/
theorem min_one_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min 1 (a + b) ≤ min 1 a + min 1 b := by
  rcases le_total 1 a with h | h
  · have h1 : min 1 a = 1 := min_eq_left h
    have h2 : (0 : ℝ) ≤ min 1 b := le_min zero_le_one hb
    rw [h1]
    linarith [min_le_left (1 : ℝ) (a + b)]
  rcases le_total 1 b with h' | h'
  · have h1 : min 1 b = 1 := min_eq_left h'
    have h2 : (0 : ℝ) ≤ min 1 a := le_min zero_le_one ha
    rw [h1]
    linarith [min_le_left (1 : ℝ) (a + b)]
  · rw [min_eq_right h, min_eq_right h']
    exact min_le_right _ _

variable {T A : ℝ}

/-- **The unit-capped sup distance between two raw functions on the box.**  Bounded by `1`, so
well-defined (via `Real.iSup`) for functions of any size, unlike the plain sup distance. -/
def capDist [Nonempty (rewardBox T A)] (v w : rewardBox T A → ℝ) : ℝ :=
  ⨆ p : rewardBox T A, min 1 |v p - w p|

theorem bddAbove_capDist_range [Nonempty (rewardBox T A)] (v w : rewardBox T A → ℝ) :
    BddAbove (Set.range fun p : rewardBox T A => min 1 |v p - w p|) :=
  ⟨1, by rintro _ ⟨p, rfl⟩; exact min_le_left _ _⟩

theorem le_capDist [Nonempty (rewardBox T A)] (v w : rewardBox T A → ℝ) (p : rewardBox T A) :
    min 1 |v p - w p| ≤ capDist v w :=
  le_ciSup (bddAbove_capDist_range v w) p

theorem capDist_nonneg [Nonempty (rewardBox T A)] (v w : rewardBox T A → ℝ) :
    0 ≤ capDist v w :=
  le_trans (le_min zero_le_one (abs_nonneg _))
    (le_capDist v w (Classical.arbitrary (α := rewardBox T A)))

theorem capDist_le_one [Nonempty (rewardBox T A)] (v w : rewardBox T A → ℝ) :
    capDist v w ≤ 1 :=
  ciSup_le fun _ => min_le_left _ _

theorem capDist_comm [Nonempty (rewardBox T A)] (v w : rewardBox T A → ℝ) :
    capDist v w = capDist w v := by
  unfold capDist; simp_rw [abs_sub_comm]

/-- **The near-triangle inequality for `Parking.capDist`.** -/
theorem capDist_le_add [Nonempty (rewardBox T A)] (v w u : rewardBox T A → ℝ) :
    capDist v w ≤ capDist v u + capDist u w := by
  refine ciSup_le fun p => ?_
  have hstep : |v p - w p| ≤ |v p - u p| + |u p - w p| := by
    have := abs_sub_le (v p) (u p) (w p); linarith
  calc min 1 |v p - w p| ≤ min 1 (|v p - u p| + |u p - w p|) :=
        min_le_min le_rfl hstep
    _ ≤ min 1 |v p - u p| + min 1 |u p - w p| :=
        min_one_add_le _ _ (abs_nonneg _) (abs_nonneg _)
    _ ≤ capDist v u + capDist u w :=
        add_le_add (le_capDist v u p) (le_capDist u w p)

end Parking

end
