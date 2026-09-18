/-
Lemma 11.1 of parking.tex, frozen.  `parking.tex:2584-2589` (label
`lem:near-tilt`), in the setting of `parking.tex:2573-2583` ("let $\eta_\delta$
satisfy the assumptions of Theorem 1.7, and let $S_t^\delta$ be the expected
number of particles from the origin not settled by time $t$; let $R_t$ be the
range through time $t$ of a simple random walk from the origin, independent of
the model"):

  "For all sufficiently small $\delta>0$ and every $t\geq0$,
   $S_t^\delta\leq C\E_0e^{-c\delta^2|R_t|}$."

"For all sufficiently small `δ`" is an explicit threshold `δ₁`.  The
finiteness of the expected number of surviving particles from the origin is
asserted alongside the bound, so that an undefined integral cannot satisfy it
through its junk value.
-/
import Parking.Support.Near
import Parking.Support.NearTiltInterval

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.near_tilt (d : ℕ) (hd : 1 ≤ d) (δ₀ : ℝ) (ν : ℝ → Measure ℤ)
    (θ M K : ℝ) (hfam : Parking.NearFamily δ₀ ν θ M K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ δ₀ ∧
      ∀ δ ∈ Set.Ioc (0 : ℝ) δ₁, ∀ t : ℕ,
        Integrable (fun ω => (LatticeProb.survivorsFrom (Parking.toDriver ω) t 0 : ℝ))
            (Parking.law d (ν δ)) ∧
          Parking.S (Parking.law d (ν δ)) t ≤ C * Parking.rangeExp d (c * δ ^ 2) t
-- FROZEN-STATEMENT-END
:= by
  exact Parking.exists_near_tilt_bound hd hfam
