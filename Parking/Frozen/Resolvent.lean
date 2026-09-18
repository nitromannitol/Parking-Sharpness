/-
Proposition 11.2 of parking.tex, frozen.  `parking.tex:2628-2648` (label
`prop:resolvent`):

  "There are $c,C>0$ such that, for $0<a\leq1$ and $t\geq1$,
   $\E_0e^{-a|R_t|}\leq C\exp\{-ca^{2/3}t^{1/3}\}$ for $d=1$,
   $\leq C\exp\{-c\sqrt{at/\log(t+2)}\}$ for $d=2$ and $t\geq e/a$,
   $\leq C\exp\{-c\sqrt{at}\}$ for $d\geq3$.
   Moreover, with $\Lambda=\log(e/a)$ and
   $T=C a^{-2}\Lambda^3$ for $d=1$, $Ca^{-1}\Lambda^3$ for $d=2$,
   $Ca^{-1}\Lambda^2$ for $d\geq3$,
   the sum $\sum_{t>T}\E_0e^{-a|R_t|}$ is at most one."

Summability of the tail sum is asserted alongside its bound, so that a
divergent series cannot satisfy the statement through the junk value of a
nonsummable `tsum`.
-/
import Parking.Support.RangeResolvent

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.resolvent (d : ℕ) (hd : 1 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ a : ℝ, 0 < a → a ≤ 1 → ∀ t : ℕ, 1 ≤ t →
        (d = 1 → Parking.rangeExp d a t
            ≤ C * Real.exp (-(c * a ^ ((2 : ℝ) / 3) * (t : ℝ) ^ ((1 : ℝ) / 3)))) ∧
        (d = 2 → Real.exp 1 / a ≤ (t : ℝ) → Parking.rangeExp d a t
            ≤ C * Real.exp (-(c * Real.sqrt (a * t / Real.log ((t : ℝ) + 2))))) ∧
        (3 ≤ d → Parking.rangeExp d a t ≤ C * Real.exp (-(c * Real.sqrt (a * t))))) ∧
      ∀ a : ℝ, 0 < a → a ≤ 1 →
        Summable (fun t : ℕ => if Parking.resolventThreshold d C a < (t : ℝ)
            then Parking.rangeExp d a t else 0) ∧
          ∑' t : ℕ, (if Parking.resolventThreshold d C a < (t : ℝ)
            then Parking.rangeExp d a t else 0) ≤ 1
-- FROZEN-STATEMENT-END
:= by
  rcases (show d = 1 ∨ d = 2 ∨ 3 ≤ d by omega) with h1 | h2 | h3
  · obtain ⟨c, C, hc, hC, hpt, htail⟩ := Parking.exists_resolvent_tail_one h1
    exact ⟨c, C, hc, hC, fun a ha ha1 t ht =>
      ⟨fun _ => hpt a ha ha1 t ht, fun hcon => absurd hcon (by omega),
        fun hcon => absurd hcon (by omega)⟩, htail⟩
  · obtain ⟨c, C, hc, hC, hpt, htail⟩ := Parking.exists_resolvent_tail_two h2
    exact ⟨c, C, hc, hC, fun a ha ha1 t ht =>
      ⟨fun hcon => absurd hcon (by omega), fun _ hte => hpt a ha ha1 t ht hte,
        fun hcon => absurd hcon (by omega)⟩, htail⟩
  · obtain ⟨c, C, hc, hC, hpt, htail⟩ := Parking.exists_resolvent_tail_high h3
    exact ⟨c, C, hc, hC, fun a ha ha1 t ht =>
      ⟨fun hcon => absurd hcon (by omega), fun hcon => absurd hcon (by omega),
        fun _ => hpt a ha ha1 t ht⟩, htail⟩
