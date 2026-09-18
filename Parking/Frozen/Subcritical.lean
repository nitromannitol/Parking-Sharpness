/-
Theorem 10.3 of parking.tex, frozen.  `parking.tex:2419-2432` (label
`thm:subcritical`), in the setting of `parking.tex:2272-2320`:

  "Under the assumptions and notation above, let
   $a\coloneqq\frac13\int_0^{\lambda_1}\delta(\lambda)\,d\lambda$.  Then $a>0$
   and, for every $t\geq0$ and every $k\geq1$ in the support of $\eta(0)$,
   $\P(\tau_1>t\mid\eta(0)=k,\ X_0,\ldots,X_t)
     \leq\exp\{\frac13\int_0^{\lambda_1}\E_\lambda|\eta(0)|\,d\lambda\}
       e^{\lambda_1(k-1)/3-a|R_t|}$.
   Consequently $S_t\leq C\E_0e^{-a|R_t|}$."

The finiteness of the expected number of surviving particles from the origin
is asserted alongside the last bound, so that an undefined integral cannot
satisfy it through its junk value.
Conditioning on the walk of the first particle at the origin is realized by
prescribing the moves of the label `(0,0)`, which is what
`survivalGivenWalk` does; the bound then holds for every prescribed walk.
`E_0` is an average over the walk alone.
-/
import Parking.Support.SubcriticalJointBound

open MeasureTheory

-- The dimension enters through the construction, the positive chance of a
-- positive value through the standing hypotheses of the section, and the
-- positivity of the tilting parameter through `lam₁ < θ`; the proof reads
-- neither of the last two.
set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.subcritical (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ)
    (hprob : IsProbabilityMeasure ν) (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k, (k : ℝ) ∂ν < 0) (hpos : 0 < ν (Set.Ioi 0))
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    (lam₁ : ℝ) (hlam₁ : 0 < lam₁) (hlam₁θ : lam₁ < θ)
    (hnonpos : ∀ s ∈ Set.Icc 0 lam₁,
      Integrable (fun k : ℤ => (k : ℝ)) (Parking.tiltLaw ν s) ∧
      ∫ k, (k : ℝ) ∂(Parking.tiltLaw ν s) ≤ 0)
    (a : ℝ) (ha : a = (1 / 3) * ∫ s in (0 : ℝ)..lam₁, Parking.drift ν s) :
    0 < a ∧
    (∀ (k : ℕ), 1 ≤ k → ν {(k : ℤ)} ≠ 0 → ∀ (t : ℕ) (w : ℕ → Fin d × Bool),
        Parking.survivalGivenWalk d ν k t w
          ≤ Real.exp ((1 / 3) * ∫ s in (0 : ℝ)..lam₁, ∫ j, |(j : ℝ)| ∂(Parking.tiltLaw ν s))
            * Real.exp (lam₁ * ((k : ℝ) - 1) / 3
              - a * (Parking.rangeCard (0 : Parking.Site d) w t : ℝ))) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ,
      Integrable (fun ω => (LatticeProb.survivorsFrom (Parking.toDriver ω) t 0 : ℝ))
        (Parking.law d ν) ∧
      Parking.S (Parking.law d ν) t
      ≤ C * ∫ p, Real.exp (-(a * (Parking.rangeCard (0 : Parking.Site d) p t : ℝ)))
          ∂(Parking.walkLaw d)
-- FROZEN-STATEMENT-END
:= by
  haveI := hprob
  subst ha
  exact ⟨Parking.subcritical_a_pos hint hexp hmean hlam₁ hlam₁θ hnonpos,
    fun k hk hνk t w =>
      Parking.survivalGivenWalk_le hd hint hexp hlam₁ hlam₁θ hnonpos k hk hνk t w,
    Parking.S_le_rangeExp hd hint hexp hlam₁ hlam₁θ hnonpos⟩
