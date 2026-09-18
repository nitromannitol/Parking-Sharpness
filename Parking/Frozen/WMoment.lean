/-
Proposition 5.6 of parking.tex, frozen.  `parking.tex:1187-1200` (label
`prop:w-moment`):

  "Let $\eta=(\eta(x))_{x\in\Z^d}$ have i.i.d. integer-valued coordinates, with
   $\E e^{\theta\eta(0)^+}<\infty$ for some $\theta>0$.  There is a
   dimension-dependent $C<\infty$ such that, for every $n\geq1$ and $r\geq2$,
   $\max_{m\leq n}(\E|w_m(0)|^r)^{1/r}
     \leq C(\sqrt{r\kappa_d(n)(\E U_n(0)^r)^{1/r}}+r)$,
   $(\E w_n^\star(0)^r)^{1/r}
     \leq(n+1)^{1/r}\max_{m\leq n}(\E|w_m(0)|^r)^{1/r}$."

The constant depends on the dimension alone, so it is bound before `ν`, `θ` and
the moment hypothesis, as well as before `n` and `r`.  The maximum is over the
nonempty finite set `{m : m ≤ n}`.
The two moments on the left are asserted finite alongside the bounds, so that
an undefined integral cannot satisfy them through its junk value.  The
martingale moment inequality the proof quotes enters as an explicit
hypothesis.
-/
import Parking.Support.WMomentProof

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.w_moment (hBernstein : Parking.External.Bernstein) (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : Measure ℤ, IsProbabilityMeasure ν → ∀ θ : ℝ, 0 < θ →
      Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν →
      ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 2 ≤ r →
      (∀ m ≤ n, Integrable (fun ω => |Parking.wErr ω m 0| ^ r) (Parking.law d ν)) ∧
      Integrable (fun ω => Parking.wStar ω n 0 ^ r) (Parking.law d ν) ∧
      (⨆ m ∈ Set.Iic n,
          (∫ ω, |Parking.wErr ω m 0| ^ r ∂(Parking.law d ν)) ^ (1 / r))
        ≤ C * (Real.sqrt (r * Parking.kappa d n *
            (∫ ω, (Parking.U ω n 0 : ℝ) ^ r ∂(Parking.law d ν)) ^ (1 / r)) + r) ∧
      (∫ ω, Parking.wStar ω n 0 ^ r ∂(Parking.law d ν)) ^ (1 / r)
        ≤ ((n : ℝ) + 1) ^ (1 / r) * ⨆ m ∈ Set.Iic n,
            (∫ ω, |Parking.wErr ω m 0| ^ r ∂(Parking.law d ν)) ^ (1 / r)
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨C, hC, hCle⟩ := Parking.exists_wErr_moment_const_uniform hd hBernstein
  refine ⟨C, hC, fun ν hprob θ hθ hexp n hn r hr2 => ?_⟩
  haveI := hprob
  refine ⟨?_, ?_, hCle ν hprob θ hθ hexp n hn r hr2, ?_⟩
  · exact fun m _ => Parking.integrable_abs_wErr_rpow hd ν hθ hexp (by linarith) m 0
  · exact Parking.integrable_wStar_rpow hd ν hθ hexp (by linarith) n 0
  · exact Parking.wStar_moment_bound hd ν hθ hexp (by linarith) n
