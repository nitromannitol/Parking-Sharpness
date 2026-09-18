/-
Theorem 12.2 of parking.tex, frozen.  `parking.tex:3057-3070` (label
`thm:oriented`):

  "Let $\eta=(\eta(x))_{x\in\Z^d}$ be i.i.d. with mean zero, and let
   $\vec u_n$ obey $\vec u_0=0$, $\vec u_{n+1}=(\eta+\vec P\vec u_n)^+$.  The
   following bounds hold for $n\geq1$.  If $d=2$ and
   $\E|\eta(0)|^r<\infty$ for some $r>4$, then $\E\vec u_n(0)\leq Cn^{1/4}$.
   If $d\geq3$ and $\E e^{\theta|\eta(0)|}<\infty$ for some $\theta>0$, then
   $\E\vec u_n(0)\leq C\log(n+1)$.  If $\eta(0)$ has positive finite variance,
   then $\E\vec u_n(0)\geq c\sqrt{\vec\kappa_d(n)}$."

`E \vec u_n(0)` is `meanuOriented`, the mean of the oriented divisible
odometer, which reads only the configuration coordinate of the data.  The
directed Green square norms, the walk maximum comparison, and the scenery
moment estimates give the three bounds.  The lower bound uses convex
comparison with a sparse symmetric integer law and second and fourth moments.
-/
import Parking.Support.Range
import Parking.Support.OrientedTwoMean
import Parking.Support.OrientedAllNorms
import Parking.Support.OrientedLogMean

open MeasureTheory ProbabilityTheory

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.oriented (d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ)
    (hprob : IsProbabilityMeasure ν) (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k, (k : ℝ) ∂ν = 0) :
    (d = 2 → ∀ r : ℝ, 4 < r → Integrable (fun k : ℤ => |(k : ℝ)| ^ r) ν →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        Parking.meanuOriented (Parking.orientedLaw d ν) n ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4)) ∧
    (3 ≤ d → ∀ θ : ℝ, 0 < θ → Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        Parking.meanuOriented (Parking.orientedLaw d ν) n ≤ C * Real.log ((n : ℝ) + 1)) ∧
    (0 < evariance (fun k : ℤ => (k : ℝ)) ν → evariance (fun k : ℤ => (k : ℝ)) ν < ⊤ →
      ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
        c * Real.sqrt (Parking.orientedKappa d n)
          ≤ Parking.meanuOriented (Parking.orientedLaw d ν) n)
-- FROZEN-STATEMENT-END
:= by
  letI : IsProbabilityMeasure ν := hprob
  refine ⟨?_, ?_, ?_⟩
  · intro hd2 r hr hmom
    subst d
    exact Parking.exists_meanuOriented_two_upper ν hmean r hr hmom
  · intro hd3 θ hθ he
    exact Parking.exists_meanuOriented_log_upper hd3 ν hint hmean hθ he
  · intro hv _hvfin
    exact Parking.exists_meanuOriented_variance_lower ν hint hmean hv hd
