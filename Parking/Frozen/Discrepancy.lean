/-
Proposition 8.1 of parking.tex, frozen.  `parking.tex:1551-1568` (label
`prop:discrepancy`):

  "Under the assumptions of Theorem 1.2, suppose $d\leq3$.  For $n\geq1$, let
   $r=2\vee\lceil\log(n+1)\rceil$.  Then
   $(\E|U_n(0)-u_n(0)|^r)^{1/r}\leq C\,n^{5/8}[\log(n+1)]^{3/4}$ for $d=1$,
   $C\,n^{1/4}[\log(n+1)]^{5/4}$ for $d=2$, and
   $C\,n^{1/8}[\log(n+1)]^{3/4}$ for $d=3$.
   Consequently, for every $\eps>0$, there is $c>0$ such that, for all
   sufficiently large $n$,
   $\P(|U_n(0)-u_n(0)|>\eps\E u_n(0))\leq e^{-c(\log n)^2}$."

The exponent `r` is the paper's `2 ∨ ⌈log(n+1)⌉`, read as a real number.  "For
all sufficiently large `n`" is an explicit threshold.  The moment on the left
is asserted finite alongside the bound, so that an undefined integral cannot
satisfy it through its junk value. The proof at `parking.tex:1571-1576`
uses the collected Green estimates, which enter as an explicit hypothesis.
-/
import Parking.External.SandpileGrowth
import Parking.External.Bernstein
import Parking.External.UConcentration
import Parking.External.GreenNorms
import Parking.Support.DiscrepancyTail

open MeasureTheory

/-- The exponent `r = 2 ∨ ⌈log(n+1)⌉` of `prop:discrepancy`. -/
noncomputable def Parking.discrepancyExponent (n : ℕ) : ℝ :=
  max 2 ⌈Real.log ((n : ℝ) + 1)⌉₊

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.discrepancy (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration)
    (hGreenNorms : Parking.External.GreenNorms)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    ∃ C : ℝ, 0 < C ∧
      (∀ n : ℕ, 1 ≤ n →
        Integrable (fun ω => |(Parking.U ω n 0 : ℝ) - Parking.uOf ω n 0|
            ^ Parking.discrepancyExponent n) (Parking.law d ν) ∧
        (∫ ω, |(Parking.U ω n 0 : ℝ) - Parking.uOf ω n 0| ^ Parking.discrepancyExponent n
            ∂(Parking.law d ν)) ^ (1 / Parking.discrepancyExponent n)
          ≤ C * (if d = 1 then (n : ℝ) ^ ((5 : ℝ) / 8) * Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4)
              else if d = 2 then (n : ℝ) ^ ((1 : ℝ) / 4) * Real.log ((n : ℝ) + 1) ^ ((5 : ℝ) / 4)
              else (n : ℝ) ^ ((1 : ℝ) / 8) * Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4))) ∧
      ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ((Parking.law d ν) {ω | ε * Parking.meanu (Parking.law d ν) n
            < |(Parking.U ω n 0 : ℝ) - Parking.uOf ω n 0|}).toReal
          ≤ Real.exp (-(c * Real.log n ^ 2))
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨C, hC, hm⟩ := Parking.exists_discrepancy_moment hd hd3
    hGrowth hBernstein hConcentration hGreenNorms ν hν
  refine ⟨C, hC, ?_, Parking.exists_discrepancy_tail hd hd3
    hGrowth hBernstein hConcentration hGreenNorms ν hν⟩
  intro n hn
  simpa only [Parking.rNorm, Parking.discrepancyExponent, Parking.rHigh,
    Parking.discrepancyRate] using hm n hn
