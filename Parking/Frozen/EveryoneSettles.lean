/-
Proposition 7.3 of parking.tex, frozen.  `parking.tex:1486-1494` (label
`prop:everyone-settles`):

  "Let $\eta=(\eta(x))_{x\in\Z^d}$ have i.i.d. integer-valued coordinates.
   Suppose that $\eta(0)$ is nonconstant, $\E\eta(0)=0$, and
   $\E e^{\theta|\eta(0)|}<\infty$ for some $\theta>0$.  Then the following
   hold together on one event of probability one: every particle settles after
   finitely many rounds; every hole is filled after finitely many rounds; and
   infinitely many distinct particles leave every site, so that
   $U_\infty(x)=\infty$ for every $x\in\Z^d$."

"On one event of probability one" is the single almost-sure statement below.
"After finitely many rounds" is a time past which the property holds at every
later round.  A particle settles when its label stops being active; a hole at
`x` is filled when `H_t(x)` reaches zero; a particle leaves `x` in round
`t + 1` when it is active at `x` after round `t` and stands elsewhere after
round `t + 1`.  The
limiting odometer is read in `ℕ∞`, where "infinite" is the value `⊤` and not a
junk value.
-/
import Parking.External.SandpileGrowth
import Parking.External.Bernstein
import Parking.External.UConcentration
import Parking.External.GreenNorms
import Parking.Support.Error
import Parking.Support.Settles
import Parking.Support.AllInfinite
import Parking.Support.Departers

open MeasureTheory
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.everyone_settles (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration)
    (hGreenNorms : Parking.External.GreenNorms)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    ∀ᵐ ω ∂(Parking.law d ν),
      (∀ p : Parking.Label d, ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
          (LatticeProb.state (Parking.toDriver ω) t).active p = false) ∧
      (∀ x : Parking.Site d, ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → Parking.H ω t x = 0) ∧
      (∀ x : Parking.Site d, {p : Parking.Label d | ∃ t : ℕ,
          (LatticeProb.state (Parking.toDriver ω) t).active p = true ∧
            (LatticeProb.state (Parking.toDriver ω) t).pos p = x ∧
            (LatticeProb.state (Parking.toDriver ω) (t + 1)).pos p ≠ x}.Infinite) ∧
      (∀ x : Parking.Site d, Parking.Ulimit ω x = ⊤)
-- FROZEN-STATEMENT-END
:= by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  filter_upwards
    [Parking.ae_settle_and_fill hGrowth hBernstein hConcentration hGreenNorms d hd ν hν,
      Parking.ae_forall_Ulimit_top hGrowth hBernstein hConcentration hGreenNorms d hd ν hν,
      Parking.ae_stack_nbr hd (LatticeProb.iidLaw d ν)] with ω hsf htop hstep
  exact ⟨hsf.1, hsf.2, fun x => Parking.infinite_departers hstep hsf.1 (htop x), htop⟩
