/-
Lemma 9.1 of parking.tex, frozen.  `parking.tex:1867-1876` (label
`lem:nearest-one-point`), in the setting of `parking.tex:1835-1866`
("Fix $d\geq5$; every constant below depends only on $d$.  For
$p\in(0,1/4]$, let $(\eta(x))_{x\in\Z^d}$ be i.i.d. with
$\P(\eta(0)=1)=\P(\eta(0)=-1)=p$, $\P(\eta(0)=0)=1-2p$", and
"$h_t=\P(H_t(0)=1)$, $m_t=\E U_t(0)$"):

  "There is $C<\infty$, depending only on $d$, such that, for every $t\geq0$,
   $x\in\Z^d$, and $r\geq2$,
   $(\E U_t(x)^r)^{1/r}\leq C(m_t+r)$, $m_t\leq C\log(1/h_t)$.
   Moreover, $h_t\downarrow0$."

The constant depends only on the dimension, so it is bound before `p`.
`h_t ↓ 0` is the conjunction of monotonicity and convergence to zero.  The
moment on the left is asserted finite alongside the bound, so that an undefined
integral cannot satisfy it through its junk value.  The martingale moment
inequality the proof quotes enters as an explicit hypothesis.
-/
import Parking.Support.NearestOnePointProof
import Parking.Support.Range
import Parking.External.Bernstein
import Parking.Support.ThreePointLaw

open MeasureTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.nearest_one_point (hBernstein : Parking.External.Bernstein) (d : ℕ) (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 0 < p → p ≤ 1 / 4 →
      (∀ (t : ℕ) (x : Parking.Site d) (r : ℝ), 2 ≤ r →
          Integrable (fun ω => (Parking.U ω t x : ℝ) ^ r)
            (Parking.law d (Parking.threePointLaw p)) ∧
          (∫ ω, (Parking.U ω t x : ℝ) ^ r ∂(Parking.law d (Parking.threePointLaw p))) ^ (1 / r)
            ≤ C * (Parking.meanU (Parking.law d (Parking.threePointLaw p)) t + r)) ∧
      (∀ t : ℕ, Parking.meanU (Parking.law d (Parking.threePointLaw p)) t
          ≤ C * Real.log (1 / Parking.holeProb d (Parking.threePointLaw p) t)) ∧
      Antitone (fun t : ℕ => Parking.holeProb d (Parking.threePointLaw p) t) ∧
      Tendsto (fun t : ℕ => Parking.holeProb d (Parking.threePointLaw p) t) atTop (𝓝 0)
-- FROZEN-STATEMENT-END
:= by
  exact Parking.nearest_one_point_proof hBernstein d hd
