/-
Lemma 3.7 of parking.tex, frozen.  `parking.tex:803-813` (label
`lem:density-compare`):

  "Let $\eta$ and $\widetilde\eta$ have finite first moments and admit a
   translation invariant coupling under which $\eta(x)\leq\widetilde\eta(x)$
   for every $x$ almost surely.  Let $S_t$ and $\widetilde S_t$ be the two
   expected numbers of particles which start at the origin and are still active
   after round $t$.  Then, for every $t\geq0$,
   $0\leq\widetilde S_t-S_t\leq\E\widetilde\eta(0)-\E\eta(0)$."

A coupling is a probability measure on pairs of configurations with the two
marginals; it is translation invariant when the diagonal translation of the
pair preserves it.  The two processes are driven by their own stacks and
uniform variables, as the definition of `S_t` requires.  The finiteness of the
two expected survivor counts is asserted alongside the inequalities, so that
two undefined integrals cannot satisfy them through their junk values.
-/
import Parking.Support.DensityCompare

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.density_compare (d : ℕ) (hd : 1 ≤ d)
    (μ μ' : Measure (Parking.Site d → ℤ))
    (hprob : IsProbabilityMeasure μ) (hprob' : IsProbabilityMeasure μ')
    (hint : Integrable (fun η : Parking.Site d → ℤ => |((η 0 : ℤ) : ℝ)|) μ)
    (hint' : Integrable (fun η : Parking.Site d → ℤ => |((η 0 : ℤ) : ℝ)|) μ')
    (Q : Measure ((Parking.Site d → ℤ) × (Parking.Site d → ℤ)))
    (hQ : IsProbabilityMeasure Q) (hfst : Q.map Prod.fst = μ) (hsnd : Q.map Prod.snd = μ')
    (hQti : ∀ v : Parking.Site d,
      Q.map (fun c => (Parking.shiftConf v c.1, Parking.shiftConf v c.2)) = Q)
    (hmono : ∀ᵐ c ∂Q, ∀ x, c.1 x ≤ c.2 x) (t : ℕ) :
    Integrable (fun ω => (LatticeProb.survivorsFrom (Parking.toDriver ω) t 0 : ℝ))
        (Parking.dataLaw d μ) ∧
      Integrable (fun ω => (LatticeProb.survivorsFrom (Parking.toDriver ω) t 0 : ℝ))
        (Parking.dataLaw d μ') ∧
    0 ≤ Parking.S (Parking.dataLaw d μ') t - Parking.S (Parking.dataLaw d μ) t ∧
      Parking.S (Parking.dataLaw d μ') t - Parking.S (Parking.dataLaw d μ) t
        ≤ ∫ η, ((η 0 : ℤ) : ℝ) ∂μ' - ∫ η, ((η 0 : ℤ) : ℝ) ∂μ
-- FROZEN-STATEMENT-END
:= by
  haveI := hprob
  haveI := hprob'
  haveI := hQ
  have hti : Parking.TranslationInvariant μ :=
    Parking.translationInvariant_of_coupling hfst hQti
  have hti' : Parking.TranslationInvariant μ' :=
    Parking.translationInvariant_of_coupling' hsnd hQti
  have hI := Parking.integrable_survivorsFrom_data hd hti hint t 0
  have hI' := Parking.integrable_survivorsFrom_data hd hti' hint' t 0
  refine ⟨hI, hI', ?_, ?_⟩
  · have h := Parking.S_mono_of_coupling hd hfst hsnd hmono t hI hI'
    linarith
  · have hSA := Parking.mean_activity_eq_survivors hd hti hint t
    have hSA' := Parking.mean_activity_eq_survivors hd hti' hint' t
    have hAH := Parking.activity_holes_main hd hti hint t
    have hAH' := Parking.activity_holes_main hd hti' hint' t
    have hH := Parking.H_mean_mono_of_coupling hd hfst hsnd hmono t
      (Parking.integrable_H_data hd hti hint t 0)
      (Parking.integrable_H_data hd hti' hint' t 0)
    linarith
