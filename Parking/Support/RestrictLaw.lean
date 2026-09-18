/-
Conditioning on the randomness away from the tilted sites.

`lem:product` (`parking.tex:2321-2332`) fixes "finitely many sites carrying the
tilted law" and conditions on the remaining randomness, which is `restrictLaw`:
the sites of `N` are random and everything else is a fixed background `ω₀`.  Its
observables are functions of the data at the sites of `N` alone, and such a
functional does not see the background at all: `restrictLaw` is the image of the
full product law under the map that keeps the data at `N` and replaces the rest
by `ω₀`, and that map does not change the value of such a functional.  So its
mean, its integrability and hence its covariance with another such functional
are the same under `restrictLaw` and under the full product law, where the
counts, the walks and the uniform variables are three independent fields.
-/
import Parking.Support.Range

open MeasureTheory

noncomputable section

namespace Parking

/-- The configuration that reads `ω` at the sites of `N` and the background `ω₀`
everywhere else. -/
def keepAt {d : ℕ} (N : Finset (Site d)) (ω₀ ω : PData d) : PData d :=
  ((fun x => if x ∈ N then ω.1 x else ω₀.1 x),
    (fun q : Label d × ℕ => if q.1.1 ∈ N then ω.2.1 q else ω₀.2.1 q),
    (fun q : Label d × ℕ => if q.1.1 ∈ N then ω.2.2 q else ω₀.2.2 q))

theorem restrictLaw_eq_map {d : ℕ} (N : Finset (Site d)) (ν : Measure ℤ) (ω₀ : PData d) :
    restrictLaw d N ν ω₀ = (pDataLaw d ν).map (keepAt N ω₀) := rfl

theorem measurable_keepAt {d : ℕ} (N : Finset (Site d)) (ω₀ : PData d) :
    Measurable (keepAt N ω₀) := by
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · refine measurable_pi_lambda _ fun x => ?_
    by_cases hx : x ∈ N
    · simpa [hx] using (measurable_fst.eval : Measurable fun ω : PData d => ω.1 x)
    · simp [hx]
  · refine measurable_pi_lambda _ fun q => ?_
    by_cases hq : q.1.1 ∈ N
    · simpa [hq] using
        (measurable_snd.fst.eval : Measurable fun ω : PData d => ω.2.1 q)
    · simp [hq]
  · refine measurable_pi_lambda _ fun q => ?_
    by_cases hq : q.1.1 ∈ N
    · simpa [hq] using
        (measurable_snd.snd.eval : Measurable fun ω : PData d => ω.2.2 q)
    · simp [hq]

/-- A functional of the data at the sites of `N` does not see the background. -/
theorem DependsOn.keepAt {d : ℕ} {N : Finset (Site d)} {F : PData d → ℝ}
    (hF : Parking.DependsOn N F) (ω₀ ω : PData d) : F (keepAt N ω₀ ω) = F ω := by
  refine hF _ _ ?_ ?_ ?_
  · intro x hx; simp [Parking.keepAt, hx]
  · intro q hq; simp [Parking.keepAt, hq]
  · intro q hq; simp [Parking.keepAt, hq]

variable {d : ℕ} {N : Finset (Site d)} {ν : Measure ℤ} {ω₀ : PData d} {F : PData d → ℝ}

/-- A functional of the data at the sites of `N` has the same integral under the
law in which only those sites are random and under the law in which every site
is random. -/
theorem integral_restrictLaw [IsProbabilityMeasure ν] (hF : Parking.DependsOn N F)
    (hFm : Measurable F) :
    ∫ ω, F ω ∂(restrictLaw d N ν ω₀) = ∫ ω, F ω ∂(pDataLaw d ν) := by
  rw [restrictLaw_eq_map, integral_map (measurable_keepAt N ω₀).aemeasurable
    hFm.aestronglyMeasurable]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => hF.keepAt ω₀ ω)

/-- The same for integrability. -/
theorem integrable_restrictLaw_iff [IsProbabilityMeasure ν] (hF : Parking.DependsOn N F)
    (hFm : Measurable F) :
    Integrable F (restrictLaw d N ν ω₀) ↔ Integrable F (pDataLaw d ν) := by
  rw [restrictLaw_eq_map, integrable_map_measure hFm.aestronglyMeasurable
    (measurable_keepAt N ω₀).aemeasurable]
  constructor
  · intro h
    exact h.congr (Filter.Eventually.of_forall fun ω => hF.keepAt ω₀ ω)
  · intro h
    exact h.congr (Filter.Eventually.of_forall fun ω => (hF.keepAt ω₀ ω).symm)

end Parking

end
