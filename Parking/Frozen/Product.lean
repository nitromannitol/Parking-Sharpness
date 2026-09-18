/-
Lemma 10.2 of parking.tex, frozen.  `parking.tex:2321-2332` (label
`lem:product`), in the setting of `parking.tex:2303-2320` (the tilted law
$\P_\lambda(\eta(0)=j)=e^{\lambda j}\P(\eta(0)=j)/\E e^{\lambda\eta(0)}$ with
$0<\lambda_1<\theta$ chosen so small that $\P_\lambda$ has nonpositive mean for
$0\leq\lambda\leq\lambda_1$):

  "Fix $0\leq\lambda\leq\lambda_1$ and finitely many sites carrying the tilted
   law, and condition on the remaining randomness.  Let $F$ and $Z$ be
   functions of the counts, walks, and uniform variables at these sites, each
   invariant under relabeling the particles at a site.  Suppose $F$ takes
   values in $[0,1]$ and does not decrease when a particle is added.  Suppose
   $Z$ is nonnegative and integrable, does not increase when a particle is
   added, and changes by at most one when a single particle is added or
   deleted.  Then $|\Cov_\lambda(F,Z)|\leq3\,\partial_\lambda\E_\lambda F$."

The finitely many tilted sites and the conditioning on the remaining
randomness are `restrictLaw`, in which the sites of `N` carry the tilted law
with fresh walks and uniform variables while everything else is the fixed
background `ω₀`; `F` and `Z` are functions of the data at the sites of `N`
alone.  Adding a particle is `addAt`, which cancels a hole when the count is
negative and otherwise turns the next label at that site into a particle
carrying the walk and uniform variables already attached to it, and deleting
one is `delAt`.  The derivative is supplied as a hypothesis, so the statement
never reads the junk value of a derivative that does not exist, and the
covariance is asserted to be the covariance of integrable variables, so that
two undefined integrals cannot satisfy the bound through their junk values.
`F` and `Z` are measurable, which is what "functions of the counts, walks, and
uniform variables at these sites" asserts of them; without it the conclusion is
not a bound on a covariance of random variables, and the deletion and addition
comparisons the proof makes at configurations of another count cannot be read
off an almost sure class.
-/
import Parking.Support.TiltCov

open MeasureTheory

set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.product (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ)
    (hprob : IsProbabilityMeasure ν) (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (θ : ℝ) (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    (lam₁ : ℝ) (hlam₁ : 0 < lam₁) (hlam₁θ : lam₁ < θ)
    (hnonpos : ∀ s ∈ Set.Icc 0 lam₁,
      Integrable (fun k : ℤ => (k : ℝ)) (Parking.tiltLaw ν s) ∧
      ∫ k, (k : ℝ) ∂(Parking.tiltLaw ν s) ≤ 0)
    (lam : ℝ) (hlam : lam ∈ Set.Icc 0 lam₁)
    (N : Finset (Parking.Site d)) (ω₀ : Parking.PData d) (F Z : Parking.PData d → ℝ)
    (hFN : Parking.DependsOn N F) (hZN : Parking.DependsOn N Z)
    (hFrel : Parking.RelabelInvariant F) (hZrel : Parking.RelabelInvariant Z)
    (hFmeas : Measurable F) (hZmeas : Measurable Z)
    (hF01 : ∀ ω, F ω ∈ Set.Icc (0 : ℝ) 1)
    (hFmono : ∀ (x₀ : Parking.Site d) (ω : Parking.PData d), F ω ≤ F (Parking.addAt x₀ ω))
    (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hZint : Integrable Z (Parking.restrictLaw d N (Parking.tiltLaw ν lam) ω₀))
    (hZanti : ∀ (x₀ : Parking.Site d) (ω : Parking.PData d), Z (Parking.addAt x₀ ω) ≤ Z ω)
    (hZlip : ∀ (x₀ : Parking.Site d) (ω : Parking.PData d),
      |Z (Parking.addAt x₀ ω) - Z ω| ≤ 1 ∧ |Z (Parking.delAt x₀ ω) - Z ω| ≤ 1)
    (D : ℝ)
    (hD : HasDerivAt
      (fun s => ∫ ω, F ω ∂(Parking.restrictLaw d N (Parking.tiltLaw ν s) ω₀)) D lam) :
    Integrable (fun ω => F ω * Z ω) (Parking.restrictLaw d N (Parking.tiltLaw ν lam) ω₀) ∧
    |∫ ω, F ω * Z ω ∂(Parking.restrictLaw d N (Parking.tiltLaw ν lam) ω₀)
        - (∫ ω, F ω ∂(Parking.restrictLaw d N (Parking.tiltLaw ν lam) ω₀))
          * ∫ ω, Z ω ∂(Parking.restrictLaw d N (Parking.tiltLaw ν lam) ω₀)|
      ≤ 3 * D
-- FROZEN-STATEMENT-END
:= by
  letI : IsProbabilityMeasure ν := hprob
  obtain ⟨hlam0, hlamlam₁⟩ := hlam
  have hlamθ : lam < θ := lt_of_le_of_lt hlamlam₁ hlam₁θ
  obtain ⟨hmeanint, hmeanle⟩ := hnonpos lam ⟨hlam0, hlamlam₁⟩
  exact Parking.abs_cov_le_deriv hd hint hθ hexp hlam0 hlamθ hmeanint hmeanle
    hFN hFrel hZN hZrel hFmeas hZmeas hF01 hFmono hZanti hZlip hZint hD
