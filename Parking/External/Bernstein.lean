/-
External input: the martingale Rosenthal-Burkholder inequalities the paper
quotes (`parking.tex:1165-1178`, `lem:bernstein`) from Pinelis, Theorems 4.1
and 3.3 there.

Assumed here.  It enters only as an explicit hypothesis of the results whose
proofs use it.  The constant is universal, so it is bound before every other
datum of the statement.
-/
import Parking.Basic

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
/-- "Let $(\mathcal F_i)_{i=0}^k$ be a filtration, let $(\xi_i)_{i=1}^k$ be
martingale differences for it, let $r\geq2$, and let $a>0$.  If
$|\xi_i|\leq a$ for every $1\leq i\leq k$, then
$(\E|\sum\xi_i|^r)^{1/r}\leq C(\sqrt r(\E[\sum\E[\xi_i^2\mid\mathcal
F_{i-1}]]^{r/2})^{1/r}+ra)$, with $C$ universal.  If instead there is $v>0$
such that, almost surely, $\sum\E[|\xi_i|^q\mid\mathcal F_{i-1}]\leq
\frac{q!}2a^{q-2}v$ for every integer $q\geq2$, then
$(\E|\sum\xi_i|^r)^{1/r}\leq C(\sqrt{rv}+ra)$, again with $C$ universal." -/
def Parking.External.Bernstein : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (k : ℕ) (F : ℕ → MeasurableSpace Ω) (ξ : ℕ → Ω → ℝ) (r a : ℝ),
      Monotone F → (∀ i, F i ≤ ‹MeasurableSpace Ω›) →
      (∀ i, Measurable[F i] (ξ i)) → (∀ i, Integrable (ξ i) μ) →
      (∀ i, 1 ≤ i → i ≤ k → μ[ξ i | F (i - 1)] =ᵐ[μ] 0) →
      2 ≤ r → 0 < a →
      ((∀ i, 1 ≤ i → i ≤ k → ∀ ω, |ξ i ω| ≤ a) →
        (∫ ω, |∑ i ∈ Finset.Icc 1 k, ξ i ω| ^ r ∂μ) ^ (1 / r) ≤
          C * (Real.sqrt r *
              (∫ ω, (∑ i ∈ Finset.Icc 1 k, (μ[fun ω' => ξ i ω' ^ 2 | F (i - 1)]) ω) ^ (r / 2) ∂μ)
                ^ (1 / r)
            + r * a)) ∧
      (∀ v : ℝ, 0 < v → (∀ (i : ℕ) (q : ℕ), Integrable (fun ω => |ξ i ω| ^ q) μ) →
        (∀ q : ℕ, 2 ≤ q → ∀ᵐ ω ∂μ,
            ∑ i ∈ Finset.Icc 1 k, (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω
              ≤ (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v) →
        (∫ ω, |∑ i ∈ Finset.Icc 1 k, ξ i ω| ^ r ∂μ) ^ (1 / r) ≤
          C * (Real.sqrt (r * v) + r * a))
-- FROZEN-STATEMENT-END
