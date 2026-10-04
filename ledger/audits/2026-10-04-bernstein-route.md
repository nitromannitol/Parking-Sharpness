# Route to `Parking.External.Bernstein` (Pinelis Rosenthal–Burkholder)

Status note for the discharge of `Parking.External.Bernstein`
(`~/lean/Parking-Sharpness/Parking/External/Bernstein.lean`, frozen).  The full bound is a
research-level result (Pinelis, *Optimum bounds for the distributions of martingales in Banach
spaces*, 1994); not reachable as a single bounded Lean step.  This file records exactly what is
proved, the route, and the remaining lemmas with signatures.

Repository: `~/lean/Lattice-Probability`, branch `rectangle-ergodic-reduction` (not switched).

## 0. The frozen target

`Parking.External.Bernstein : Prop` is
```
∃ C : ℝ, 0 < C ∧
  ∀ (Ω) [MeasurableSpace Ω] (μ) [IsProbabilityMeasure μ]
    (k : ℕ) (F : ℕ → MeasurableSpace Ω) (ξ : ℕ → Ω → ℝ) (r a : ℝ),
    Monotone F → (∀ i, F i ≤ ‹MeasurableSpace Ω›) →
    (∀ i, Measurable[F i] (ξ i)) → (∀ i, Integrable (ξ i) μ) →
    (∀ i, 1 ≤ i → i ≤ k → μ[ξ i | F (i - 1)] =ᵐ[μ] 0) →
    2 ≤ r → 0 < a →
    ((∀ i, 1 ≤ i → i ≤ k → ∀ ω, |ξ i ω| ≤ a) →
      (∫ ω, |∑ i ∈ Finset.Icc 1 k, ξ i ω| ^ r ∂μ) ^ (1 / r) ≤
        C * (Real.sqrt r *
            (∫ ω, (∑ i ∈ Finset.Icc 1 k, (μ[fun ω' => ξ i ω' ^ 2 | F (i - 1)]) ω) ^ (r / 2) ∂μ)
              ^ (1 / r) + r * a)) ∧
    (∀ v : ℝ, 0 < v → (∀ i q, Integrable (fun ω => |ξ i ω| ^ q) μ) →
      (∀ q : ℕ, 2 ≤ q → ∀ᵐ ω ∂μ,
          ∑ i ∈ Finset.Icc 1 k, (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω
            ≤ (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v) →
      (∫ ω, |∑ i ∈ Finset.Icc 1 k, ξ i ω| ^ r ∂μ) ^ (1 / r) ≤
        C * (Real.sqrt (r * v) + r * a))
```
Write `M_k = ∑_{i=1}^k ξ_i`, `v_i = μ[ξ_i² | F(i-1)]`, `V_k = ∑_{i=1}^k v_i`.  Clause 1 is the
bounded-increment Rosenthal bound; clause 2 is its factorial-moment (Bernstein) form.

## 1. What is already proved

* `LatticeProb.exists_abs_add_rpow_bound` (`Prob/PowerIneq.lean`): the pointwise second-order
  bound `|a+b|^p ≤ |a|^p + p|a|^{p-2}ab + C(|a|^{p-2}b² + |b|^p)` for `p ≥ 2`.
* `LatticeProb.exists_two_smooth_const` (`Prob/PowerIneq.lean`): the scalar two-smoothness
  algebra `u^{p/2} + C₁(u^{(p-2)/2}v + v^{p/2}) ≤ (u + C v)^{p/2}`.
* `LatticeProb.exists_lp_two_smooth` (`Prob/LpSmooth.lean`): `L^p` two-smoothness on a product of
  two probability spaces, `‖X+Y‖_p² ≤ ‖X‖_p² + C‖Y‖_p²` for `X = X(β)`, `∫ Y dκ = 0`.
* `LatticeProb.condExp_abs_add_rpow_eq` (`Prob/MartingaleRosenthal.lean`): the conditional
  second-order expansion
  `μ[|S+ξ|^p + p|S|^{p-2}Sξ + C(…)|m] =ᵐ |S|^p + C(|S|^{p-2}μ[ξ²|m] + μ[|ξ|^p|m])`.
* `LatticeProb.condExp_mul_mul_ae_eq_zero'` (`Prob/BernsteinMartingale.lean`): the linear term
  `μ[|S|^{p-2}Sξ|m] =ᵐ 0`.
* `LatticeProb.condExp_sq_le_rpow_condExp` (`Prob/BernsteinMartingale.lean`): the conditional
  Lyapunov bound `μ[ξ²|m] ≤ᵐ (μ[|ξ|^p|m])^{2/p}` for `p ≥ 2`.
* `LatticeProb.integral_abs_add_rpow_le` (`Prob/BernsteinMartingale.lean`): the integrated
  one-step estimate
  `∫|S+ξ|^p ≤ ∫|S|^p + C(∫|S|^{p-2}ξ² + ∫|ξ|^p)`.  **Step 1 of the `.DONE` remainder is done.**
* `LatticeProb.condExp_one_add_linear_quadratic`, `condExp_exp_le`, `condQvar`,
  `integral_exp_sub_condQvar_le_one`, `freedman_upper` (`Prob/Freedman.lean`): the conditional
  Bernstein mgf bound and the exponential supermartingale of a bounded martingale difference.

## 2. Clause 1 — the Rosenthal bound

### Step A — instantiate the one-step estimate along the filtration (routine)

Set `S i ω = ∑ j ∈ Finset.Icc 1 i, ξ j ω` (so `S 0 = 0`, `S i = S (i-1) + ξ i`).  For `1 ≤ i ≤ k`,
`S (i-1)` is `F (i-1)`-strongly-measurable and `μ[ξ i | F (i-1)] = 0`; the pull-out
`condExp_mul_of_stronglyMeasurable_left` gives `∫|S(i-1)|^{p-2}ξ i² = ∫|S(i-1)|^{p-2} v_i`.
Applying `integral_abs_add_rpow_le` at `m := F (i-1)`, `S := S (i-1)`, `ξ := ξ i`, `p := r`, yields

```
theorem one_step {F : Filtration ℕ m₀} {ξ : ℕ → Ω → ℝ} {v : ℕ → Ω → ℝ}
    (hξ : ∀ i, μ[ξ i | F (i-1)] =ᵐ[μ] 0)
    (hv : ∀ i, μ[fun ω => ξ i ω ^ 2 | F (i-1)] =ᵐ[μ] v i)
    (p : ℝ) (hp : 2 ≤ p) {C : ℝ}
    (hC : ∀ a b, |a+b|^p ≤ |a|^p + p*|a|^(p-2)*a*b + C*(|a|^(p-2)*b^2 + |b|^p)) :
    ∀ i, ∫ ω, |S ξ i ω|^p ∂μ ≤ ∫ ω, |S ξ (i-1) ω|^p ∂μ
      + C * (∫ ω, |S ξ (i-1) ω|^(p-2) * v i ω ∂μ + ∫ ω, |ξ i ω|^p ∂μ)
```

### Step B — Hölder and the Lyapunov bound (routine)

`∫ |S(i-1)|^{p-2} v_i ≤ (∫|S(i-1)|^p)^{(p-2)/p} (∫ v_i^{p/2})^{2/p}` by Hölder with exponents
`p/(p-2)` and `p/2` (the library's `integral_mul_le_Lp_mul_Lq_of_nonneg`).  Writing
`A i = ∫|S i|^p`, `b i = (∫ v_i^{p/2})^{2/p}`, `c i = ∫|ξ i|^p`:

```
theorem rosenthal_recursion ... : ∀ i, A i ≤ A (i-1) + C * (A (i-1) ^ ((p-2)/p) * b i + c i)
```

### Step C — the Pinelis induction (**the hard remaining lemma**)

This is the substantive gap.  What is needed is the martingale Rosenthal inequality itself, in
the cumulative form used by the frozen statement:

```
theorem exists_martingale_rosenthal :
    ∃ K : ℝ, 0 < K ∧ ∀ (p : ℝ), 2 ≤ p → ∀ {Ω} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] {m₀} (F : Filtration ℕ m₀) (ξ : ℕ → Ω → ℝ),
      (∀ i, StronglyMeasurable[F i] (ξ i)) →
      (∀ i, μ[ξ i | F (i-1)] =ᵐ[μ] 0) →
      ∀ k, (∫ ω, |∑ i ∈ Finset.Icc 1 k, ξ i ω| ^ p ∂μ) ^ (2/p) ≤
        K^2 * ( (∫ ω, (∑ i ∈ Finset.Icc 1 k, (μ[fun ω' => ξ i ω'^2 | F (i-1)]) ω) ^ (p/2) ∂μ) ^ (2/p)
          + (∑ i ∈ Finset.Icc 1 k, (∫ ω, |ξ i ω|^p ∂μ) ^ (2/p)) )
```

Two known routes; both are the hard part.

* **Pinelis's second-order induction.**  Start from Step B and bootstrap on `i`.  The naive
  recursion `A i ≤ A (i-1) + C(A(i-1)^{(p-2)/p} b i + c i)` is *too weak*: summing it controls
  `∑ ‖v_i‖_{p/2}`, whereas clause 1 needs `‖V_k‖_{p/2} ≤ ∑ ‖v_i‖_{p/2}` (Minkowski, wrong
  direction).  The correct proof keeps the cumulative `V_k` and uses the deterministic
  two-smoothness `exists_two_smooth_const` (resp. `exists_lp_two_smooth`) to fold the cross term
  into the power of a single running variable `|S_i|² + C V_i`, then a Gronwall/induction on
  `E[(|S_i|² + C V_i)^{p/2}]`.  The exact missing algebraic step:
  ```
  lemma rosenthal_cumulative :
    ∃ K, ∀ {u w : ℝ}, 0 ≤ u → 0 ≤ w →
      u ^ (p/2) + C * (u ^ ((p-2)/2) * w + w ^ (p/2)) ≤ (u + K * w) ^ (p/2)
  ```
  is exactly `exists_two_smooth_const`; what remains is its *conditional/martingale* lift to the
  process `(S_i, V_i)` and the induction that shows
  `E[(|S_k|² + K V_k)^{p/2}] ≤ K^p E[(V_k + …)^{p/2}]`.
* **BDG + predictable-QV comparison.**  Prove the Burkholder–Davis–Gundy inequality
  `E|M_k|^p ≤ C_p E[(∑ ΔM_i²)^{p/2}]` for `p ≥ 2` (via `exists_lp_two_smooth` and a good-λ
  argument), then the comparison `E[(∑ ΔM_i²)^{p/2}] ≤ C_p (E V_k^{p/2} + Σ E|ξ_i|^p)`; the second
  term is the `ra` summand.  This is the route of Pinelis, Section 4; it is not in Mathlib.

### Step D — bounded case

With `|ξ_i| ≤ a`, `c i = ∫|ξ_i|^p ≤ a^{p-2}∫|ξ_i|² ≤ a^{p-2} b i` (Lyapunov, `condExp_sq_le_rpow_condExp`
in conditional form), and `∑ c_i ≤ a^{p-2} ∑ b_i`; combined with Step C this gives Clause 1 with
the `r a` term.  Choose `C := max(K, 1)`; the `√r` and `r` factors are supplied by the
`p`-dependent constant of Step C together with the standard sharp constants
(`K ≍ √p`, `K² ≍ p`).

## 3. Clause 2 — the factorial-moment form

### Step E — factorial condition ⟹ conditional mgf (**remaining**)

From the hypothesis `∑_i μ[|ξ_i|^q | F(i-1)] ≤ (q!/2) a^{q-2} v` a.s. for all `q ≥ 2`, the
exponential series with the conditional MCT/DCT (the technique of
`condExp_one_add_linear_quadratic` / `condExp_exp_le`) gives, for `λ ≥ 0`,
```
theorem condExp_exp_le_of_factorial :
    ∀ᵐ ω ∂μ, μ[fun ω' => Real.exp (λ * (∑ i ∈ Finset.Icc 1 k, ξ i ω')) | m₀] ω
      ≤ Real.exp (λ ^ 2 * v / (2 * (1 - a * λ)))
```
for `0 ≤ λ < 1/a`.  The `q = 0, 1` terms contribute `1` and `0` (martingale difference); the
`q ≥ 2` terms are dominated by `(λ²v/2) ∑_{j≥0} (aλ)^j = λ²v/(2(1-aλ))`, then `1 + z ≤ e^z`.
This is a self-contained series argument; the only subtlety is the conditional interchange of
sum and conditional expectation (Mathlib: `condExp_tsum` / monotone convergence under `condExp`).

### Step F — tail/moment integration (**remaining**)

The conditional mgf bound is a Bernstein (sub-exponential) bound; the exponential supermartingale
machinery is already in `Freedman.lean` (`integral_exp_sub_condQvar_le_one`, `freedman_upper`).
Either:
* derive the tail `P(M_k ≥ t) ≤ exp(-t²/(2(v + a t)))` and integrate `r t^{r-1}` against it using
  the deterministic lemma below; or
* feed `v` and the level `a` into the clause-1 machinery via the standard truncation
  `ξ_i ↦ ξ_i 1{|ξ_i| ≤ a}` plus the factorial hypothesis to control the truncated part.

Deterministic integration core:
```
lemma integral_rpow_exp_bernstein (r a v : ℝ) (hr : 2 ≤ r) (ha : 0 < a) (hv : 0 < v) :
    ∫ t in Set.Ioi 0, r * t ^ (r-1) * Real.exp (-(t^2 / (2 * (v + a * t)))) ≤
      K ^ r * (r ^ (r/2) * v ^ (r/2) + (r * a) ^ r)
```
(and its `2·` two-sided companion), with a universal `K`.

## 4. Assembly

1. Prove `exists_martingale_rosenthal` (Step C) and `condExp_exp_le_of_factorial` +
   the tail/moment lemma (Steps E–F).
2. Bundle into a `Parking.External.Bernstein` proof: `C := max(1, K₁, K₂)` universal; the two
   clauses are the bounded and factorial cases.  Clause 2 uses `v` as the frozen statement's
   `v`; clause 1 uses `v := V_k` and `a`.
3. Put the result in `Parking/External/BernsteinProved.lean` as
   `theorem Parking.External.bernstein : Parking.External.Bernstein` importing
   `LatticeProb.Prob.BernsteinMartingale` (and the Step C/E/F modules), then replace the
   `Frozen`/`External` hypothesis in the 7 dependent nodes by the proved theorem.
4. Check `#print axioms Parking.External.bernstein` is exactly
   `{propext, Classical.choice, Quot.sound}` (no `sorryAx`), and that the frozen statement hash is
   untouched.

## 5. Exact remaining Lean obligations

| # | lemma | status |
|---|---|---|
| 1 | `LatticeProb.integral_abs_add_rpow_le` | **done** (`BernsteinMartingale.lean`) |
| 2 | `LatticeProb.condExp_sq_le_rpow_condExp` | **done** (`BernsteinMartingale.lean`) |
| 3 | `LatticeProb.condExp_mul_mul_ae_eq_zero'` | **done** (`BernsteinMartingale.lean`) |
| 4 | `one_step` (filtration instantiation + pull-out) | routine, not written |
| 5 | `exists_martingale_rosenthal` (Step C, cumulative form) | **hard / open** |
| 6 | `condExp_exp_le_of_factorial` (Step E) | bounded but nontrivial (series + condExp MCT) |
| 7 | `integral_rpow_exp_bernstein` (Step F, real analysis) | bounded but nontrivial |
| 8 | assembly + `BernsteinProved.lean` | depends on 4–7 |

Steps 4, 6, 7 are each expected to be a bounded Lean file; step 5 is the research-level core and
is the only genuine blocker.  If a weaker but sufficient form of Clause 1 is acceptable at the
call sites (e.g. with `k a²` in place of the sharp `V_k`), Step 5 can be replaced by the
per-step two-smoothness `exists_lp_two_smooth`, which is already in the library; that is a
mathematical decision for the director, not a transcription change (the frozen statement stays
as it is).
