/-
Lemma 5.4 of parking.tex, frozen.  `parking.tex:1125-1138` (label
`lem:w-martingale`):

  "Fix $n\geq2$.  There are a filtration $(\mathcal F_i)_{i\geq0}$ and random
   variables $(\xi_i)_{i\geq1}$, only finitely many of which are nonzero almost
   surely, such that $w_n(0)=\sum_i\xi_i$ and, for every $i\geq1$,
   $\E[\xi_i\mid\mathcal F_{i-1}]=0$,
   $|\xi_i|\leq\max_{m<n}\max_y\max_{z\sim y}|g_m(z)-(Pg_m)(y)|$.
   Moreover
   $\sum_i\E[\xi_i^2\mid\mathcal F_{i-1}]
    =\sum_{s=1}^{n-1}\sum_yA_{s-1}(y)\Gamma_{n-s}(y)$."

The family is indexed here from zero, so the paper's `ξ_i` is `ξ (i-1)` and the
paper's `\mathcal F_{i-1}` is `F i`; that removes the truncated subtraction
without changing the statement.  "Only finitely many nonzero" is the existence
of an index past which they all vanish.  The two sums over the lattice and over
the index are asserted summable alongside the identity, so that a divergent
series cannot satisfy it through the junk value of a nonsummable `tsum`.
-/
import Parking.Support.WQuadratic

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.w_martingale (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ)
    (hprob : IsProbabilityMeasure ν) (n : ℕ) (hn : 2 ≤ n) :
    ∃ (F : ℕ → MeasurableSpace (Parking.Data d)) (ξ : ℕ → Parking.Data d → ℝ),
      Monotone F ∧ (∀ i, F i ≤ inferInstanceAs (MeasurableSpace (Parking.Data d))) ∧ (∀ i, Measurable[F (i + 1)] (ξ i)) ∧
      (∀ i, Integrable (ξ i) (Parking.law d ν)) ∧
      (∀ᵐ ω ∂(Parking.law d ν), ∃ N, ∀ i, N ≤ i → ξ i ω = 0) ∧
      (∀ᵐ ω ∂(Parking.law d ν), Parking.wErr ω n 0 = ∑' i, ξ i ω) ∧
      (∀ i, (Parking.law d ν)[ξ i | F i] =ᵐ[Parking.law d ν] 0) ∧
      (∀ i, ∀ ω, |ξ i ω| ≤ Parking.greenIncrement d n) ∧
      (∀ᵐ ω ∂(Parking.law d ν),
        Summable (fun i => ((Parking.law d ν)[fun ω' => ξ i ω' ^ 2 | F i]) ω) ∧
        ∀ s : ℕ, Summable fun y : Parking.Site d =>
          (Parking.A ω (s - 1) y : ℝ) * Parking.gamma d (n - s) y) ∧
      (fun ω => ∑' i, ((Parking.law d ν)[fun ω' => ξ i ω' ^ 2 | F i]) ω)
        =ᵐ[Parking.law d ν] fun ω => ∑ s ∈ Finset.Icc 1 (n - 1), ∑' y : Parking.Site d,
          (Parking.A ω (s - 1) y : ℝ) * Parking.gamma d (n - s) y
-- FROZEN-STATEMENT-END
:= by
  classical
  haveI := hprob
  set i₀ : Fin d := ⟨0, hd⟩ with hi₀
  have hn1 : 1 ≤ n := by omega
  have hae : ∀ᵐ ω ∂(Parking.law d ν), ∀ i : ℕ,
      ((Parking.law d ν)[fun ω' => Parking.wXi i₀ n i ω' ^ 2 |
        Parking.wFiltration i₀ n i]) ω = Parking.wGamma i₀ n i ω :=
    MeasureTheory.ae_all_iff.mpr fun i => Parking.condExp_wXi_sq hd i₀ ν n hn1 i
  refine ⟨Parking.wFiltration i₀ n, Parking.wXi i₀ n,
    Parking.wFiltration_mono i₀ n, Parking.wFiltration_le i₀ n,
    Parking.measurable_wXi_wFiltration i₀ n,
    fun i => Parking.integrable_wXi hd i₀ ν n hn1 i,
    Filter.Eventually.of_forall fun ω => ⟨_, Parking.wXi_eventually_zero i₀ n ω⟩,
    Parking.wErr_ae_eq_tsum_wXi hd i₀ ν n,
    fun i => Parking.condExp_wXi hd i₀ ν n hn1 i,
    fun i ω => Parking.abs_wXi_le hd i₀ n hn1 i ω, ?_, ?_⟩
  · refine (hae.and (Parking.ae_stack_nbr_law hd ν)).mono fun ω hω => ⟨?_, ?_⟩
    · have hfun : (fun i => ((Parking.law d ν)[fun ω' => Parking.wXi i₀ n i ω' ^ 2 |
          Parking.wFiltration i₀ n i]) ω) = fun i => Parking.wGamma i₀ n i ω :=
        funext hω.1
      rw [hfun]
      exact Parking.summable_wGamma hd i₀ n ω
    · intro s
      exact Parking.summable_A_gamma ω n s
  · refine (hae.and (Parking.ae_stack_nbr_law hd ν)).mono fun ω hω => ?_
    show ∑' i : ℕ, ((Parking.law d ν)[fun ω' => Parking.wXi i₀ n i ω' ^ 2 |
        Parking.wFiltration i₀ n i]) ω
      = ∑ s ∈ Finset.Icc 1 (n - 1), ∑' y : Parking.Site d,
          (Parking.A ω (s - 1) y : ℝ) * Parking.gamma d (n - s) y
    have hfun : (fun i => ((Parking.law d ν)[fun ω' => Parking.wXi i₀ n i ω' ^ 2 |
        Parking.wFiltration i₀ n i]) ω) = fun i => Parking.wGamma i₀ n i ω :=
      funext hω.1
    rw [show (∑' i : ℕ, ((Parking.law d ν)[fun ω' => Parking.wXi i₀ n i ω' ^ 2 |
        Parking.wFiltration i₀ n i]) ω) = ∑' i : ℕ, Parking.wGamma i₀ n i ω from
      congrArg tsum hfun]
    exact Parking.tsum_wGamma_eq hd i₀ n ω hω.2
