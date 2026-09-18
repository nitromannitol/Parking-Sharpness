/-
Lemma 3.5 of parking.tex, frozen.  `parking.tex:739-751` (label `lem:transport`):

  "For every $t\geq0$ and every $n\geq0$,
   $\E A_t(0)=S_t$, $\E U_n(0)=\sum_{s<n}S_s$,
   and, for every $k\geq1$ with $\P(\eta(0)=k)>0$, the $k$ particles at the
   origin are exchangeable conditionally on $\eta(0)=k$, so that
   $S_t=\sum_{k\geq1}k\,\P(\eta(0)=k)\,\P(\tau_1>t\mid\eta(0)=k)$."

Exchangeability of the `k` particles at the origin is the invariance, on the
event `{η(0)=k}` the paper conditions on, of the joint law of their whole
activity histories under every permutation of the labels `(0,0), …, (0,k-1)`.
Version 2 restricts both laws to that event.  Version 1 recorded `η(0)` in the
pair instead of restricting, which asserted the invariance on every
realization, including those with `η(0) < k`, where a permutation moves an
index below `η(0)` to an index above it and the two laws differ; the witness
is in the shift record.
$\{\tau_i>t\}$ is the event that the particle labelled `(0, i)` is still
active after round `t`.  The last display is written with the joint
probabilities $\P(\eta(0)=k,\ \tau_1>t)$ rather than with conditional ones,
which is the same identity and never divides by a null probability.  The
integrability and summability the proof establishes are asserted alongside the
identities, so that no undefined integral or divergent series can satisfy them
through a junk value.
-/
import Parking.Support.SurvivorExpansion

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.transport (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ)
    (hprob : IsProbabilityMeasure ν) (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) :
    (∀ t : ℕ, Integrable (fun ω => (Parking.A ω t 0 : ℝ)) (Parking.law d ν) ∧
        Integrable (fun ω => (LatticeProb.survivorsFrom (Parking.toDriver ω) t 0 : ℝ))
          (Parking.law d ν) ∧
        ∫ ω, (Parking.A ω t 0 : ℝ) ∂(Parking.law d ν) = Parking.S (Parking.law d ν) t) ∧
    (∀ n : ℕ, Parking.meanU (Parking.law d ν) n
        = ∑ s ∈ Finset.range n, Parking.S (Parking.law d ν) s) ∧
    (∀ k : ℕ, 1 ≤ k → ν {(k : ℤ)} ≠ 0 → ∀ σ : Equiv.Perm ℕ, (∀ i, k ≤ i → σ i = i) →
        ((Parking.law d ν).restrict {ω : Parking.Data d | ω.1 0 = (k : ℤ)}).map
            (fun ω : Parking.Data d => fun q : ℕ × ℕ =>
              (LatticeProb.state (Parking.toDriver ω) q.1).active (0, σ q.2))
          = ((Parking.law d ν).restrict {ω : Parking.Data d | ω.1 0 = (k : ℤ)}).map
            (fun ω : Parking.Data d => fun q : ℕ × ℕ =>
              (LatticeProb.state (Parking.toDriver ω) q.1).active (0, q.2))) ∧
    (∀ t : ℕ, Summable (fun k : ℕ => ((k : ℝ) + 1) *
          ((Parking.law d ν) {ω | ω.1 0 = (k : ℤ) + 1 ∧
            (LatticeProb.state (Parking.toDriver ω) t).active (0, 0) = true}).toReal) ∧
        Parking.S (Parking.law d ν) t = ∑' k : ℕ, ((k : ℝ) + 1) *
          ((Parking.law d ν) {ω | ω.1 0 = (k : ℤ) + 1 ∧
            (LatticeProb.state (Parking.toDriver ω) t).active (0, 0) = true}).toReal)
-- FROZEN-STATEMENT-END
:= by
  haveI := hprob
  have hlaw : Parking.law d ν = Parking.dataLaw d (LatticeProb.iidLaw d ν) := rfl
  have hti : Parking.TranslationInvariant (LatticeProb.iidLaw d ν) :=
    fun v => Parking.iidLaw_map_shiftConf' ν v
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hmap : (LatticeProb.iidLaw d ν).map (fun η : Parking.Site d → ℤ => η 0) = ν := by
    show (MeasureTheory.Measure.infinitePi fun _ : Parking.Site d => ν).map
      (fun η : Parking.Site d → ℤ => η 0) = ν
    exact Measure.infinitePi_map_eval _ 0
  have hint' : Integrable (fun η : Parking.Site d → ℤ => |((η 0 : ℤ) : ℝ)|)
      (LatticeProb.iidLaw d ν) := by
    refine (integrable_map_measure (g := fun k : ℤ => |(k : ℝ)|)
      (f := fun η : Parking.Site d → ℤ => η 0) (μ := LatticeProb.iidLaw d ν) ?_
      (measurable_pi_apply (0 : Parking.Site d)).aemeasurable).mp ?_
    · rw [hmap]; exact hint.aestronglyMeasurable
    · rw [hmap]; exact hint
  rw [hlaw]
  refine ⟨fun t => ⟨Parking.integrable_A_data hd hti hint' t 0,
      Parking.integrable_survivorsFrom_data hd hti hint' t 0,
      Parking.mean_activity_eq_survivors hd hti hint' t⟩,
    fun n => Parking.meanU_eq_sum_S hd hti hint' n,
    fun k _ _ σ hσ => Parking.exchangeable_origin hd _ k σ hσ,
    fun t => Parking.S_expansion hd _ t
      (Parking.integrable_survivorsFrom_data hd hti hint' t 0)⟩
