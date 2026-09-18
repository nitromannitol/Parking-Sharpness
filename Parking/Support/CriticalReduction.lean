/-
Step 3 of the proof of `lem:critical-density` (`parking.tex:1320-1338`), the part
that is deterministic once the coupling of Steps 1 and 2 has produced the
survivor bound.

The paper's Step 3 ends with `S_t ≥ 1/(16t)` for `t ≥ 1/(2γ)`, and then reads
both conclusions off it: `liminf_t t S_t ≥ 1/16` is immediate, and summing over
`1/(2γ) ≤ t < n` gives `E U_n(0) ≥ c log n - C`, because `E U_n(0) = ∑_{s<n} S_s`
(`lem:transport`) and `∑_{T ≤ s < n} 1/s ≥ log n - log T`, the left endpoint rule
for the integral of `1/x`.

What remains of the node after this file is exactly the survivor bound: a
threshold past which `S_t ≥ 1/(16t)`.
-/
import Parking.Frozen.Transport

noncomputable section

namespace Parking

open MeasureTheory Filter Topology LatticeProb

variable {d : ℕ}

/-! ### The harmonic sum against the logarithm -/

/-- The left endpoint rule: `∑_{T ≤ s < n} 1/s ≥ log n - log T` for `1 ≤ T`. -/
theorem log_sub_log_le_sum_inv {T : ℕ} (hT : 1 ≤ T) :
    ∀ n : ℕ, T ≤ n →
      Real.log n - Real.log T ≤ ∑ s ∈ Finset.Ico T n, (1 : ℝ) / (s : ℝ) := by
  intro n hn
  induction n with
  | zero =>
      have : T = 0 := Nat.le_zero.mp hn
      omega
  | succ m ih =>
      rcases Nat.lt_or_ge m T with hlt | hge
      · -- `m < T ≤ m + 1` forces `T = m + 1` and the sum is empty
        have hTm : T = m + 1 := le_antisymm hn (by omega)
        subst hTm
        simp
      · have hm : (1 : ℝ) ≤ (m : ℝ) := by
          have : 1 ≤ m := le_trans hT hge
          exact_mod_cast this
        have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
        have hstep : Real.log ((m : ℝ) + 1) - Real.log m ≤ 1 / (m : ℝ) := by
          have hpos : (0 : ℝ) < ((m : ℝ) + 1) / (m : ℝ) := by positivity
          have hlog := Real.log_le_sub_one_of_pos hpos
          rw [Real.log_div (by linarith) (ne_of_gt hm0)] at hlog
          have hdiv : ((m : ℝ) + 1) / (m : ℝ) - 1 = 1 / (m : ℝ) := by
            field_simp
            ring
          linarith
        have hsum : ∑ s ∈ Finset.Ico T (m + 1), (1 : ℝ) / (s : ℝ)
            = (∑ s ∈ Finset.Ico T m, (1 : ℝ) / (s : ℝ)) + 1 / (m : ℝ) :=
          Finset.sum_Ico_succ_top hge _
        have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        rw [hsum, hcast]
        have := ih hge
        linarith

/-! ### The two conclusions from the survivor bound -/

theorem S_nonneg (P : Measure (Data d)) (t : ℕ) : 0 ≤ S P t :=
  integral_nonneg fun _ => Nat.cast_nonneg _

/-- **Step 3 of `lem:critical-density`.**  From `S_t ≥ 1/(16t)` past a threshold,
the two conclusions of the lemma follow: `t S_t ≥ 1/16` from that threshold on,
which is the content of the paper's `liminf_t t S_t ≥ 1/16`, and the logarithmic
lower bound on the mean odometer.

The first conclusion is stated as the eventual bound rather than as a `liminf`.
In `ℝ` the `liminf` of a sequence with no eventual upper bound is the junk value
`0`, since `sSup` of an unbounded set is `0`; below dimension four `t S_t` grows
like `t^{(4-d)/4}`, so the `liminf` written in `ℝ` is `0` there.  The finding is
recorded in the shift status file. -/
theorem critical_density_of_survivor_bound (hd : 1 ≤ d) (ν : Measure ℤ)
    (hprob : IsProbabilityMeasure ν) (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    {T : ℕ} (hT : 1 ≤ T)
    (hS : ∀ t : ℕ, T ≤ t → (1 : ℝ) / (16 * (t : ℝ)) ≤ S (law d ν) t) :
    (∀ t : ℕ, T ≤ t → (1 / 16 : ℝ) ≤ (t : ℝ) * S (law d ν) t) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        (1 / 16 : ℝ) * Real.log n - C ≤ meanU (law d ν) n := by
  have hexp : ∀ n : ℕ, meanU (law d ν) n = ∑ s ∈ Finset.range n, S (law d ν) s :=
    (Parking.Frozen.transport d hd ν hprob hint).2.1
  constructor
  · intro t ht
    have ht0 : (0 : ℝ) < (t : ℝ) := by
      have h1 : 1 ≤ t := le_trans hT ht
      have : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast h1
      linarith
    have h := hS t ht
    have hkey : (1 / 16 : ℝ) = (t : ℝ) * ((1 : ℝ) / (16 * (t : ℝ))) := by
      field_simp
    rw [hkey]
    exact mul_le_mul_of_nonneg_left h (le_of_lt ht0)
  · refine ⟨(1 / 16 : ℝ) * Real.log T + 1, ?_, fun n hn => ?_⟩
    · have : (0 : ℝ) ≤ Real.log T := Real.log_nonneg (by exact_mod_cast hT)
      linarith
    rcases Nat.lt_or_ge n T with hlt | hge
    · have hlog : Real.log n ≤ Real.log T := by
        refine Real.log_le_log ?_ ?_
        · have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          linarith
        · exact_mod_cast le_of_lt hlt
      have h0 : 0 ≤ meanU (law d ν) n := by
        rw [hexp n]
        exact Finset.sum_nonneg fun s _ => S_nonneg _ s
      linarith
    · have hterm : ∀ s ∈ Finset.Ico T n,
          (1 / 16 : ℝ) * ((1 : ℝ) / (s : ℝ)) ≤ S (law d ν) s := by
        intro s hs
        rw [Finset.mem_Ico] at hs
        have h := hS s hs.1
        have hs0 : (0 : ℝ) < (s : ℝ) := by
          have h1 : 1 ≤ s := le_trans hT hs.1
          have : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast h1
          linarith
        calc (1 / 16 : ℝ) * ((1 : ℝ) / (s : ℝ)) = (1 : ℝ) / (16 * (s : ℝ)) := by
              field_simp
          _ ≤ S (law d ν) s := h
      have hsplit : ∑ s ∈ Finset.Ico T n, S (law d ν) s
          ≤ ∑ s ∈ Finset.range n, S (law d ν) s := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun s _ _ => S_nonneg _ s)
        intro s hs
        rw [Finset.mem_Ico] at hs
        exact Finset.mem_range.mpr hs.2
      have hlower : (1 / 16 : ℝ) * (Real.log n - Real.log T)
          ≤ ∑ s ∈ Finset.Ico T n, S (law d ν) s := by
        calc (1 / 16 : ℝ) * (Real.log n - Real.log T)
            ≤ (1 / 16 : ℝ) * ∑ s ∈ Finset.Ico T n, (1 : ℝ) / (s : ℝ) := by
              have := log_sub_log_le_sum_inv hT n hge
              linarith
          _ = ∑ s ∈ Finset.Ico T n, (1 / 16 : ℝ) * ((1 : ℝ) / (s : ℝ)) := by
              rw [Finset.mul_sum]
          _ ≤ ∑ s ∈ Finset.Ico T n, S (law d ν) s := Finset.sum_le_sum hterm
      rw [hexp n]
      linarith

end Parking

end
