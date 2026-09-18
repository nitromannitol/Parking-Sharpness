/-
The proof of `lem:mean-horizon` (`parking.tex:2772-2827`).

Step 1 is `Parking.exists_step1`: the fifth moment of the odometer of the
recentred scenery is at most `C φ_d(m)`, uniformly in `δ`, because the one-site
law of `ξ_δ(0)` is below a fixed law in convex order.

Step 2 is assembled here.  For each configuration the reward is split into the
dyadic blocks `[0,N)`, `[N,2N)`, `[2N,4N)`, … with `N = 1 ∨ ⌈M⌉`
(`Parking.integral_stopping_reward_le`); each block is bounded by Hölder's
inequality on the joint space of the configuration and the walk
(`Parking.integral_blockAvg_le`); the chance that the stopping time reaches the
`k`-th block is at most `M / s_k ≤ 2^{1-k}` by Markov's inequality
(`Parking.measureReal_blockEvent_le`); and the resulting series
`∑_j 2^{-4j/5} φ_d(2^j N)` converges to at most `C φ_d(N)`
(`Parking.exists_phi_block_sum`), which is the paper's "the last series converges
by the choice of `q`".  Finally `φ_d(N) ≤ 3 φ_d(M)`, because `N ≤ M + 2`.

The exponent is `q = 5` throughout: the paper asks for `1 - 1/q > (4-d)/4` when
`d ≤ 3`, and `1 - 1/5 = 4/5 > 3/4`.
-/
import Parking.Support.JointBlocks
import Parking.Support.MeanHorizonStep1
import Parking.Support.PhiSum

noncomputable section

namespace Parking

open MeasureTheory LatticeProb

variable {d : ℕ}

theorem blockLen_succ (N : ℕ) (hN : 1 ≤ N) (j : ℕ) :
    blockBound N (j + 2) - blockBound N (j + 1) = 2 ^ j * N := by
  rw [blockBound_succ_eq N hN (j + 1), blockBound_succ_eq N hN j]
  have h : 2 ^ (j + 1) * N = 2 * (2 ^ j * N) := by ring
  omega

theorem blockLen_zero (N : ℕ) : blockBound N (0 + 1) - blockBound N 0 = N := by
  show blockBound N 1 - blockBound N 0 = N
  rw [show blockBound N 1 = max N (2 * blockBound N 0) from rfl,
    show blockBound N 0 = 0 from rfl]
  omega

theorem ceil_bounds {Mσ : ℝ} (hM : 0 ≤ Mσ) :
    Mσ ≤ ((max 1 ⌈Mσ⌉₊ : ℕ) : ℝ) ∧ ((max 1 ⌈Mσ⌉₊ : ℕ) : ℝ) ≤ Mσ + 2 := by
  constructor
  · refine le_trans (Nat.le_ceil Mσ) ?_
    exact_mod_cast Nat.cast_le.mpr (le_max_right 1 ⌈Mσ⌉₊)
  · have h1 : (⌈Mσ⌉₊ : ℝ) < Mσ + 1 := Nat.ceil_lt_add_one hM
    have h2 : ((max 1 ⌈Mσ⌉₊ : ℕ) : ℝ) = max 1 ((⌈Mσ⌉₊ : ℕ) : ℝ) := by
      rw [Nat.cast_max, Nat.cast_one]
    rw [h2]
    refine max_le (by linarith) (by linarith)

/-- **`lem:mean-horizon`** (`parking.tex:2764-2770`), assembled.

Step 1 (`Parking.exists_step1`) bounds the fifth moment of the odometer of the recentred
scenery by `C φ_d(m)`, uniformly in `δ`.  Step 2 splits the reward into the dyadic blocks
(`Parking.integral_stopping_reward_le`), bounds each block by Hölder's inequality
(`Parking.integral_blockAvg_le`), bounds the chance that the stopping time reaches the
`k`-th block by `M/s_k ≤ 2^{1-k}` (`Parking.measureReal_blockEvent_le`), and sums the
resulting series (`Parking.exists_phi_block_sum`), whose convergence is the choice
`q = 5`. -/
theorem exists_meanHorizon (hd : 1 ≤ d) (hGrowth : Parking.External.SandpileGrowth)
    (hStopping : Parking.External.Stopping) (hConc : Parking.External.UConcentration)
    (hGreen : Parking.External.GreenNorms)
    {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ} (hfam : NearFamily δ₀ ν θ M K) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Icc (0:ℝ) δ₀, ∀ n : ℕ,
      ∀ σ : (Site d → ℤ) → (ℕ → Site d) → ℕ,
        (∀ η, LatticeProb.IsWalkStopping (σ η)) → (∀ η X, σ η X ≤ n) →
        (∀ X, Measurable fun η => σ η X) →
        ∀ Mσ : ℝ, Mσ = ∫ η, ∫ X, ((σ η X : ℕ) : ℝ)
              ∂(LatticeProb.siteWalkLaw d (0 : Site d)) ∂(LatticeProb.iidLaw d (ν δ)) →
          Integrable (rewardAvg δ σ) (LatticeProb.iidLaw d (ν δ)) ∧
            ∫ η, rewardAvg δ σ η ∂(LatticeProb.iidLaw d (ν δ)) ≤ C * phi d Mσ := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨hδ₀, hθ, hprob, hmeanν, -, hexpfam, -⟩ := id hfam
  obtain ⟨C1, hC1, hstep1⟩ := exists_step1 (d := d) hd hGrowth hConc hGreen hfam
  obtain ⟨C2, hC2, hseries⟩ := exists_phi_block_sum d (θ := (4:ℝ)/5) (by norm_num)
    (fun hd3 => by
      have : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      linarith)
  refine ⟨3 * C1 * (1 + C2), by positivity, fun δ hδ n σ hσ hσn hm Mσ hMdef => ?_⟩
  haveI hpν : IsProbabilityMeasure (ν δ) := hprob δ hδ
  have hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) (ν δ) := (hexpfam δ hδ).1
  set P := LatticeProb.iidLaw d (ν δ) with hP
  haveI : IsProbabilityMeasure P := by rw [hP, LatticeProb.iidLaw]; infer_instance
  have hIreward : Integrable (rewardAvg δ σ) P :=
    integrable_rewardAvg hd hθ (ν δ) hexp hσ hσn hm
  refine ⟨hIreward, ?_⟩
  -- the mean of the stopping time is nonnegative
  have hM0 : 0 ≤ Mσ := by
    rw [hMdef]
    exact integral_nonneg fun η => integral_nonneg fun X => Nat.cast_nonneg _
  set N : ℕ := max 1 ⌈Mσ⌉₊ with hNdef
  have hN1 : 1 ≤ N := le_max_left 1 _
  obtain ⟨hNM, hNM2⟩ := ceil_bounds hM0
  rw [← hNdef] at hNM hNM2
  have hNpos : (0:ℝ) < (N:ℝ) := by
    have : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
    linarith
  -- Step 2: the block decomposition, integrated over the configuration
  have hblocks : ∀ η, rewardAvg δ σ η ≤ ∑ k ∈ Finset.range (n + 1), blockAvg δ σ N k η := by
    intro η
    exact integral_stopping_reward_le hd hStopping (Parking.xi δ η) (hσ η) (hσn η) hN1
  have hIsum : Integrable (fun η => ∑ k ∈ Finset.range (n + 1), blockAvg δ σ N k η) P :=
    integrable_finsetSum _ fun k _ => integrable_blockAvg hd hθ (ν δ) hexp hσ hσn hm N k
  have hchain1 : ∫ η, rewardAvg δ σ η ∂P
      ≤ ∑ k ∈ Finset.range (n + 1), ∫ η, blockAvg δ σ N k η ∂P := by
    rw [← integral_finsetSum _ (fun k _ => integrable_blockAvg hd hθ (ν δ) hexp hσ hσn hm N k)]
    exact integral_mono hIreward hIsum hblocks
  refine hchain1.trans ?_
  -- the scale is nonnegative and does not see the shift from `Mσ` to `N`
  have hphinn : ∀ s : ℝ, 0 ≤ s → 0 ≤ phi d s := by
    intro s hs
    simp only [phi]
    split_ifs with h
    · exact Real.rpow_nonneg (by linarith) _
    · exact Real.log_nonneg (by linarith)
  have hphiMnn : 0 ≤ phi d Mσ := hphinn Mσ hM0
  have hphiN3 : phi d ((N:ℕ):ℝ) ≤ 3 * phi d Mσ :=
    le_trans (phi_mono d (by positivity : (0:ℝ) ≤ ((N:ℕ):ℝ)) hNM2) (phi_add_two_le d hM0)
  have hphiNnn : 0 ≤ phi d ((N:ℕ):ℝ) := hphinn _ (by positivity)
  -- each block, by Hölder and Step 1
  have hterm : ∀ k : ℕ, ∫ η, blockAvg δ σ N k η ∂P
      ≤ ((jointLaw d (ν δ)).real (blockEvent σ (blockBound N k))) ^ ((4:ℝ)/5)
        * (C1 * phi d (((blockBound N (k + 1) - blockBound N k : ℕ) : ℝ))) := by
    intro k
    refine (integral_blockAvg_le hd hθ (ν δ) hexp hσ hσn hm N k).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg measureReal_nonneg _)
    exact hstep1 δ hδ _
  -- the zeroth block
  have hzero : ∫ η, blockAvg δ σ N 0 η ∂P ≤ C1 * phi d ((N:ℕ):ℝ) := by
    refine (hterm 0).trans ?_
    rw [blockLen_zero N]
    have h1 : ((jointLaw d (ν δ)).real (blockEvent σ (blockBound N 0))) ^ ((4:ℝ)/5) ≤ 1 :=
      Real.rpow_le_one measureReal_nonneg
        (measureReal_blockEvent_le_one hd (ν δ) σ _) (by norm_num)
    have h2 : (0:ℝ) ≤ C1 * phi d ((N:ℕ):ℝ) := by positivity
    calc ((jointLaw d (ν δ)).real (blockEvent σ (blockBound N 0))) ^ ((4:ℝ)/5)
          * (C1 * phi d ((N:ℕ):ℝ))
        ≤ 1 * (C1 * phi d ((N:ℕ):ℝ)) := mul_le_mul_of_nonneg_right h1 h2
      _ = C1 * phi d ((N:ℕ):ℝ) := one_mul _
  -- the later blocks
  have hsucc : ∀ j : ℕ, ∫ η, blockAvg δ σ N (j + 1) η ∂P
      ≤ C1 * ((2:ℝ) ^ (-(j:ℝ) * ((4:ℝ)/5)) * phi d (2 ^ j * ((N:ℕ):ℝ))) := by
    intro j
    have hb : blockBound N (j + 1) = 2 ^ j * N := blockBound_succ_eq N hN1 j
    have hbpos : 0 < blockBound N (j + 1) := by
      rw [hb]; exact Nat.mul_pos (Nat.two_pow_pos j) hN1
    have hbR : ((blockBound N (j + 1) : ℕ) : ℝ) = 2 ^ j * ((N:ℕ):ℝ) := by
      rw [hb]; push_cast; ring
    have hmk := measureReal_blockEvent_le hd (ν δ) hσ hσn hm (s := blockBound N (j + 1)) hbpos
    rw [← hMdef, hbR] at hmk
    have h2j : (0:ℝ) < (2:ℝ) ^ j := by positivity
    have hle : (jointLaw d (ν δ)).real (blockEvent σ (blockBound N (j + 1)))
        ≤ (2:ℝ) ^ (-(j:ℝ)) := by
      refine hmk.trans ?_
      rw [div_le_iff₀ (by positivity), Real.rpow_neg (by norm_num), Real.rpow_natCast]
      rw [inv_mul_eq_div, le_div_iff₀ h2j]
      nlinarith [hNM, hNpos, h2j]
    have hrpow : ((jointLaw d (ν δ)).real (blockEvent σ (blockBound N (j + 1)))) ^ ((4:ℝ)/5)
        ≤ (2:ℝ) ^ (-(j:ℝ) * ((4:ℝ)/5)) := by
      refine le_trans (Real.rpow_le_rpow measureReal_nonneg hle (by norm_num)) ?_
      rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    refine (hterm (j + 1)).trans ?_
    rw [blockLen_succ N hN1 j]
    have hcast : (((2 ^ j * N : ℕ)) : ℝ) = 2 ^ j * ((N:ℕ):ℝ) := by push_cast; ring
    rw [hcast]
    have hphij : 0 ≤ phi d (2 ^ j * ((N:ℕ):ℝ)) := hphinn _ (by positivity)
    have h2 : (0:ℝ) ≤ C1 * phi d (2 ^ j * ((N:ℕ):ℝ)) := by positivity
    calc ((jointLaw d (ν δ)).real (blockEvent σ (blockBound N (j + 1)))) ^ ((4:ℝ)/5)
          * (C1 * phi d (2 ^ j * ((N:ℕ):ℝ)))
        ≤ (2:ℝ) ^ (-(j:ℝ) * ((4:ℝ)/5)) * (C1 * phi d (2 ^ j * ((N:ℕ):ℝ))) :=
          mul_le_mul_of_nonneg_right hrpow h2
      _ = C1 * ((2:ℝ) ^ (-(j:ℝ) * ((4:ℝ)/5)) * phi d (2 ^ j * ((N:ℕ):ℝ))) := by ring
  -- the series
  have hN1R : (1:ℝ) ≤ ((N:ℕ):ℝ) := by exact_mod_cast hN1
  obtain ⟨hsummable, htsum⟩ := hseries ((N:ℕ):ℝ) hN1R
  have hfin : ∑ j ∈ Finset.range n,
      ((2:ℝ) ^ (-(j:ℝ) * ((4:ℝ)/5)) * phi d (2 ^ j * ((N:ℕ):ℝ)))
      ≤ C2 * phi d ((N:ℕ):ℝ) := by
    refine le_trans (Summable.sum_le_tsum _ (fun j _ => ?_) hsummable) htsum
    have : 0 ≤ phi d (2 ^ j * ((N:ℕ):ℝ)) := hphinn _ (by positivity)
    positivity
  rw [Finset.sum_range_succ']
  have hsum2 : ∑ j ∈ Finset.range n, ∫ η, blockAvg δ σ N (j + 1) η ∂P
      ≤ ∑ j ∈ Finset.range n,
        C1 * ((2:ℝ) ^ (-(j:ℝ) * ((4:ℝ)/5)) * phi d (2 ^ j * ((N:ℕ):ℝ))) :=
    Finset.sum_le_sum fun j _ => hsucc j
  rw [← Finset.mul_sum] at hsum2
  have hA : ∑ j ∈ Finset.range n, ∫ η, blockAvg δ σ N (j + 1) η ∂P
      ≤ C1 * (C2 * phi d ((N:ℕ):ℝ)) :=
    hsum2.trans (mul_le_mul_of_nonneg_left hfin hC1.le)
  have hD : C1 * (1 + C2) * phi d ((N:ℕ):ℝ) ≤ 3 * C1 * (1 + C2) * phi d Mσ := by
    have h1 : (0:ℝ) ≤ C1 * (1 + C2) := by positivity
    nlinarith [hphiN3, h1]
  nlinarith [hA, hzero, hD]

end Parking

end
