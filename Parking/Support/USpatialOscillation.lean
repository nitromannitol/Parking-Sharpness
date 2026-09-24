/-
**The spatial oscillation of the divisible odometer reduces, pathwise, to the spatial
oscillation of the linear membrane field alone.**

`u_n(x) = V_n(x) + \sup_{\sigma\le n} E_x[-V_{n-\sigma}(X_\sigma)]` (BP's Lemma 2.5,
`Parking.u_eq_potential_add_stoppingSup`, `Parking/Support/Terminal.lean`).  Writing the
starting site into the reward via `Parking.stoppingSup_eq_shift`
(`Parking/Support/StoppingShift.lean`) and applying `Parking.abs_stoppingSup_sub_le`
(`Parking/Support/ValueLipschitz.lean`, the value's `1`-Lipschitz dependence on the reward for
the supremum norm) gives, for every fixed sample `η` and every two sites `x, y`,

    |u_n(x) - u_n(y)| \le |V_n(x) - V_n(y)| + \sup_{k \le n, z} |V_{n-k}(z+x) - V_{n-k}(z+y)|.

This gives a route to the equicontinuity clause of `prop:spatial-scaling`
(`Parking/Frozen/SpatialScaling.lean`) that avoids a direct one-coordinate induction on the
recursion `u_{n+1} = (\eta + Pu_n)^+`: such an induction bounds the response of `u` to ONE
perturbed coordinate and only certifies the SIGNED range `[0, \delta g_n(z-x)]`, not the sharp
translated-kernel difference, whichever pair `x, y` is read off at the end.  The bound here is
pathwise (no probability, no citation) and is PROVED directly from BP's Lemma 2.5 (already in
the repository, unconditionally) together with the value's own Lipschitz continuity in the
reward (also already in the repository, unconditionally).  It never compares `u` at two
perturbed sceneries; it compares `u` at two SITES for the SAME scenery, going through the
LINEAR field's exact translation structure instead of the nonlinear recursion's one-sided
coordinatewise sensitivity.

The right-hand side's supremum ranges over EVERY site `z` (not only `z` near `x, y`),
matching `Parking.External.OrientedStoppingStability`'s own docstring point ("the uniform
convergence is over all of `[0,T] × (Fin d → ℝ)`, because the application supplies the
reward through a spatial cutoff"): the walk can reach any site within its horizon, so the
reward comparison the value's Lipschitz bound consumes has to hold everywhere, not merely
locally.  Here this global control enters only through the hypotheses `hVb` and `hVdiff`;
obtaining it with high probability takes a cutoff together with a tail bound on how far the
walk can travel (`Parking/Support/WalkMaximal.lean`).
-/
import Parking.Support.StoppingShift
import Parking.Support.ValueLipschitz

noncomputable section

namespace Parking

variable {d : ℕ}

/-- **The value's Lipschitz bound, specialized to the reward `-V_{n-\cdot}` shifted by two
starting sites.**  One packaged application of `Parking.abs_stoppingSup_sub_le` after
`Parking.stoppingSup_eq_shift` moves the starting sites into the reward. -/
theorem abs_stoppingSup_potential_sub_le (hd : 1 ≤ d) (η : Site d → ℝ) (n : ℕ) (x y : Site d)
    {c M : ℝ} (hVb : ∀ k ≤ n, ∀ z : Site d, |linPotential η k z| ≤ M)
    (hVdiff : ∀ k ≤ n, ∀ z : Site d,
      |linPotential η k (x + z) - linPotential η k (y + z)| ≤ c) :
    |stoppingSup d (fun k z => -linPotential η (n - k) z) n x -
        stoppingSup d (fun k z => -linPotential η (n - k) z) n y| ≤ c := by
  have hc : 0 ≤ c := by
    have h := hVdiff 0 (Nat.zero_le n) (0 : Site d)
    rw [linPotential_zero, linPotential_zero, sub_self, abs_zero] at h
    exact h
  have hM : 0 ≤ M := by
    have h := hVb 0 (Nat.zero_le n) (0 : Site d)
    rw [linPotential_zero, abs_zero] at h
    exact h
  rw [stoppingSup_eq_shift (fun k z => -linPotential η (n - k) z) n x,
    stoppingSup_eq_shift (fun k z => -linPotential η (n - k) z) n y]
  apply abs_stoppingSup_sub_le hd (fun k z => -linPotential η (n - k) (x + z))
    (fun k z => -linPotential η (n - k) (y + z)) n (0 : Site d) (c := c) (M := M)
  · intro k z
    by_cases hk : k ≤ n
    · rw [abs_neg]; exact hVb (n - k) (Nat.sub_le n k) (x + z)
    · have hnk : n - k = 0 := by omega
      rw [hnk, linPotential_zero, abs_neg, abs_zero]; exact hM
  · intro k z
    by_cases hk : k ≤ n
    · rw [abs_neg]; exact hVb (n - k) (Nat.sub_le n k) (y + z)
    · have hnk : n - k = 0 := by omega
      rw [hnk, linPotential_zero, abs_neg, abs_zero]; exact hM
  · intro k z
    by_cases hk : k ≤ n
    · simp only [neg_sub_neg]
      rw [abs_sub_comm]
      exact hVdiff (n - k) (Nat.sub_le n k) z
    · have hnk : n - k = 0 := by omega
      simp [hnk, linPotential_zero, hc]

/-- **The spatial oscillation of `u` reduces to the spatial oscillation of the linear
membrane field `V` alone.**  Pathwise (fixed sample `η`), unconditional, no citation. -/
theorem abs_u_sub_le_of_linPotential_osc (hd : 1 ≤ d) (η : Site d → ℝ) (n : ℕ) (x y : Site d)
    {c M : ℝ} (hVb : ∀ k ≤ n, ∀ z : Site d, |linPotential η k z| ≤ M)
    (hVdiff : ∀ k ≤ n, ∀ z : Site d,
      |linPotential η k (x + z) - linPotential η k (y + z)| ≤ c) :
    |u η n x - u η n y| ≤ |linPotential η n x - linPotential η n y| + c := by
  rw [u_eq_potential_add_stoppingSup hd η n x, u_eq_potential_add_stoppingSup hd η n y]
  have hS := abs_stoppingSup_potential_sub_le hd η n x y hVb hVdiff
  set A := linPotential η n x - linPotential η n y with hA
  set B := stoppingSup d (fun k z => -linPotential η (n - k) z) n x -
      stoppingSup d (fun k z => -linPotential η (n - k) z) n y with hB
  have heq : (linPotential η n x + stoppingSup d (fun k z => -linPotential η (n - k) z) n x) -
      (linPotential η n y + stoppingSup d (fun k z => -linPotential η (n - k) z) n y) = A + B := by
    rw [hA, hB]; ring
  rw [heq]
  calc |A + B| ≤ |A| + |B| := abs_add_le A B
    _ ≤ |A| + c := by linarith

end Parking

end
