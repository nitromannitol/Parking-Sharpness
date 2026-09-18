/-
The McShane lift of a bounded Lipschitz test functional off `C(rewardBox T A, ℝ)` to a
globally-defined, bounded, `capDist`-Lipschitz functional on raw functions
`rewardBox T A → ℝ`, built as an infimal convolution against the unit-capped distance
`Parking.capDist` of `Parking.Support.TightHlawLift`.

For `Φ0 : C(rewardBox T A, ℝ) → ℝ` bounded by `M0` and `L0'`-Lipschitz for the sup metric,
`Parking.liftPhi Φ0 L0 v := sInf {y | ∃ G, y = Φ0 G + L0 * capDist v G}` at `L0 := L0' + 2 * M0`
is `L0`-Lipschitz for `capDist` (`Parking.abs_liftPhi_sub_le`), bounded by `M0 + L0`
(`Parking.abs_liftPhi_le`), and recovers `Φ0` exactly on genuine continuous functions
(`Parking.liftPhi_coe_eq`): the `L0` = `L0' + 2 * M0` bookkeeping is exactly what the far
regime `dist H G > 1` needs, where boundedness alone (not the Lipschitz bound) controls the
gap once the unit cap saturates.
-/
import Parking.Support.TightHlawLift

open MeasureTheory LatticeProb Filter Topology

noncomputable section

namespace Parking

variable {T A : ℝ} [Nonempty (rewardBox T A)]

/-! ### The lift as an infimal convolution -/

/-- The defining set of the McShane lift at `v`. -/
def liftPhiSet (Φ0 : C(rewardBox T A, ℝ) → ℝ) (L0 : ℝ) (v : rewardBox T A → ℝ) : Set ℝ :=
  {y : ℝ | ∃ G : C(rewardBox T A, ℝ), y = Φ0 G + L0 * capDist v (⇑G)}

theorem liftPhiSet_nonempty (Φ0 : C(rewardBox T A, ℝ) → ℝ) (L0 : ℝ) (v : rewardBox T A → ℝ) :
    (liftPhiSet Φ0 L0 v).Nonempty :=
  ⟨Φ0 0 + L0 * capDist v (⇑(0 : C(rewardBox T A, ℝ))), 0, rfl⟩

theorem bddBelow_liftPhiSet {Φ0 : C(rewardBox T A, ℝ) → ℝ} {M0 : ℝ} (hΦ0 : ∀ G, |Φ0 G| ≤ M0)
    {L0 : ℝ} (hL0 : 0 ≤ L0) (v : rewardBox T A → ℝ) : BddBelow (liftPhiSet Φ0 L0 v) := by
  refine ⟨-M0, ?_⟩
  rintro y ⟨G, rfl⟩
  have h1 : -M0 ≤ Φ0 G := neg_le_of_abs_le (hΦ0 G)
  have h2 : 0 ≤ L0 * capDist v (⇑G) := mul_nonneg hL0 (capDist_nonneg _ _)
  linarith

/-- **The McShane lift**: the infimal convolution of `Φ0` against `L0` times the unit-capped
distance. -/
noncomputable def liftPhi (Φ0 : C(rewardBox T A, ℝ) → ℝ) (L0 : ℝ) (v : rewardBox T A → ℝ) : ℝ :=
  sInf (liftPhiSet Φ0 L0 v)

theorem liftPhi_le {Φ0 : C(rewardBox T A, ℝ) → ℝ} {M0 L0 : ℝ} (hΦ0 : ∀ G, |Φ0 G| ≤ M0)
    (hL0 : 0 ≤ L0) (v : rewardBox T A → ℝ) (G : C(rewardBox T A, ℝ)) :
    liftPhi Φ0 L0 v ≤ Φ0 G + L0 * capDist v (⇑G) :=
  csInf_le (bddBelow_liftPhiSet hΦ0 hL0 v) ⟨G, rfl⟩

theorem exists_liftPhi_near (Φ0 : C(rewardBox T A, ℝ) → ℝ) (L0 : ℝ) (v : rewardBox T A → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : C(rewardBox T A, ℝ), Φ0 G + L0 * capDist v (⇑G) < liftPhi Φ0 L0 v + ε := by
  obtain ⟨y, hy, hylt⟩ := exists_lt_of_csInf_lt (liftPhiSet_nonempty Φ0 L0 v)
    (lt_add_of_pos_right (liftPhi Φ0 L0 v) hε)
  obtain ⟨G, rfl⟩ := hy
  exact ⟨G, hylt⟩

/-! ### The lift is `L0`-Lipschitz for `capDist` -/

theorem liftPhi_le_add {Φ0 : C(rewardBox T A, ℝ) → ℝ} {M0 L0 : ℝ} (hΦ0 : ∀ G, |Φ0 G| ≤ M0)
    (hL0 : 0 ≤ L0) (v w : rewardBox T A → ℝ) :
    liftPhi Φ0 L0 v ≤ liftPhi Φ0 L0 w + L0 * capDist v w := by
  refine le_of_forall_sub_le fun ε hε => ?_
  obtain ⟨G, hG⟩ := exists_liftPhi_near Φ0 L0 w hε
  have h1 : liftPhi Φ0 L0 v ≤ Φ0 G + L0 * capDist v (⇑G) := liftPhi_le hΦ0 hL0 v G
  have h2 : capDist v (⇑G) ≤ capDist v w + capDist w (⇑G) := capDist_le_add v (⇑G) w
  have h3 : Φ0 G + L0 * capDist v (⇑G) ≤
      (Φ0 G + L0 * capDist w (⇑G)) + L0 * capDist v w := by nlinarith
  linarith

/-- **The lift is `L0`-Lipschitz for `Parking.capDist`.** -/
theorem abs_liftPhi_sub_le {Φ0 : C(rewardBox T A, ℝ) → ℝ} {M0 L0 : ℝ} (hΦ0 : ∀ G, |Φ0 G| ≤ M0)
    (hL0 : 0 ≤ L0) (v w : rewardBox T A → ℝ) :
    |liftPhi Φ0 L0 v - liftPhi Φ0 L0 w| ≤ L0 * capDist v w := by
  rw [abs_sub_le_iff]
  refine ⟨by linarith [liftPhi_le_add hΦ0 hL0 v w], ?_⟩
  have h := liftPhi_le_add hΦ0 hL0 w v
  rw [capDist_comm w v] at h
  linarith

/-! ### The lift is bounded -/

/-- **The lift is bounded by `M0 + L0`.** -/
theorem abs_liftPhi_le {Φ0 : C(rewardBox T A, ℝ) → ℝ} {M0 L0 : ℝ} (hΦ0 : ∀ G, |Φ0 G| ≤ M0)
    (hL0 : 0 ≤ L0) (v : rewardBox T A → ℝ) :
    |liftPhi Φ0 L0 v| ≤ M0 + L0 := by
  have hupper : liftPhi Φ0 L0 v ≤ Φ0 0 + L0 * capDist v (⇑(0 : C(rewardBox T A, ℝ))) :=
    liftPhi_le hΦ0 hL0 v 0
  have hb1 : Φ0 0 + L0 * capDist v (⇑(0 : C(rewardBox T A, ℝ))) ≤ M0 + L0 := by
    have h0 := abs_le.mp (hΦ0 0)
    have hc := capDist_le_one v (⇑(0 : C(rewardBox T A, ℝ)))
    nlinarith
  have hlower : -M0 ≤ liftPhi Φ0 L0 v :=
    le_csInf (liftPhiSet_nonempty Φ0 L0 v) (by
      rintro y ⟨G, rfl⟩
      have h1 : -M0 ≤ Φ0 G := neg_le_of_abs_le (hΦ0 G)
      have h2 : 0 ≤ L0 * capDist v (⇑G) := mul_nonneg hL0 (capDist_nonneg _ _)
      linarith)
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-! ### `capDist` between two continuous maps is the unit-capped sup distance -/

/-- **`Parking.capDist` between two continuous maps is the unit-capped sup distance.** -/
theorem capDist_coe_eq_min_dist [CompactSpace (rewardBox T A)] (H G : C(rewardBox T A, ℝ)) :
    capDist (⇑H) (⇑G) = min 1 (dist H G) := by
  have hbdd : BddAbove (Set.range fun p : rewardBox T A => dist (H p) (G p)) :=
    ⟨dist H G, by rintro _ ⟨p, rfl⟩; exact ContinuousMap.dist_apply_le_dist p⟩
  have hmono : Monotone (fun x : ℝ => min 1 x) := fun a b hab => min_le_min le_rfl hab
  have hcont : ContinuousAt (fun x : ℝ => min 1 x) (⨆ p, dist (H p) (G p)) :=
    (continuous_const.min continuous_id).continuousAt
  have hmap := hmono.map_ciSup_of_continuousAt hcont hbdd
  have hdist : dist H G = ⨆ p, dist (H p) (G p) := ContinuousMap.dist_eq_iSup
  have hunfold : capDist (⇑H) (⇑G) = ⨆ p : rewardBox T A, min 1 |H p - G p| := rfl
  rw [hunfold]
  simp_rw [← Real.dist_eq]
  rw [hdist, hmap]

/-! ### The lift recovers `Φ0` exactly on genuine continuous functions -/

/-- **The lift recovers `Φ0` exactly on continuous functions**, at `L0 := L0' + 2 * M0` for a
`Φ0` bounded by `M0` and `L0'`-Lipschitz: the far regime `dist H G > 1`, where the unit cap
saturates, needs boundedness alone, and that is exactly what the `2 * M0` term supplies. -/
theorem liftPhi_coe_eq {Φ0 : C(rewardBox T A, ℝ) → ℝ} {M0 L0' : ℝ} (hΦ0 : ∀ G, |Φ0 G| ≤ M0)
    (hΦ0lip : ∀ G G' : C(rewardBox T A, ℝ), |Φ0 G - Φ0 G'| ≤ L0' * dist G G')
    (hL0' : 0 ≤ L0') [CompactSpace (rewardBox T A)] (H : C(rewardBox T A, ℝ)) :
    liftPhi Φ0 (L0' + 2 * M0) (⇑H) = Φ0 H := by
  set L0 := L0' + 2 * M0 with hL0def
  have hM0nn : 0 ≤ M0 := le_trans (abs_nonneg _) (hΦ0 0)
  have hL0 : 0 ≤ L0 := by rw [hL0def]; linarith
  refine le_antisymm ?_ ?_
  · have hself : capDist (⇑H) (⇑H) = 0 := by
      rw [capDist_coe_eq_min_dist]; simp
    have hle := liftPhi_le hΦ0 hL0 (⇑H) H
    rw [hself, mul_zero, add_zero] at hle
    exact hle
  · refine le_csInf (liftPhiSet_nonempty Φ0 L0 (⇑H)) ?_
    rintro y ⟨G, rfl⟩
    rw [capDist_coe_eq_min_dist]
    rcases le_total (dist H G) 1 with hd | hd
    · rw [min_eq_right hd]
      have hlip := abs_le.mp (hΦ0lip H G)
      have hdnn : 0 ≤ dist H G := dist_nonneg
      have hLL : L0' * dist H G ≤ L0 * dist H G :=
        mul_le_mul_of_nonneg_right (by linarith) hdnn
      linarith [hlip.2]
    · rw [min_eq_left hd]
      have h1 := abs_le.mp (hΦ0 H)
      have h2 := abs_le.mp (hΦ0 G)
      linarith [h1.2, h2.1]

end Parking

end
