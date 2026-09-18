/- The error field of the directed particle recursion and its maximal walk average. -/
import Parking.Support.OrientedMaximum
import Parking.Support.OrientedOdometer

noncomputable section
namespace Parking
open LatticeProb Finset MeasureTheory
variable {d : ℕ}

/-- The error field of the directed recursion: `w⃗_0 = 0` and
`w⃗_{k+1}(x) = (P⃗ w⃗_k)(x) + ∑_i (I_{x-e_i,x}(U⃗_k(x-e_i)) - U⃗_k(x-e_i)/d)`. -/
def wErrOriented (η : Site d → ℤ) (σ : Site d × ℕ → Site d) : ℕ → Site d → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun x => orientedOp (wErrOriented η σ k) x +
      ∑ i : Fin d, ((arrivals σ (x - unit i) x (orientedOdometer η σ k (x - unit i)) : ℝ)
        - (orientedOdometer η σ k (x - unit i) : ℝ) / d)

/-- `w⃗^⋆_n(x)`, the expected maximum of the error field along the directed walk. -/
def wStarOriented (η : Site d → ℤ) (σ : Site d × ℕ → Site d) (n : ℕ) (x : Site d) : ℝ :=
  orientedMaxMean (wErrOriented η σ) n x

theorem wErrOriented_zero (η : Site d → ℤ) (σ : Site d × ℕ → Site d) (x : Site d) :
    wErrOriented η σ 0 x = 0 := rfl

/-- The real value of the truncation `(·)⁺` that the particle recursion applies. -/
theorem cast_toNat_max (a : ℤ) : ((a.toNat : ℕ) : ℝ) = max 0 (a : ℝ) := by
  have h : ((a.toNat : ℤ) : ℝ) = ((max a 0 : ℤ) : ℝ) := by rw [Int.toNat_eq_max]
  push_cast at h
  rw [max_comm] at h
  exact_mod_cast h

/-- One round of the directed particle odometer, read over the reals. -/
theorem orientedOdometer_succ_real (η : Site d → ℤ) (σ : Site d × ℕ → Site d)
    (k : ℕ) (x : Site d) :
    ((orientedOdometer η σ (k + 1) x : ℕ) : ℝ) =
      max 0 ((η x : ℝ) +
        ∑ i : Fin d, ((arrivals σ (x - unit i) x (orientedOdometer η σ k (x - unit i)) : ℕ) : ℝ)) := by
  simp only [orientedOdometer, cast_toNat_max]
  push_cast
  ring

/-- The Bellman form of the corrected odometer: with `V_k = U⃗_k - w⃗_k`,
`V_{k+1}(x) = max(-w⃗_{k+1}(x), η(x) + (P⃗ V_k)(x))`. -/
theorem orientedOdometer_sub_wErr_succ (η : Site d → ℤ) (σ : Site d × ℕ → Site d)
    (k : ℕ) (x : Site d) :
    ((orientedOdometer η σ (k + 1) x : ℕ) : ℝ) - wErrOriented η σ (k + 1) x =
      max (-wErrOriented η σ (k + 1) x)
        ((η x : ℝ) + orientedOp
          (fun y => ((orientedOdometer η σ k y : ℕ) : ℝ) - wErrOriented η σ k y) x) := by
  rw [orientedOdometer_succ_real, ← max_sub_sub_right, zero_sub]
  congr 1
  simp only [wErrOriented, orientedOp, Finset.sum_sub_distrib, ← Finset.sum_div]
  ring

/-- The directed average does not increase the absolute value. -/
theorem abs_orientedOp_le (f : Site d → ℝ) (x : Site d) :
    |orientedOp f x| ≤ orientedOp (fun y => |f y|) x := by
  rw [orientedOp, orientedOp, abs_div, Nat.abs_cast]
  gcongr
  exact Finset.abs_sum_le_sum_abs _ _

/-- The directed pathwise comparison: the particle odometer corrected by the error field stays
within `w⃗^⋆` of the directed divisible odometer. -/
theorem abs_orientedOdometer_sub_wErr_sub_u_le (hd : 1 ≤ d) (η : Site d → ℤ)
    (σ : Site d × ℕ → Site d) (n : ℕ) (x : Site d) :
    |((orientedOdometer η σ n x : ℕ) : ℝ) - wErrOriented η σ n x
        - uOriented (fun y => (η y : ℝ)) n x| ≤ wStarOriented η σ n x := by
  simp only [wStarOriented]
  induction n generalizing x with
  | zero =>
      have h : |wErrOriented η σ 0 x| ≤ orientedMaxMean (wErrOriented η σ) 0 x :=
        abs_le_orientedMaxMean hd (wErrOriented η σ) 0 x
      simpa [orientedOdometer, wErrOriented, uOriented] using h
  | succ n ih =>
      have hV := orientedOdometer_sub_wErr_succ η σ n x
      have hu : uOriented (fun y => (η y : ℝ)) (n + 1) x
          = max 0 ((η x : ℝ) + orientedOp (uOriented (fun y => (η y : ℝ)) n) x) := rfl
      rw [hV, hu]
      refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
      · simpa using abs_le_orientedMaxMean hd (wErrOriented η σ) (n + 1) x
      · have hrw : ((η x : ℝ) + orientedOp
              (fun y => ((orientedOdometer η σ n y : ℕ) : ℝ) - wErrOriented η σ n y) x)
              - ((η x : ℝ) + orientedOp (uOriented (fun y => (η y : ℝ)) n) x)
            = orientedOp (fun y => ((orientedOdometer η σ n y : ℕ) : ℝ) - wErrOriented η σ n y
                  - uOriented (fun y => (η y : ℝ)) n y) x := by
          simp only [orientedOp, Finset.sum_sub_distrib]
          ring
        rw [hrw]
        exact ((abs_orientedOp_le _ x).trans (orientedOp_mono (fun y => ih y) x)).trans
          (orientedOp_orientedMaxMean_le hd (wErrOriented η σ) n x)

/-- The directed particle odometer is within `2 w⃗^⋆` of the directed divisible odometer. -/
theorem abs_orientedOdometer_sub_u_le (hd : 1 ≤ d) (η : Site d → ℤ)
    (σ : Site d × ℕ → Site d) (n : ℕ) (x : Site d) :
    |((orientedOdometer η σ n x : ℕ) : ℝ) - uOriented (fun y => (η y : ℝ)) n x|
      ≤ 2 * wStarOriented η σ n x := by
  have h1 := abs_orientedOdometer_sub_wErr_sub_u_le hd η σ n x
  have h2 : |wErrOriented η σ n x| ≤ wStarOriented η σ n x :=
    abs_le_orientedMaxMean hd (wErrOriented η σ) n x
  have h3 : |((orientedOdometer η σ n x : ℕ) : ℝ) - uOriented (fun y => (η y : ℝ)) n x|
      ≤ |((orientedOdometer η σ n x : ℕ) : ℝ) - wErrOriented η σ n x
          - uOriented (fun y => (η y : ℝ)) n x| + |wErrOriented η σ n x| := by
    have := abs_add_le (((orientedOdometer η σ n x : ℕ) : ℝ) - wErrOriented η σ n x
      - uOriented (fun y => (η y : ℝ)) n x) (wErrOriented η σ n x)
    calc |((orientedOdometer η σ n x : ℕ) : ℝ) - uOriented (fun y => (η y : ℝ)) n x|
        = |(((orientedOdometer η σ n x : ℕ) : ℝ) - wErrOriented η σ n x
            - uOriented (fun y => (η y : ℝ)) n x) + wErrOriented η σ n x| := by ring_nf
      _ ≤ _ := this
  linarith

end Parking
end
