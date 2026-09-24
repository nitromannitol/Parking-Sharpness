import Parking.Support.SubharmonicMaximum
import Parking.Support.NearestGreen
import LatticeProb.Walk.ExteriorDirichlet

noncomputable section
namespace Parking
open LatticeProb
variable {d : ℕ}

/-- A superharmonic function that equals m outside a finite box and vanishes at the hole dominates the Green barrier. -/
theorem exterior_superharmonic_barrier (hd : 3 ≤ d) (f : Site d → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (hzero : f 0 = 0) (hsub : ∀ y : Site d, y ≠ 0 → walkOp f y ≤ f y)
    (R : ℕ) (hfar : ∀ y : Site d, y ∉ boxFinset 0 R → f y = m) :
    ∀ y : Site d, m * (1 - srwGreenInf d y / srwGreenInf d 0) ≤ f y := by
  classical
  have hd1 : 1 ≤ d := by omega
  haveI : NeZero d := ⟨by omega⟩
  have hg : 0 < srwGreenInf d 0 := zero_lt_one.trans_le (one_le_srwGreenInf_origin hd)
  let b : Site d → ℝ := fun y => m * (1 - srwGreenInf d y / srwGreenInf d 0)
  let h : Site d → ℝ := fun y => b y - f y
  have hb (y : Site d) (hy : y ≠ 0) : walkOp b y = b y := by
    dsimp only [b]
    have he : walkOp (fun y => m * (1 - srwGreenInf d y / srwGreenInf d 0)) y =
        m * walkOp (fun y => 1 - srwGreenInf d y / srwGreenInf d 0) y := by
      simpa only [mul_comm] using walkOp_mul_const (fun y => 1 - srwGreenInf d y / srwGreenInf d 0) m y
    rw [he, walkOp_sub, walkOp_const hd1, walkOp_div_const,
      walkOp_srwGreenInf_of_ne hd hy]
  have hlap (y : Site d) (hy : y ≠ 0) : 0 ≤ LatticeProb.Network.netLaplacian
      (lattice d) (LatticeProb.Network.unitCond (lattice d)) h y := by
    rw [netLaplacian_lattice hd1, show walkOp h y = walkOp b y - walkOp f y from walkOp_sub b f y, hb y hy]
    apply mul_nonneg (by positivity)
    dsimp only [h]
    linarith [hsub y hy]
  have hout (y : Site d) (hy : y ∉ boxFinset 0 R) : h y ≤ 0 := by
    dsimp only [h, b]
    rw [hfar y hy]
    have hq : 0 ≤ srwGreenInf d y / srwGreenInf d 0 := div_nonneg (srwGreenInf_nonneg y) hg.le
    nlinarith
  have h0 : h 0 = 0 := by
    dsimp only [h, b]
    rw [hzero, div_self hg.ne']
    ring
  let q : Site d := fun _ => (R : ℤ) + 1
  have hq : q ∉ boxFinset 0 R := by
    intro hq
    have h := mem_boxFinset_iff.mp hq ⟨0, hd1⟩
    simp only [q, Pi.zero_apply, sub_zero, abs_of_nonneg (by positivity : (0 : ℤ) ≤ R + 1)] at h
    omega
  have hle := le_of_subharmonicOn (LatticeProb.Graph.Zd.latticeConnected d)
    LatticeProb.Network.isCond_unitCond (boxFinset 0 R) {(0 : Site d)} h 0 hq
    (fun y _ hy => hlap y (by simpa using hy)) hout
    (fun y hy => by have he : y = 0 := hy; rw [he, h0])
  intro y
  exact sub_nonpos.mp (hle y)
end Parking
