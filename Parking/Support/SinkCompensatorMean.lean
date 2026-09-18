import Parking.Support.SinkMean

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The neighbor average of the Green escape barrier at the origin. -/
theorem walkOp_green_escape_barrier (hd : 3 ≤ d) (m : ℝ) :
    walkOp (fun y : Site d => m * (1 - srwGreenInf d y / srwGreenInf d 0)) 0 = m / escapeConst d := by
  have hg : 0 < srwGreenInf d 0 := zero_lt_one.trans_le (one_le_srwGreenInf_origin hd)
  have he : walkOp (fun y : Site d => m * (1 - srwGreenInf d y / srwGreenInf d 0)) 0 =
      m * walkOp (fun y : Site d => 1 - srwGreenInf d y / srwGreenInf d 0) 0 := by
    simpa only [mul_comm] using walkOp_mul_const (fun y : Site d => 1 - srwGreenInf d y / srwGreenInf d 0) m 0
  rw [he, walkOp_sub, walkOp_const (by omega : 1 ≤ d), walkOp_div_const, walkOp_srwGreenInf hd, if_pos rfl,
    escapeConst, fullGreen_eq_srwGreenInf]
  field_simp
  ring

/-- The expected compensator of entrances to the sink is comparable to the ordinary odometer mean. -/
theorem sparseSink_compensator_mean_bounds (hd : 3 ≤ d) {p : ℝ} (hp : 0 < p) (hp4 : p ≤ 1 / 4) (T : ℕ) :
    meanU (law d (threePointLaw p)) T / escapeConst d ≤ walkOp (sparseSinkMean (d := d) p T) 0 ∧
      walkOp (sparseSinkMean (d := d) p T) 0 ≤ meanU (law d (threePointLaw p)) T := by
  refine ⟨?_, walkOp_le_of_nbr (by omega) (fun y _ => sparseSinkMean_le (by omega) hp hp4 T y)⟩
  rw [← walkOp_green_escape_barrier hd]
  exact walkOp_mono (by omega) (fun y => sparseSinkMean_green_lower hd hp hp4 T y) 0
end Parking
