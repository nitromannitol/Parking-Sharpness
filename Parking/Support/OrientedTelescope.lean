/- The telescoping total of the directed instruction variance. -/
import Parking.Support.OrientedLayerBounds
import Parking.Support.OrientedVariance

noncomputable section
namespace Parking
open LatticeProb Finset Filter
variable {d : ℕ}

theorem tsum_orientedLayer_sq_tendsto_zero (hd : 2 ≤ d) :
    Tendsto (fun m : ℕ => ∑' x : Site d, orientedLayer d m x ^ 2) atTop (nhds 0) := by
  obtain ⟨c, C, hc, hC, hb⟩ := exists_orientedLayer_sq_bounds (d := d) (by omega)
  refine squeeze_zero' (Eventually.of_forall fun m => tsum_nonneg fun x => sq_nonneg _)
    (g := fun m : ℕ => C / Real.sqrt (m : ℝ)) ?_
    (tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs : 1 ≤ Real.sqrt (m : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hmR
  refine (hb m hm).2.trans ?_
  apply div_le_div_of_nonneg_left hC.le (Real.sqrt_pos.mpr (by linarith)) ?_
  exact le_self_pow₀ hs (by omega)

theorem hasSum_orientedLayer_sq_telescope (hd : 2 ≤ d) :
    HasSum (fun l : ℕ => ((∑' x : Site d, orientedLayer d l x ^ 2) -
      ∑' x : Site d, orientedLayer d (l + 1) x ^ 2)) 1 := by
  have hA := tsum_orientedLayer_sq_tendsto_zero (d := d) hd
  have h0 : (∑' x : Site d, orientedLayer d 0 x ^ 2) = 1 := by simp [orientedLayer]
  have hnonneg : ∀ l : ℕ, 0 ≤ (∑' x : Site d, orientedLayer d l x ^ 2) -
      ∑' x : Site d, orientedLayer d (l + 1) x ^ 2 := by
    intro l
    rw [← tsum_orientedCharge (by omega : 1 ≤ d) l]
    exact tsum_nonneg fun x => orientedCharge_nonneg l x
  refine (hasSum_iff_tendsto_nat_of_nonneg hnonneg 1).mpr ?_
  have htel : ∀ m : ℕ, (∑ l ∈ range m, ((∑' x : Site d, orientedLayer d l x ^ 2) -
      ∑' x : Site d, orientedLayer d (l + 1) x ^ 2)) =
      (∑' x : Site d, orientedLayer d 0 x ^ 2) - ∑' x : Site d, orientedLayer d m x ^ 2 :=
    fun m => Finset.sum_range_sub' (fun l => ∑' x : Site d, orientedLayer d l x ^ 2) m
  simp only [htel, h0]
  simpa using tendsto_const_nhds.sub hA

theorem tsum_orientedLayer_sq_telescope (hd : 2 ≤ d) :
    (∑' l : ℕ, ((∑' x : Site d, orientedLayer d l x ^ 2) -
      ∑' x : Site d, orientedLayer d (l + 1) x ^ 2)) = 1 :=
  (hasSum_orientedLayer_sq_telescope (d := d) hd).tsum_eq

theorem tsum_orientedCharge_eq_one (hd : 2 ≤ d) :
    (∑' l : ℕ, ∑' y : Site d, orientedCharge d l y) = 1 := by
  have hd1 : 1 ≤ d := by omega
  have htel := hasSum_orientedLayer_sq_telescope (d := d) hd
  rw [tsum_congr (fun l => tsum_orientedCharge hd1 l)]
  exact htel.tsum_eq

theorem summable_orientedCharge_site (hd : 1 ≤ d) (y : Site d) :
    Summable (fun l : ℕ => orientedCharge d l y) := by
  refine summable_of_sum_range_le (c := 1) (fun l => orientedCharge_nonneg l y) (fun m => ?_)
  calc ∑ l ∈ range m, orientedCharge d l y
      ≤ ∑ l ∈ range m, ∑' y' : Site d, orientedCharge d l y' :=
        sum_le_sum fun l _ => Summable.le_tsum (summable_orientedCharge hd l) y
          (fun y' _ => orientedCharge_nonneg l y')
    _ = ∑' y' : Site d, ∑ l ∈ range m, orientedCharge d l y' :=
        (Summable.tsum_finsetSum (fun l _ => summable_orientedCharge hd l)).symm
    _ = ∑' y' : Site d, orientedGamma d m y' :=
        tsum_congr fun y' => (orientedGamma_eq_sum m y').symm
    _ ≤ 1 := tsum_orientedGamma_le_one hd m

theorem orientedGammaSup_eq_tsum_charge (hd : 1 ≤ d) (y : Site d) :
    (⨆ m : ℕ, orientedGamma d m y) = ∑' l : ℕ, orientedCharge d l y := by
  have hbdd : BddAbove (Set.range fun m : ℕ => orientedGamma d m y) := by
    refine ⟨∑' l : ℕ, orientedCharge d l y, ?_⟩
    rintro _ ⟨m, rfl⟩
    change orientedGamma d m y ≤ ∑' l : ℕ, orientedCharge d l y
    rw [orientedGamma_eq_sum]
    exact Summable.sum_le_tsum (range m) (fun l _ => orientedCharge_nonneg l y)
      (summable_orientedCharge_site hd y)
  have h1 : Tendsto (fun m : ℕ => orientedGamma d m y) atTop
      (nhds (⨆ m : ℕ, orientedGamma d m y)) :=
    tendsto_atTop_ciSup (orientedGamma_mono y) hbdd
  have h2 : Tendsto (fun m : ℕ => orientedGamma d m y) atTop
      (nhds (∑' l : ℕ, orientedCharge d l y)) := by
    have hsum : HasSum (fun l : ℕ => orientedCharge d l y) (∑' l : ℕ, orientedCharge d l y) :=
      (summable_orientedCharge_site hd y).hasSum
    refine (hasSum_iff_tendsto_nat_of_nonneg (fun l => orientedCharge_nonneg l y) _).mp hsum |>.congr' ?_
    filter_upwards [] with m
    exact (orientedGamma_eq_sum m y).symm
  exact tendsto_nhds_unique h1 h2

theorem summable_orientedCharge_tsum (hd : 1 ≤ d) :
    Summable (fun l : ℕ => ∑' y : Site d, orientedCharge d l y) := by
  refine summable_of_sum_range_le (c := 1)
    (fun l => tsum_nonneg fun y => orientedCharge_nonneg l y) (fun m => ?_)
  calc ∑ l ∈ range m, ∑' y : Site d, orientedCharge d l y
      = ∑' y : Site d, ∑ l ∈ range m, orientedCharge d l y :=
        (Summable.tsum_finsetSum (fun l _ => summable_orientedCharge hd l)).symm
    _ = ∑' y : Site d, orientedGamma d m y :=
        tsum_congr fun y => (orientedGamma_eq_sum m y).symm
    _ ≤ 1 := tsum_orientedGamma_le_one hd m

theorem summable_orientedCharge_pair (hd : 1 ≤ d) :
    Summable (fun p : ℕ × Site d => orientedCharge d p.1 p.2) := by
  rw [summable_prod_of_nonneg (f := fun p : ℕ × Site d => orientedCharge d p.1 p.2)
    (fun p => orientedCharge_nonneg p.1 p.2)]
  exact ⟨fun l => summable_orientedCharge hd l, summable_orientedCharge_tsum hd⟩

theorem tsum_orientedGammaSup_eq_one (hd : 2 ≤ d) :
    (∑' y : Site d, ⨆ m : ℕ, orientedGamma d m y) = 1 := by
  rw [tsum_congr fun y => orientedGammaSup_eq_tsum_charge (by omega : 1 ≤ d) y]
  rw [Summable.tsum_comm (f := fun l y => orientedCharge d l y)
    (summable_orientedCharge_pair (by omega : 1 ≤ d))]
  exact tsum_orientedCharge_eq_one hd

/-- The supremum of the directed layer variance is nonnegative. -/
theorem orientedGammaSup_nonneg (hd : 1 ≤ d) (y : Site d) :
    0 ≤ ⨆ m : ℕ, orientedGamma d m y := by
  rw [orientedGammaSup_eq_tsum_charge hd y]
  exact tsum_nonneg fun l => orientedCharge_nonneg l y

/-- The total directed layer variance over the box of radius `n` is at most one: the
telescoping identity `∑_y sup_m Γ_m(y) = 1` of `parking.tex:3255-3262`. -/
theorem sum_orientedGammaSup_box_le_one (hd : 2 ≤ d) (n : ℕ) :
    ∑ y ∈ boxFinset (0 : Site d) n, (⨆ m : ℕ, orientedGamma d m y) ≤ 1 := by
  have hd1 : 1 ≤ d := by omega
  have hpair : Summable fun p : Site d × ℕ => orientedCharge d p.2 p.1 :=
    (summable_orientedCharge_pair hd1).prod_symm
  have hsum2 : Summable fun y : Site d => ∑' l : ℕ, orientedCharge d l y :=
    ((summable_prod_of_nonneg (f := fun p : Site d × ℕ => orientedCharge d p.2 p.1)
      (fun p => orientedCharge_nonneg p.2 p.1)).mp hpair).2
  have hs : Summable fun y : Site d => ⨆ m : ℕ, orientedGamma d m y :=
    Summable.congr hsum2 (fun y => (orientedGammaSup_eq_tsum_charge hd1 y).symm)
  calc ∑ y ∈ boxFinset (0 : Site d) n, (⨆ m : ℕ, orientedGamma d m y)
      ≤ ∑' y : Site d, (⨆ m : ℕ, orientedGamma d m y) :=
        hs.sum_le_tsum _ fun y _ => orientedGammaSup_nonneg hd1 y
    _ = 1 := tsum_orientedGammaSup_eq_one hd

end Parking
end
