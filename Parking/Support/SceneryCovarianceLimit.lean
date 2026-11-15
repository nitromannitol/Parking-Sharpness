import Parking.Support.SceneryCovariance
import Parking.External.LinearFieldScaling
import Sandpile.Support.LimOccupationIdentity

/-!
# Limits of scenery covariances

The finite-time Brownian Green kernel represents integrated transition averages.
-/

open MeasureTheory ProbabilityTheory Filter Topology LatticeProb
open scoped NNReal

noncomputable section
namespace Parking

/-- The finite-time Green kernels agree under the Euclidean coordinate equivalence. -/
theorem scenery_contFiniteGreen_eq_greenTimeBM (d : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (x y : Fin d → ℝ) :
    External.contFiniteGreen d t x y =
      Sandpile.Continuum.greenTimeBM d t (WithLp.toLp 2 x) (WithLp.toLp 2 y) := by
  have hnorm : ‖(WithLp.toLp 2 x : Sandpile.Continuum.Space d) - WithLp.toLp 2 y‖ ^ 2 =
      ∑ i, (x i - y i) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  unfold External.contFiniteGreen Sandpile.Continuum.greenTimeBM
  rw [intervalIntegral.integral_of_le ht]
  congr 1
  funext s
  simp only [External.contHeatKernel, Sandpile.Continuum.heatKernelBM, hnorm]

/-- A coordinate Green-kernel pairing is the time integral of Brownian averages. -/
theorem integral_mul_contFiniteGreen_eq_integral_brownian {d : ℕ} (hd : 1 ≤ d)
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hB : IsBrownianSpace d 0 B P)
    {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) {t : ℝ} (ht : 0 ≤ t)
    (x : Fin d → ℝ) :
    (∫ y, φ y * External.contFiniteGreen d t x y) =
      ∫ s in Set.Ioo (0 : ℝ) t, ∫ ω, φ (x + ofBrownianSpace B s.toNNReal ω) ∂P := by
  let f : Sandpile.Continuum.Space d → ℝ := fun y => φ (WithLp.ofLp y)
  obtain ⟨M, _, hM⟩ := LatticeProb.Walk.exists_norm_le_of_hasCompactSupport
    hφ.1.continuous hφ.2
  have hf : Measurable f := hφ.1.continuous.measurable.comp (PiLp.continuous_ofLp 2 _).measurable
  have hbound : ∀ y, |f y| ≤ M := fun y => by simpa [f, Real.norm_eq_abs] using hM (WithLp.ofLp y)
  have hBrown : Sandpile.Continuum.IsBrownian d 0 B P := ⟨hB.start, hB.coord, hB.indep⟩
  calc
    _ = ∫ y : Sandpile.Continuum.Space d,
        f y * Sandpile.Continuum.greenTimeBM d t (WithLp.toLp 2 x) y := by
      rw [← (PiLp.volume_preserving_toLp (Fin d)).integral_comp
        (MeasurableEquiv.toLp 2 _).measurableEmbedding]
      congr 1
      funext y
      simp [f, scenery_contFiniteGreen_eq_greenTimeBM d t ht]
    _ = ∫ s in Set.Ioo (0 : ℝ) t,
        Sandpile.Support.transAvg d f s (WithLp.toLp 2 x) :=
      Sandpile.Support.integral_mul_greenTimeBM hd ht _ f hf hbound
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro s hs
      dsimp only
      rw [Sandpile.Support.transAvg_eq_integral hd hBrown hs.1 _ f hf hbound]
      apply integral_congr_ae
      filter_upwards [hB.start] with ω hω
      simp [f, ofBrownianSpace, hω]
      congr 1

/-- The natural parabolic mesh changes a fixed-time walk index by a bounded amount. -/
theorem floor_sq_time_sub_floor_mesh_le (R a : ℝ) (ha : 0 ≤ a) :
    0 ≤ (⌊R ^ 2 * a⌋₊ : ℝ) - (⌊(⌊R ^ 2⌋₊ : ℝ) * a⌋₊ : ℝ) ∧
      (⌊R ^ 2 * a⌋₊ : ℝ) - (⌊(⌊R ^ 2⌋₊ : ℝ) * a⌋₊ : ℝ) ≤ a + 1 := by
  have hn : (⌊R ^ 2⌋₊ : ℝ) ≤ R ^ 2 := Nat.floor_le (sq_nonneg R)
  have hn' : R ^ 2 < (⌊R ^ 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hprod : (⌊R ^ 2⌋₊ : ℝ) * a ≤ R ^ 2 * a :=
    mul_le_mul_of_nonneg_right hn ha
  have hprod' : R ^ 2 * a ≤ ((⌊R ^ 2⌋₊ : ℝ) + 1) * a :=
    mul_le_mul_of_nonneg_right hn'.le ha
  have hfloor : (⌊R ^ 2 * a⌋₊ : ℝ) ≤ R ^ 2 * a :=
    Nat.floor_le (mul_nonneg (sq_nonneg R) ha)
  have hfloor' : (⌊R ^ 2⌋₊ : ℝ) * a <
      (⌊(⌊R ^ 2⌋₊ : ℝ) * a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmono : ⌊(⌊R ^ 2⌋₊ : ℝ) * a⌋₊ ≤ ⌊R ^ 2 * a⌋₊ := Nat.floor_mono hprod
  constructor
  · exact sub_nonneg.mpr (by exact_mod_cast hmono)
  · nlinarith

/-- A coordinate of a walk changes by at most the number of elapsed steps. -/
theorem abs_walkPath_add_sub_le {d : ℕ} (x : Site d) (p : ℕ → Fin d × Bool)
    (m k : ℕ) (i : Fin d) :
    |walkPath x p (m + k) i - walkPath x p m i| ≤ (k : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := abs_stepVec_le_one (p (m + k)) i
      have heq : walkPath x p (m + (k + 1)) i - walkPath x p m i =
          (walkPath x p (m + k) i - walkPath x p m i) + stepVec (p (m + k)) i := by
        change (walkPath x p (m + k) i + stepVec (p (m + k)) i) -
          walkPath x p m i = _
        ring
      rw [heq]
      calc
        _ ≤ |walkPath x p (m + k) i - walkPath x p m i| +
            |stepVec (p (m + k)) i| := abs_add_le _ _
        _ ≤ (k : ℤ) + 1 := add_le_add ih hstep
        _ = ((k + 1 : ℕ) : ℤ) := by push_cast; rfl

/-- The two fixed-time parabolic meshes sample walk positions a bounded distance apart. -/
theorem abs_walkPath_floor_sq_sub_floor_mesh_le {d : ℕ}
    (p : ℕ → Fin d × Bool) (R a : ℝ) (ha : 0 ≤ a) (i : Fin d) :
    |(walkPath (0 : Site d) p ⌊R ^ 2 * a⌋₊ i : ℝ) -
      (walkPath (0 : Site d) p ⌊(⌊R ^ 2⌋₊ : ℝ) * a⌋₊ i : ℝ)| ≤ a + 1 := by
  let m := ⌊(⌊R ^ 2⌋₊ : ℝ) * a⌋₊
  let n := ⌊R ^ 2 * a⌋₊
  have hmn : m ≤ n := Nat.floor_mono (mul_le_mul_of_nonneg_right
    (Nat.floor_le (sq_nonneg R)) ha)
  have hwalk := abs_walkPath_add_sub_le (0 : Site d) p m (n - m) i
  rw [Nat.add_sub_of_le hmn] at hwalk
  have hwalk' : |(walkPath (0 : Site d) p n i : ℝ) -
      (walkPath (0 : Site d) p m i : ℝ)| ≤ ((n - m : ℕ) : ℝ) := by
    exact_mod_cast hwalk
  have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := Nat.cast_sub hmn
  rw [hcast] at hwalk'
  exact hwalk'.trans (floor_sq_time_sub_floor_mesh_le R a ha).2

/-- The square-root mesh lies within one inverse scale of the real scale. -/
theorem sqrt_floor_sq_bounds {R : ℝ} (hR : 1 ≤ R) :
    0 < Real.sqrt (⌊R ^ 2⌋₊ : ℝ) ∧
    Real.sqrt (⌊R ^ 2⌋₊ : ℝ) ≤ R ∧
    R - Real.sqrt (⌊R ^ 2⌋₊ : ℝ) ≤ 1 / R := by
  have hRpos : 0 < R := by linarith
  have hfloor : (⌊R ^ 2⌋₊ : ℝ) ≤ R ^ 2 := Nat.floor_le (sq_nonneg R)
  have hfloor' : R ^ 2 < (⌊R ^ 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hfloorpos : (0 : ℝ) < ⌊R ^ 2⌋₊ := by
    have : (1 : ℕ) ≤ ⌊R ^ 2⌋₊ := Nat.le_floor (by norm_num only [Nat.cast_one]; nlinarith [sq_nonneg (R - 1)])
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) this)
  have hspos : 0 < Real.sqrt (⌊R ^ 2⌋₊ : ℝ) := Real.sqrt_pos.2 hfloorpos
  have hs2 := Real.sq_sqrt hfloorpos.le
  have hsle : Real.sqrt (⌊R ^ 2⌋₊ : ℝ) ≤ R := by nlinarith
  refine ⟨hspos, hsle, ?_⟩
  apply (le_div_iff₀ hRpos).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hsle) hspos.le]

/-- A coordinate of a walk started at the origin is bounded by elapsed time. -/
theorem abs_walkPath_zero_le {d : ℕ} (p : ℕ → Fin d × Bool) (n : ℕ) (i : Fin d) :
    |(walkPath (0 : Site d) p n i : ℝ)| ≤ n := by
  have h := abs_walkPath_add_sub_le (0 : Site d) p 0 n i
  simpa [walkPath] using (show |(walkPath (0 : Site d) p (0 + n) i : ℝ) -
      (walkPath (0 : Site d) p 0 i : ℝ)| ≤ (n : ℝ) by exact_mod_cast h)

/-- Deterministic comparison of the two spatially rescaled walk meshes. -/
theorem abs_walkPath_rescaled_mesh_sub_le {d : ℕ}
    (p : ℕ → Fin d × Bool) {R a : ℝ} (hR : 1 ≤ R) (ha : 0 ≤ a) (i : Fin d) :
    |(walkPath (0 : Site d) p ⌊R ^ 2 * a⌋₊ i : ℝ) / R -
      (walkPath (0 : Site d) p ⌊(⌊R ^ 2⌋₊ : ℝ) * a⌋₊ i : ℝ) /
        Real.sqrt (⌊R ^ 2⌋₊ : ℝ)| ≤ (2 * a + 1) / R := by
  let s := Real.sqrt (⌊R ^ 2⌋₊ : ℝ)
  let m := ⌊(⌊R ^ 2⌋₊ : ℝ) * a⌋₊
  let n := ⌊R ^ 2 * a⌋₊
  let u : ℝ := (walkPath (0 : Site d) p n i : ℝ)
  let v : ℝ := (walkPath (0 : Site d) p m i : ℝ)
  have hRpos : 0 < R := by linarith
  obtain ⟨hspos, hsle, hsdiff⟩ := sqrt_floor_sq_bounds hR
  change 0 < s at hspos
  change s ≤ R at hsle
  change R - s ≤ 1 / R at hsdiff
  have hs2 : s ^ 2 = (⌊R ^ 2⌋₊ : ℝ) := Real.sq_sqrt (by positivity)
  have hm : (m : ℝ) ≤ s ^ 2 * a := by
    rw [hs2]
    exact Nat.floor_le (mul_nonneg (by positivity) ha)
  have hv : |v| ≤ s ^ 2 * a := (abs_walkPath_zero_le p m i).trans hm
  have huv : |u - v| ≤ a + 1 := abs_walkPath_floor_sq_sub_floor_mesh_le p R a ha i
  have hvs : |v| / s ≤ s * a := by
    apply (div_le_iff₀ hspos).2
    nlinarith
  have hcomp : |u / R - v / s| ≤ (a + 1) / R + a / R := by
    have hid : u / R - v / s = (u - v) / R - (v / s) * ((R - s) / R) := by
      field_simp
      ring
    rw [hid]
    calc
      _ ≤ |(u - v) / R| + |(v / s) * ((R - s) / R)| := by
        simpa [sub_eq_add_neg] using abs_add_le ((u - v) / R) (-(v / s * ((R - s) / R)))
      _ = |u - v| / R + (|v| / s) * ((R - s) / R) := by
        rw [abs_div, abs_of_pos hRpos, abs_mul, abs_div, abs_of_pos hspos,
          abs_div, abs_of_nonneg (sub_nonneg.mpr hsle), abs_of_pos hRpos]
      _ ≤ (a + 1) / R + (s * a) * ((R - s) / R) := by
        gcongr
      _ ≤ (a + 1) / R + a * (R - s) := by
        refine add_le_add le_rfl ?_
        calc
          _ = (s / R) * (a * (R - s)) := by ring
          _ ≤ 1 * (a * (R - s)) :=
            mul_le_mul_of_nonneg_right ((div_le_one hRpos).2 hsle)
              (mul_nonneg ha (sub_nonneg.mpr hsle))
          _ = _ := one_mul _
      _ ≤ (a + 1) / R + a / R := by
        refine add_le_add le_rfl ?_
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hsdiff ha
  convert hcomp using 1; ring

/-- Moving the starting mesh point and replacing the parabolic mesh changes the
rescaled walk by at most the starting-point error plus a vanishing pathwise bound. -/
theorem dist_walkPath_rescaled_mesh_le {d : ℕ}
    (p : ℕ → Fin d × Bool) {R a : ℝ} (hR : 1 ≤ R) (ha : 0 ≤ a)
    (z : Site d) (x : Fin d → ℝ) :
    dist (fun i => ((z i : ℝ) + (walkPath (0 : Site d) p ⌊R ^ 2 * a⌋₊ i : ℝ)) / R)
      (x + spatialScaledSite ⌊R ^ 2⌋₊
        (walkPath (0 : Site d) p ⌊(⌊R ^ 2⌋₊ : ℝ) * a⌋₊)) ≤
      dist (fun i => (z i : ℝ) / R) x + (2 * a + 1) / R := by
  have hRpos : 0 < R := by linarith
  have hbound : 0 ≤ (2 * a + 1) / R := by positivity
  apply (dist_pi_le_iff (add_nonneg dist_nonneg hbound)).2
  intro i
  have hi : |(z i : ℝ) / R - x i| ≤ dist (fun i => (z i : ℝ) / R) x := by
    simpa [Real.dist_eq] using dist_le_pi_dist (fun i => (z i : ℝ) / R) x i
  have hw := abs_walkPath_rescaled_mesh_sub_le p hR ha i
  simp only [Real.dist_eq, Pi.add_apply, spatialScaledSite]
  calc
    _ = |((z i : ℝ) / R - x i) +
        ((walkPath (0 : Site d) p ⌊R ^ 2 * a⌋₊ i : ℝ) / R -
          (walkPath (0 : Site d) p ⌊(⌊R ^ 2⌋₊ : ℝ) * a⌋₊ i : ℝ) /
            Real.sqrt (⌊R ^ 2⌋₊ : ℝ))| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hi hw)

/-- A compactly supported test of a finite-time walk position is integrable. -/
theorem integrable_test_walkPath {d : ℕ} (hd : 1 ≤ d)
    {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) (f : Site d → (Fin d → ℝ)) (n : ℕ) :
    Integrable (fun p => φ (f (walkPath (0 : Site d) p n))) (walkLaw d) := by
  have : IsProbabilityMeasure (walkLaw d) := walkLaw_isProbability hd
  obtain ⟨M, _, hM⟩ := LatticeProb.Walk.exists_norm_le_of_hasCompactSupport
    hφ.1.continuous hφ.2
  have hm : Measurable (fun p => φ (f (walkPath (0 : Site d) p n))) :=
    (measurable_of_countable (fun z : Site d => φ (f z))).comp (measurable_walkPath 0 n)
  exact (integrable_const M).mono' hm.aestronglyMeasurable (Eventually.of_forall fun p => hM _)

/-- A compactly supported test of the real-scale walk converges at moving starting points. -/
theorem tendsto_integral_test_walkPath_moving {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d)) (hB : IsBrownianSpace d 0 B PB)
    {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) (x : Fin d → ℝ)
    (z : ℝ → Site d) (hz : Tendsto (fun R : ℝ => fun i => (z R i : ℝ) / R) atTop (𝓝 x))
    {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun R : ℝ => ∫ p, φ (fun i => ((z R i : ℝ) +
      (walkPath (0 : Site d) p ⌊R ^ 2 * a⌋₊ i : ℝ)) / R) ∂(walkLaw d)) atTop
      (𝓝 (∫ β, φ (x + ofBrownianSpace B a.toNNReal β) ∂PB)) := by
  have : IsProbabilityMeasure (walkLaw d) := walkLaw_isProbability hd
  let F : ℝ → (ℕ → Fin d × Bool) → ℝ := fun R p => φ (fun i =>
    ((z R i : ℝ) + (walkPath (0 : Site d) p ⌊R ^ 2 * a⌋₊ i : ℝ)) / R)
  let G : ℝ → (ℕ → Fin d × Bool) → ℝ := fun R p => φ (x + spatialScaledSite ⌊R ^ 2⌋₊
    (walkPath (0 : Site d) p ⌊(⌊R ^ 2⌋₊ : ℝ) * a⌋₊))
  have hF : ∀ R, Integrable (F R) (walkLaw d) := fun R =>
    integrable_test_walkPath hd hφ (fun v i => ((z R i : ℝ) + (v i : ℝ)) / R) _
  have hG : ∀ R, Integrable (G R) (walkLaw d) := fun R =>
    integrable_test_walkPath hd hφ (fun v => x + spatialScaledSite ⌊R ^ 2⌋₊ v) _
  have hbound : Tendsto (fun R : ℝ => dist (fun i => (z R i : ℝ) / R) x +
      (2 * a + 1) / R) atTop (𝓝 0) := by
    have ht : Tendsto (fun R : ℝ => (2 * a + 1) / R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa using (hz.dist (tendsto_const_nhds : Tendsto (fun _ : ℝ => x) atTop (𝓝 x))).add ht
  have hdiff : Tendsto (fun R : ℝ => (∫ p, F R p ∂(walkLaw d)) -
      (∫ p, G R p ∂(walkLaw d))) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have huc : UniformContinuous φ := hφ.2.uniformContinuous_of_continuous hφ.1.continuous
    obtain ⟨δ, hδ, hδφ⟩ := Metric.uniformContinuous_iff.mp huc (ε / 2) (by positivity)
    filter_upwards [eventually_ge_atTop (1 : ℝ), hbound.eventually (gt_mem_nhds hδ)] with R hR hclose
    have hpt : ∀ p, ‖F R p - G R p‖ ≤ ε / 2 := by
      intro p
      have hp := (dist_walkPath_rescaled_mesh_le p hR ha (z R) x).trans_lt hclose
      have hf := hδφ hp
      simpa [F, G, Real.dist_eq, Real.norm_eq_abs] using hf.le
    have hi := norm_integral_le_of_norm_le_const (μ := walkLaw d) (Eventually.of_forall hpt)
    have hi' : ‖(∫ p, F R p ∂(walkLaw d)) - (∫ p, G R p ∂(walkLaw d))‖ ≤ ε / 2 := by
      rw [← integral_sub (hF R) (hG R)]
      simpa [probReal_univ] using hi
    simpa [Real.dist_eq, Real.norm_eq_abs] using lt_of_le_of_lt hi' (by linarith : ε / 2 < ε)
  have hfixed := tendsto_integral_test_spatialScaledWalk_floor_sq hd hd3 ΩB PB B hB hφ x ha
  have hsum := hdiff.add hfixed
  simpa [F, G] using hsum

end Parking
