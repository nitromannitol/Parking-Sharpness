import Parking.Support.SceneryCovarianceGreen

/-!
# Limits of scenery covariances

The scenery covariance converges to the continuum Green-kernel pairing.
-/

open MeasureTheory ProbabilityTheory Filter Topology LatticeProb

noncomputable section
namespace Parking

/-- A nonnegative parabolic time corner has the correct rescaled limit. -/
theorem tendsto_floor_time_corner (r : ℝ) (hr : 0 ≤ r) (b : Bool) :
    Tendsto (fun R : ℝ => (((⌊R ^ 2 * r⌋ + (if b then 1 else 0) : ℤ).toNat : ℕ) : ℝ) *
      (1 / R ^ 2)) atTop (𝓝 r) := by
  have hnon : ∀ R : ℝ, 0 ≤ (⌊R ^ 2 * r⌋ + (if b then 1 else 0) : ℤ) := by
    intro R
    have hf : 0 ≤ ⌊R ^ 2 * r⌋ := Int.floor_nonneg.mpr (mul_nonneg (sq_nonneg R) hr)
    cases b <;> simp_all; omega
  have h := (tendsto_floor_corner_div r b).comp (tendsto_pow_atTop two_ne_zero)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  have hc : (((⌊R ^ 2 * r⌋ + (if b then 1 else 0) : ℤ).toNat : ℕ) : ℝ) =
      ((⌊R ^ 2 * r⌋ + (if b then 1 else 0) : ℤ) : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg (hnon R))
  rw [hc]
  simp [div_eq_mul_inv]

/-- The spatial floor corners approach their underlying point. -/
theorem tendsto_floor_space_corner {d : ℕ} (x : Fin d → ℝ) (b : Fin d → Bool) :
    Tendsto (fun R : ℝ => fun i =>
      ((⌊R * x i⌋ + (if b i then 1 else 0) : ℤ) : ℝ) / R) atTop (𝓝 x) := by
  exact tendsto_pi_nhds.mpr fun i => tendsto_floor_corner_div (x i) (b i)

/-- Scenery covariances converge to their continuum white-noise pairings. -/
theorem sceneryCovarianceLimit :
  ∀ (d : ℕ), 1 ≤ d → d ≤ 3 → ∀ (ν : Measure ℤ), Parking.CriticalLaw ν →
    (∀ φ ψ, Parking.IsTestFun φ → Parking.IsTestFun ψ →
      Tendsto (fun R : ℝ => ∫ w, Parking.scenePair w R φ * Parking.scenePair w R ψ
          ∂(Parking.law d ν)) atTop
        (𝓝 (variance (fun k : ℤ => (k : ℝ)) ν * ∫ y, φ y * ψ y))) ∧
    ∀ φ, Parking.IsTestFun φ → ∀ (r : ℝ) (x : Fin d → ℝ), 0 ≤ r →
      Tendsto (fun R : ℝ => ∫ w, Parking.scenePair w R φ *
          Parking.linHatInterp (fun y => (w.1 y : ℝ)) R (r, x) ∂(Parking.law d ν)) atTop
        (𝓝 (variance (fun k : ℤ => (k : ℝ)) ν *
          ∫ y, φ y * Parking.External.contFiniteGreen d r x y)) := by
  intro d hd hd3 ν hν
  constructor
  · intro φ ψ hφ hψ
    exact tendsto_integral_scenePair_mul hd ν hν hφ hψ
  · intro φ hφ r x hr
    classical
    obtain ⟨ΩB, mΩ, PB, B, hB⟩ := LatticeProb.exists_isBrownianSpace d 0
    let : MeasurableSpace ΩB := mΩ
    let : IsProbabilityMeasure PB := hB.isProbabilityMeasure
    obtain ⟨A, hA, hφA⟩ := LatticeProb.Walk.exists_norm_bound_of_hasCompactSupport hφ.2
    let L : ℝ := variance (fun k : ℤ => (k : ℝ)) ν *
      ∫ y, φ y * External.contFiniteGreen d r x y
    let timeCorner : Bool → ℝ → ℤ := fun b R => ⌊R ^ 2 * r⌋ + (if b then 1 else 0)
    let spaceCorner : (Fin d → Bool) → ℝ → Site d := fun b R i =>
      ⌊R * x i⌋ + (if b i then 1 else 0)
    have hcorner : ∀ b : Bool × (Fin d → Bool),
        Tendsto (fun R : ℝ => R ^ ((d : ℝ) / 2 - 2) *
          (∫ w, scenePair w R φ * linPotential (confReal w)
            (timeCorner b.1 R).toNat (spaceCorner b.2 R) ∂(law d ν))) atTop (𝓝 L) := by
      intro b
      exact tendsto_scaled_integral_scenePair_mul_linPotential hd hd3 ΩB PB B hB ν hν hφ
        x (spaceCorner b.2) (tendsto_floor_space_corner x b.2)
        (fun R => (timeCorner b.1 R).toNat) hr (tendsto_floor_time_corner r hr b.1)
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hall : ∀ᶠ R : ℝ in atTop, ∀ b : Bool × (Fin d → Bool),
        |R ^ ((d : ℝ) / 2 - 2) *
          (∫ w, scenePair w R φ * linPotential (confReal w)
            (timeCorner b.1 R).toNat (spaceCorner b.2 R) ∂(law d ν)) - L| ≤ ε / 2 := by
      apply Filter.eventually_all.mpr
      intro b
      filter_upwards [Metric.tendsto_nhds.mp (hcorner b) (ε / 2) (by positivity)] with R hR
      exact (by simpa [Real.dist_eq] using hR.le)
    filter_upwards [eventually_ge_atTop (1 : ℝ), hall] with R hR hcorners
    have hgrid : ∀ m ∈ ({⌊R ^ 2 * r⌋, ⌊R ^ 2 * r⌋ + 1} : Finset ℤ),
        ∀ c ∈ Fintype.piFinset (fun i : Fin d => ({⌊R * x i⌋, ⌊R * x i⌋ + 1} : Finset ℤ)),
          |R ^ ((d : ℝ) / 2 - 2) *
            (∫ w, scenePair w R φ * linPotential (confReal w) m.toNat c ∂(law d ν)) - L| ≤ ε / 2 := by
      intro m hm c hc
      have htime : ∃ b : Bool, m = timeCorner b R := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with h | h
        · exact ⟨false, by simpa [timeCorner] using h⟩
        · exact ⟨true, by simpa [timeCorner] using h⟩
      have hspace : ∀ i, ∃ b : Bool, c i = spaceCorner (fun _ => b) R i := by
        intro i
        have hi := (Fintype.mem_piFinset.mp hc) i
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with h | h
        · exact ⟨false, by simpa [spaceCorner] using h⟩
        · exact ⟨true, by simpa [spaceCorner] using h⟩
      choose bs hbs using hspace
      obtain ⟨bt, hbt⟩ := htime
      have hceq : c = spaceCorner bs R := by
        funext i
        exact hbs i
      rw [hbt, hceq]
      exact hcorners (bt, bs)
    have hb := abs_integral_scenePair_mul_linHatInterp_sub_le hd ν hν hA hR hφA
      (r, x) L (ε / 2) hgrid
    have hlt : ε / 2 < ε := by linarith
    rw [Real.dist_eq]
    change |(∫ w, scenePair w R φ * linHatInterp (confReal w) R (r, x) ∂(law d ν)) - L| < ε
    exact hb.trans_lt hlt

end Parking

example :
  ∀ (d : ℕ), 1 ≤ d → d ≤ 3 → ∀ (ν : Measure ℤ), Parking.CriticalLaw ν →
    (∀ φ ψ, Parking.IsTestFun φ → Parking.IsTestFun ψ →
      Tendsto (fun R : ℝ => ∫ w, Parking.scenePair w R φ * Parking.scenePair w R ψ
          ∂(Parking.law d ν)) atTop
        (𝓝 (variance (fun k : ℤ => (k : ℝ)) ν * ∫ y, φ y * ψ y))) ∧
    ∀ φ, Parking.IsTestFun φ → ∀ (r : ℝ) (x : Fin d → ℝ), 0 ≤ r →
      Tendsto (fun R : ℝ => ∫ w, Parking.scenePair w R φ *
          Parking.linHatInterp (fun y => (w.1 y : ℝ)) R (r, x) ∂(Parking.law d ν)) atTop
        (𝓝 (variance (fun k : ℤ => (k : ℝ)) ν *
          ∫ y, φ y * Parking.External.contFiniteGreen d r x y)) := Parking.sceneryCovarianceLimit
