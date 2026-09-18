/-
A finite prescribed path witnesses randomness conditional on the initial field.
-/
import Parking.Support.AtomUpdate
import Parking.Support.LastMove
import Parking.Support.PositiveAtom

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

theorem walkPath_constant (x : Site d) (a : Fin d × Bool) (t : ℕ) :
    walkPath x (fun _ => a) t = x + t • stepVec a := by
  induction t with
  | zero => simp [walkPath]
  | succ t ih => rw [walkPath, ih, succ_nsmul]; abel

/-- At every horizon at least two, the particle odometer retains randomness conditional on the field. -/
theorem not_ae_pOdometer_eq_conf (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (k : ℤ) (hk : 1 ≤ k) (hkν : ν {k} ≠ 0) (t : ℕ) (F : (Site d → ℤ) → ℝ) :
    ¬ (∀ᵐ ω ∂(Parking.pDataLaw d ν),
      (pOdometer (toPDriver ω) (t + 2) 0 : ℝ) = F ω.1) := by
  classical
  intro h
  haveI := stepLaw_isProbability hd
  haveI := rankLaw_isProbability d
  haveI : IsProbabilityMeasure (Parking.moveLaw d) := by unfold Parking.moveLaw; infer_instance
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  let i : Fin d := ⟨0, hd⟩
  let a : Fin d × Bool := (i, true)
  let b : Fin d × Bool := (i, false)
  let start : Site d := -((t + 1) • unit i)
  let path : ℕ → Site d := walkPath start (fun _ => a)
  have hpath (s : ℕ) : path s = -((t + 1) • unit i) + s • unit i := by
    simp only [path, walkPath_constant, start, a, stepVec, ↓reduceIte]
  have hpath0 : path 0 = start := rfl
  have hpathT : path t = -unit i := by rw [hpath, succ_nsmul]; abel
  have hpathT1 : path (t + 1) = 0 := by rw [hpath]; exact neg_add_cancel _
  let R : Finset (Site d) := (Finset.range (t + 2)).image path
  have hR (s : ℕ) (hs : s ≤ t + 1) : path s ∈ R :=
    Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr (by omega), rfl⟩
  have hη := Measure.ae_ae_of_ae_prod h
  have hη' := ae_overwrite_infinitePi_atoms ν R (fun _ => k) (fun _ _ => hkν) hη
  obtain ⟨η₀, hη₀⟩ := hη'.exists
  let η : Site d → ℤ := fun y => if y ∈ R then k else η₀ y
  have hηpath (s : ℕ) (hs : s ≤ t + 1) : η (path s) = k := by simp [η, hR s hs]
  have hηzero : η 0 = k := by simpa only [hpathT1] using hηpath (t + 1) le_rfl
  have hηstart : η start = k := by simpa only [hpath0] using hηpath 0 (by omega)
  have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hη₀
  obtain ⟨ρ, hρ⟩ := (Measure.ae_ae_of_ae_prod hswap).exists
  let p : Label d := (start, 0)
  have ha := ae_update_infinitePi_atom (stepLaw d) (p, t) a (stepLaw_singleton_ne_zero a) hρ
  have hb := ae_update_infinitePi_atom (stepLaw d) (p, t) b (stepLaw_singleton_ne_zero b) hρ
  let Q : Finset (Label d × ℕ) := (Finset.range t).image (fun s => (p, s))
  have hforce := ae_overwrite_infinitePi_atoms (stepLaw d) Q (fun _ => a)
    (fun _ _ => stepLaw_singleton_ne_zero a) (ha.and hb)
  obtain ⟨m₀, hm₀⟩ := hforce.exists
  let m : Label d × ℕ → Fin d × Bool := fun q => if q ∈ Q then a else m₀ q
  let D : PDriver d := ⟨η, m, ρ⟩
  have hm (s : ℕ) (hs : s < t) : m (p, s) = a := by
    have hq : (p, s) ∈ Q := Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr hs, rfl⟩
    simp [m, hq]
  have hwalk (s : ℕ) (hs : s ≤ t) :
      walkPath p.1 (fun j => D.move (p, j)) s = path s := by
    apply walkPath_congr
    intro j hj
    exact hm j (lt_of_lt_of_le hj hs)
  have hactive := pActive_walk_of_nonneg D p (by change 0 < (η start).toNat; rw [hηstart]; omega)
    t (fun s hs => by
      rw [hwalk s hs]
      change 0 ≤ η (path s)
      rw [hηpath s (by omega)]
      omega)
  have hpos : (pState D t).pos p = -unit i := hactive.2.trans ((hwalk t le_rfl).trans hpathT)
  have hlast := pOdometer_last_move D t p 0 a b hactive.1
    (by rw [hpos]; simp [a, stepVec])
    (by rw [hpos]; intro heq; have hi := congrFun heq i; norm_num [b, stepVec, unit] at hi)
    (pHoles_eq_zero_of_nonneg D 0 (by change 0 ≤ η 0; rw [hηzero]; omega) t)
  have hcast : (pOdometer ⟨η, Function.update m (p, t) a, ρ⟩ (t + 2) 0 : ℝ) =
      (pOdometer ⟨η, Function.update m (p, t) b, ρ⟩ (t + 2) 0 : ℝ) + 1 := by
    exact_mod_cast hlast
  have ha' : (pOdometer ⟨η, Function.update m (p, t) a, ρ⟩ (t + 2) 0 : ℝ) = F η := hm₀.1
  have hb' : (pOdometer ⟨η, Function.update m (p, t) b, ρ⟩ (t + 2) 0 : ℝ) = F η := hm₀.2
  linarith only [hcast, ha', hb']
end Parking
