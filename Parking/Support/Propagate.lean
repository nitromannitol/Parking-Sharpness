/-
The odometer propagates through the lattice.

The last part of Step 2 of `prop:everyone-settles` (`parking.tex:1526-1532`):
"Almost surely, the stack at each `y` sends infinitely many instructions to each
neighbour `x`.  If `U_∞(y) = ∞`, then every instruction at `y` is eventually
used, so `x` receives infinitely many arrivals.  At most `η(x)⁻ < ∞` of them
settle at `x`, and every other arrival leads to a departure.  Connectedness of
`ℤ^d` shows that every site has infinite odometer."

The bookkeeping of that sentence is already `lem:parallel`, which is sealed:
`U_{n+1}(x) = (η(x) + ∑_{y ∼ x} I_{y,x}(U_n(y)))⁺`, where `I_{y,x}(m)` counts the
instructions among the first `m` at `y` that point at `x`.  So the arrivals from
one neighbour alone force the odometer, and the only input left is that the
stack at `y` points at `x` infinitely often.
-/
import Parking.Frozen.Parallel
import Parking.Support.OdometerInfinite
import Parking.Support.Monotone
import Parking.Support.Odometer

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Filter
open scoped ENNReal

variable {d : ℕ}

theorem exists_arrivals_ge {stack : Site d × ℕ → Site d} {y x : Site d}
    (h : {j : ℕ | stack (y, j) = x}.Infinite) (M : ℕ) :
    ∃ m : ℕ, M ≤ LatticeProb.arrivals stack y x m := by
  classical
  obtain ⟨s, hs, hcard⟩ := h.exists_subset_card_eq M
  obtain ⟨m, hm⟩ := s.exists_nat_subset_range
  refine ⟨m, ?_⟩
  rw [← hcard]
  refine Finset.card_le_card ?_
  intro j hj
  exact Finset.mem_filter.mpr ⟨hm hj, hs hj⟩

/-- **The odometer propagates to a neighbour.**  If the stack at `y` sends
infinitely many instructions to a neighbour `x` and the odometer at `y` is
infinite, then so is the odometer at `x`: by `lem:parallel` the odometer at `x`
after `n+1` rounds is at least `η(x)` plus the arrivals from `y`. -/
theorem Ulimit_top_of_nbr {ω : Data d}
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ LatticeProb.nbrFinset q.1)
    {y x : Site d} (hx : x ∈ LatticeProb.nbrFinset y)
    (hinf : {j : ℕ | ω.2.1 (y, j) = x}.Infinite)
    (hy : Parking.Ulimit ω y = ⊤) : Parking.Ulimit ω x = ⊤ := by
  classical
  rw [Ulimit_eq_top_iff] at hy ⊢
  intro M
  obtain ⟨m, hm⟩ := exists_arrivals_ge hinf (M + (ω.1 x).natAbs)
  obtain ⟨n, hn⟩ := hy m
  refine ⟨n + 1, ?_⟩
  have hpar := (Parking.Frozen.parallel ω hstep).2 n x
  have hyx : y ∈ LatticeProb.nbrFinset x := nbrFinset_symm hx
  have hterm : (LatticeProb.arrivals ω.2.1 y x (Parking.U ω n y) : ℤ)
      ≤ ∑ z ∈ LatticeProb.nbrFinset x,
        (LatticeProb.arrivals ω.2.1 z x (Parking.U ω n z) : ℤ) := by
    refine Finset.single_le_sum (f := fun z : Site d =>
      (LatticeProb.arrivals ω.2.1 z x (Parking.U ω n z) : ℤ)) (fun z _ => ?_) hyx
    exact Int.natCast_nonneg _
  have hmono : (M + (ω.1 x).natAbs : ℤ)
      ≤ (LatticeProb.arrivals ω.2.1 y x (Parking.U ω n y) : ℤ) := by
    have := arrivals_mono ω.2.1 y x hn
    have h2 : (M + (ω.1 x).natAbs) ≤ LatticeProb.arrivals ω.2.1 y x (Parking.U ω n y) :=
      le_trans hm this
    exact_mod_cast h2
  have habs : -(ω.1 x) ≤ ((ω.1 x).natAbs : ℤ) := by
    rcases Int.natAbs_eq (ω.1 x) with h | h
    · omega
    · omega
  have hle : (M : ℤ) ≤ (Parking.U ω (n + 1) x : ℤ) := by
    rw [hpar]
    refine le_trans ?_ (le_max_right 0 _)
    linarith
  exact_mod_cast hle


/-- The `ℓ¹` distance on the lattice, as a natural number. -/
def latDist (x y : Site d) : ℕ := ∑ i : Fin d, (x i - y i).natAbs

theorem latDist_eq_zero {x y : Site d} (h : latDist x y = 0) : x = y := by
  funext i
  have h1 : ∀ i : Fin d, (x i - y i).natAbs = 0 := by
    intro i
    have := Finset.sum_eq_zero_iff.mp h i (Finset.mem_univ i)
    exact this
  have := h1 i
  omega

/-- **The odometer propagates everywhere.**  `ℤ^d` is connected, so an infinite
odometer at one site makes every odometer infinite. -/
theorem Ulimit_top_of_exists {ω : Data d}
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ LatticeProb.nbrFinset q.1)
    (hinf : ∀ y x : Site d, x ∈ LatticeProb.nbrFinset y →
      {j : ℕ | ω.2.1 (y, j) = x}.Infinite)
    {y : Site d} (hy : Parking.Ulimit ω y = ⊤) (x : Site d) :
    Parking.Ulimit ω x = ⊤ := by
  classical
  induction hn : latDist x y using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst hn
      rw [latDist_eq_zero h0]
      exact hy
    · have hne : ∃ i : Fin d, x i ≠ y i := by
        by_contra hc
        push Not at hc
        have : latDist x y = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [hc i]; simp
        omega
      obtain ⟨i, hi⟩ := hne
      set s : ℤ := if y i < x i then 1 else -1 with hs
      set x' : Site d := x - s • LatticeProb.unit i with hx'
      have hcoord : ∀ j : Fin d, x' j = if j = i then x i - s else x j := by
        intro j
        by_cases hj : j = i
        · subst hj; simp [hx', LatticeProb.unit, Pi.single_eq_same]
        · simp [hx', LatticeProb.unit, hj]
      have hlt : latDist x' y < latDist x y := by
        rw [latDist, latDist]
        refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
        · rcases eq_or_ne j i with hj | hj
          · rw [hj, hcoord i, if_pos rfl]
            rcases lt_or_ge (y i) (x i) with h | h
            · rw [hs, if_pos h]; omega
            · rw [hs, if_neg (not_lt.mpr h)]; omega
          · rw [hcoord j, if_neg hj]
        · rw [hcoord i, if_pos rfl]
          rcases lt_or_ge (y i) (x i) with h | h
          · rw [hs, if_pos h]; omega
          · rw [hs, if_neg (not_lt.mpr h)]; omega
      have hmemx : x ∈ LatticeProb.nbrFinset x' := by
        simp only [LatticeProb.nbrFinset, Finset.mem_biUnion, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton]
        refine ⟨i, ?_⟩
        rcases lt_or_ge (y i) (x i) with h | h
        · left
          simp only [hx', hs, if_pos h, one_smul]
          abel
        · right
          simp only [hx', hs, if_neg (not_lt.mpr h)]
          funext j
          simp [LatticeProb.unit, Pi.single_apply]
      have hx'top : Parking.Ulimit ω x' = ⊤ := by
        refine ih (latDist x' y) (by omega) x' rfl
      exact Ulimit_top_of_nbr hstep hmemx (hinf x' x hmemx) hx'top

end Parking
