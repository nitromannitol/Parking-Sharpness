/-
Monotonicity of the odometer and of the hole counts in the configuration, for
the stack construction.

The parallel identity turns the odometer into a closed recursion,

    U_{t+1}(x) = (η(x) + ∑_{y ∼ x} I_{y,x}(U_t(y)))⁺,

in which `I_{y,x}` is nondecreasing in its argument.  Both sides are therefore
nondecreasing in `η` and in `U_t`, so raising the configuration raises the
odometer at every site and at every time, with the same instruction stacks.
The hole counts are what is left of the initial holes after the arrivals, so
they move the other way.

The activity counts do NOT follow: `A_t(x)` is a difference of odometers, and
raising the configuration at a site shifts which instruction every later
departure from that site reads, so the trajectories of everything downstream
change.  That is why the couplings of `lem:one-particle` and
`lem:tagged-monotonicity` are stated for the particle-driven construction of
`Parking/Support/Particle.lean`.
-/
import Parking.Support.MassTransport

noncomputable section

open MeasureTheory

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

theorem arrivals_mono (σ : Site d × ℕ → Site d) (y x : Site d) {m m' : ℕ} (h : m ≤ m') :
    arrivals σ y x m ≤ arrivals σ y x m' := by
  refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
  intro j hj
  exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) h)


/-- Raising the configuration raises the odometer, with the same stacks. -/
theorem U_mono {ω ω' : Data d} (hstack : ω'.2.1 = ω.2.1)
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1)
    (hconf : ∀ x, ω.1 x ≤ ω'.1 x) (t : ℕ) (x : Site d) :
    U ω t x ≤ U ω' t x := by
  induction t generalizing x with
  | zero => exact le_rfl
  | succ t ih =>
      have hstep' : ∀ q : Site d × ℕ, ω'.2.1 q ∈ nbrFinset q.1 := by
        intro q; rw [hstack]; exact hstep q
      have hpar : (U ω (t + 1) x : ℤ)
          = max 0 (ω.1 x + ∑ y ∈ nbrFinset x, (arrivals ω.2.1 y x (U ω t y) : ℤ)) :=
        (parallel_of_labelOrder (D := toDriver ω) (labelOrder d) hstep).2 t x
      have hpar' : (U ω' (t + 1) x : ℤ)
          = max 0 (ω'.1 x + ∑ y ∈ nbrFinset x, (arrivals ω'.2.1 y x (U ω' t y) : ℤ)) :=
        (parallel_of_labelOrder (D := toDriver ω') (labelOrder d) hstep').2 t x
      have hsum : ∑ y ∈ nbrFinset x, (arrivals ω.2.1 y x (U ω t y) : ℤ)
          ≤ ∑ y ∈ nbrFinset x, (arrivals ω'.2.1 y x (U ω' t y) : ℤ) := by
        refine Finset.sum_le_sum fun y _ => ?_
        have : arrivals ω.2.1 y x (U ω t y) ≤ arrivals ω'.2.1 y x (U ω' t y) := by
          rw [hstack]
          exact arrivals_mono ω.2.1 y x (ih y)
        exact_mod_cast this
      have : (U ω (t + 1) x : ℤ) ≤ (U ω' (t + 1) x : ℤ) := by
        rw [hpar, hpar']
        exact max_le_max le_rfl (by linarith [hconf x, hsum])
      exact_mod_cast this

/-- Raising the configuration lowers the hole counts, with the same stacks. -/
theorem H_antitone {ω ω' : Data d} (hstack : ω'.2.1 = ω.2.1)
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1)
    (hconf : ∀ x, ω.1 x ≤ ω'.1 x) (t : ℕ) (x : Site d) :
    H ω' t x ≤ H ω t x := by
  have hstep' : ∀ q : Site d × ℕ, ω'.2.1 q ∈ nbrFinset q.1 := by
    intro q; rw [hstack]; exact hstep q
  have h1 : H ω t x = (-(ω.1 x)).toNat
      - ∑ y ∈ nbrFinset x, arrivals ω.2.1 y x (U ω t y) := by
    show holeCount (toDriver ω) t x = _
    rw [holeCount_eq (toDriver ω) t x, totalArrivals_eq (labelOrder d) hstep t x]
    rfl
  have h2 : H ω' t x = (-(ω'.1 x)).toNat
      - ∑ y ∈ nbrFinset x, arrivals ω'.2.1 y x (U ω' t y) := by
    show holeCount (toDriver ω') t x = _
    rw [holeCount_eq (toDriver ω') t x, totalArrivals_eq (labelOrder d) hstep' t x]
    rfl
  have hstart : (-(ω'.1 x)).toNat ≤ (-(ω.1 x)).toNat := by
    have := hconf x
    omega
  have hsum : ∑ y ∈ nbrFinset x, arrivals ω.2.1 y x (U ω t y)
      ≤ ∑ y ∈ nbrFinset x, arrivals ω'.2.1 y x (U ω' t y) := by
    refine Finset.sum_le_sum fun y _ => ?_
    rw [hstack]
    exact arrivals_mono ω.2.1 y x (U_mono hstack hstep hconf t y)
  rw [h1, h2]
  omega

end Parking

end
