/-
Lemma 3.3 of parking.tex, frozen.  `parking.tex:682-690` (label
`lem:one-particle`):

  "Let $\eta$ and $\widetilde\eta$ agree at every site except one, where
   $\widetilde\eta$ exceeds $\eta$ by one, and couple the two processes by
   giving every particle they share the same walk and the same uniform
   variables.  Then, for every $t\geq0$, either $\widetilde H_t=H_t$ and
   $\widetilde A_t-A_t$ is one at a single site and zero elsewhere, or
   $\widetilde A_t=A_t$ and $H_t-\widetilde H_t$ is one at a single site and
   zero elsewhere."

The coupling of the statement is the particle-driven construction of
`Parking/Support/Particle.lean`, in which each particle carries its own walk
and its own uniform variables; `addParticleDriver x₀` raises the configuration
by one at `x₀` and changes nothing else.
-/
import Parking.Support.OneParticle

-- The dimension bound is part of the standing setting of the paper, not of the
-- argument; the proof does not read it.
set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.one_particle (d : ℕ) (hd : 1 ≤ d) (D : Parking.PDriver d)
    (x₀ : Parking.Site d) (t : ℕ) :
    ((∀ x, Parking.pHoleCount (Parking.addParticleDriver x₀ D) t x
          = Parking.pHoleCount D t x) ∧
      ∃ z, Parking.pActiveCount (Parking.addParticleDriver x₀ D) t z
            = Parking.pActiveCount D t z + 1 ∧
          ∀ x, x ≠ z → Parking.pActiveCount (Parking.addParticleDriver x₀ D) t x
            = Parking.pActiveCount D t x) ∨
    ((∀ x, Parking.pActiveCount (Parking.addParticleDriver x₀ D) t x
          = Parking.pActiveCount D t x) ∧
      ∃ z, Parking.pHoleCount D t z
            = Parking.pHoleCount (Parking.addParticleDriver x₀ D) t z + 1 ∧
          ∀ x, x ≠ z → Parking.pHoleCount D t x
            = Parking.pHoleCount (Parking.addParticleDriver x₀ D) t x)
-- FROZEN-STATEMENT-END
:= Parking.one_particle_of_labelOrder (Parking.labelOrder d) D x₀ t
