/-
The range of the independent walk, the tilted one-site law, and the
conditional quantities of Sections 7 to 9 of `parking.tex`.

- `rangeCard d x p t` is `|R_t|`, the number of distinct sites the walk from
  `x` visits up to and including time `t`.
- `tiltLaw ν l` is the law `P_l(η(0)=j) = e^{lj}P(η(0)=j)/E e^{l\eta(0)}` of
  Section 9, and `drift ν l` is `δ(l) = -E_l\eta(0)`.
- `survivalGiven d ν k t` is `P(τ_1 > t | η(0) = k)` and
  `survivalGivenWalk d ν k t w` is `P(τ_1 > t | η(0)=k, X_0,…,X_t)` for the
  walk `w` assigned to the first particle at the origin.  Conditioning on the
  walk is realized by prescribing the moves of the label `(0,0)`, which is why
  these use the particle-driven construction; conditioning on `{η(0)=k}` is a
  division by `ν {k}`, and every statement using it assumes that this is not
  zero.
- `fullGreen d x` is `G(x) = ∑_n P^n(0,x)` and `escapeConst d` is `g = G(0)`.
- `phi d s` is `φ_d(s)` of Section 9 and `orientedKappa d n` is
  `\vec\kappa_d(n)` of Section 10.
-/
import Parking.Support.Particle

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Parking

/-- `|R_t|`, the number of distinct sites visited by time `t`. -/
def rangeCard {d : ℕ} (x : Site d) (p : ℕ → Fin d × Bool) (t : ℕ) : ℕ :=
  ((Finset.range (t + 1)).image fun j => walkPath x p j).card

/-- The tilted one-site law. -/
def tiltLaw (ν : Measure ℤ) (l : ℝ) : Measure ℤ :=
  (∫⁻ k, ENNReal.ofReal (Real.exp (l * k)) ∂ν)⁻¹ •
    ν.withDensity fun k => ENNReal.ofReal (Real.exp (l * k))

/-- `δ(l) = -E_l η(0)`. -/
def drift (ν : Measure ℤ) (l : ℝ) : ℝ := -∫ k, (k : ℝ) ∂(tiltLaw ν l)

/-- `P(τ_1 > t | η(0) = k)`, the chance that the first particle at the origin
is still active after round `t`. -/
def survivalGiven (d : ℕ) (ν : Measure ℤ) (k : ℕ) (t : ℕ) : ℝ :=
  ((Parking.law d ν) {ω | ω.1 0 = (k : ℤ) ∧
      (LatticeProb.state (Parking.toDriver ω) t).active (0, 0) = true}).toReal
    / (ν {(k : ℤ)}).toReal

/-- Prescribing the moves of the first particle at the origin. -/
def setMoves {d : ℕ} (w : ℕ → Fin d × Bool) (ω : PData d) : PData d :=
  (ω.1, (fun q => if q.1 = ((0 : Site d), 0) then w q.2 else ω.2.1 q), ω.2.2)

/-- `P(τ_1 > t | η(0)=k, X_0,…,X_t)` for the prescribed walk `w`. -/
def survivalGivenWalk (d : ℕ) (ν : Measure ℤ) (k : ℕ) (t : ℕ)
    (w : ℕ → Fin d × Bool) : ℝ :=
  (∫ ω, Set.indicator {ω' : PData d | ω'.1 0 = (k : ℤ) ∧
        (pState (toPDriver ω') t).active (0, 0) = true}
      (fun _ => (1 : ℝ)) (setMoves w ω) ∂(pDataLaw d ν))
    / (ν {(k : ℤ)}).toReal

/-- The Green function `G(x) = ∑_n P^n(0, x)` of the walk. -/
def fullGreen (d : ℕ) (x : Site d) : ℝ := ∑' n : ℕ, heat d n x

/-- `g = G(0)`, the expected number of visits to the origin. -/
def escapeConst (d : ℕ) : ℝ := fullGreen d 0

/-- `φ_d(s)` of Section 9. -/
def phi (d : ℕ) (s : ℝ) : ℝ :=
  if d ≤ 3 then (s + 1) ^ ((4 - (d : ℝ)) / 4) else Real.log (s + 2)

/-- `\vec\kappa_d(n)` of Section 10. -/
def orientedKappa (d : ℕ) (n : ℕ) : ℝ :=
  if d = 2 then (n : ℝ) ^ ((1 : ℝ) / 2) else if d = 3 then Real.log ((n : ℝ) + 1) else 1

/-- `E u_∞(0)` in `ℝ≥0∞`, so that an unbounded mean is `⊤` and not a junk
value. -/
def meanuLimit {d : ℕ} (P : Measure (Data d)) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (Parking.meanu P n)

/-- The probability that the origin carries an unfilled hole after round `t`. -/
def holeProb (d : ℕ) (ν : Measure ℤ) (t : ℕ) : ℝ :=
  ((Parking.law d ν) {ω | Parking.H ω t 0 = 1}).toReal

/-- Adding one particle at `x₀`, every other particle keeping its walk and its
uniform variables. -/
def addAt {d : ℕ} (x₀ : Site d) (ω : PData d) : PData d := (addParticle x₀ ω.1, ω.2)

/-- Deleting one particle at `x₀`, the inverse of `addAt` on the counts. -/
def delAt {d : ℕ} (x₀ : Site d) (ω : PData d) : PData d :=
  ((fun x => if x = x₀ then ω.1 x - 1 else ω.1 x), ω.2)

/-- The law in which the sites of `N` carry the one-site law `ν` with fresh
walks and uniform variables, and everything else is the fixed background `ω₀`.
This is "finitely many sites carrying the tilted law, conditioned on the
remaining randomness" of `lem:product`. -/
def restrictLaw (d : ℕ) (N : Finset (Site d)) (ν : Measure ℤ) (ω₀ : PData d) :
    Measure (PData d) :=
  (pDataLaw d ν).map fun ω =>
    ((fun x => if x ∈ N then ω.1 x else ω₀.1 x),
      (fun q : Label d × ℕ => if q.1.1 ∈ N then ω.2.1 q else ω₀.2.1 q),
      (fun q : Label d × ℕ => if q.1.1 ∈ N then ω.2.2 q else ω₀.2.2 q))

/-- Relabeling the particles at `x₀` by `σ`, carrying their walks and uniform
variables with them. -/
def relabelAt {d : ℕ} (x₀ : Site d) (σ : Equiv.Perm ℕ) (ω : PData d) : PData d :=
  (ω.1,
    (fun q : Label d × ℕ =>
      ω.2.1 (((q.1.1, if q.1.1 = x₀ then σ q.1.2 else q.1.2), q.2))),
    (fun q : Label d × ℕ =>
      ω.2.2 (((q.1.1, if q.1.1 = x₀ then σ q.1.2 else q.1.2), q.2))))

/-- `F` is a function of the counts, walks and uniform variables at the sites
of `N` alone. -/
def DependsOn {d : ℕ} (N : Finset (Site d)) (F : PData d → ℝ) : Prop :=
  ∀ ω ω' : PData d, (∀ x ∈ N, ω.1 x = ω'.1 x) →
    (∀ q : Label d × ℕ, q.1.1 ∈ N → ω.2.1 q = ω'.2.1 q) →
    (∀ q : Label d × ℕ, q.1.1 ∈ N → ω.2.2 q = ω'.2.2 q) → F ω = F ω'

/-- The uniform variables of a realization are pairwise distinct.  The settling
rule orders two arrivals of equal uniform variable by their labels, which
relabeling the particles at a site changes, so the process is equivariant under
relabeling only here; the uniform variables are independent and atomless, so
this set carries the whole mass (`Parking.ae_injective_pDataLaw`). -/
def RanksDistinct {d : ℕ} (ω : PData d) : Prop := Function.Injective ω.2.2

/-- `F` is symmetric in the particles PRESENT at a site.  The permutation `σ`
moves only the labels below the count at `x₀`, the labels of the particles that
are there, and fixes every label the site does not carry; when the count at `x₀`
is nonpositive the site carries no particle and the condition forces `σ` to be
the identity.  The identity is asked for at the realizations whose uniform
variables are pairwise distinct, which is where the paper's ranks live. -/
def SymmetricInParticles {d : ℕ} (F : PData d → ℝ) : Prop :=
  ∀ (x₀ : Site d) (σ : Equiv.Perm ℕ) (ω : PData d), RanksDistinct ω →
    (∀ i : ℕ, (ω.1 x₀).toNat ≤ i → σ i = i) → F (relabelAt x₀ σ ω) = F ω

/-- `F` reads the particles present alone: with the counts held fixed, altering
the walk or the uniform variables attached to a label that carries no particle
does not change `F`.  A site with count `k` carries the `k` particles labelled
`0, …, k - 1` and nothing else, so a function of "the counts, walks and uniform
variables at these sites" cannot read the data of a label the site does not
carry. -/
def ReadsParticles {d : ℕ} (F : PData d → ℝ) : Prop :=
  ∀ ω ω' : PData d, RanksDistinct ω → RanksDistinct ω' → ω.1 = ω'.1 →
    (∀ q : Label d × ℕ, q.1.2 < (ω.1 q.1.1).toNat → ω.2.1 q = ω'.2.1 q) →
    (∀ q : Label d × ℕ, q.1.2 < (ω.1 q.1.1).toNat → ω.2.2 q = ω'.2.2 q) →
    F ω = F ω'

/-- `F` is a function of the counts and of the particles present, invariant
under relabeling those particles.  This is the pair of clauses
`parking.tex:2321-2332` puts on `F` and on `Z`, "functions of the counts, walks,
and uniform variables at these sites, each invariant under relabeling the
particles at a site": a site with count `k` carries the `k` particles labelled
`0, …, k - 1`, so such a function neither reads the data attached to a label the
site does not carry nor distinguishes the particles it does carry. -/
def RelabelInvariant {d : ℕ} (F : PData d → ℝ) : Prop :=
  SymmetricInParticles F ∧ ReadsParticles F

/-- Adding a particle leaves the uniform variables alone. -/
theorem RanksDistinct.addAt {d : ℕ} (x₀ : Site d) {ω : PData d} (h : RanksDistinct ω) :
    RanksDistinct (Parking.addAt x₀ ω) := h

/-- Deleting a particle leaves the uniform variables alone. -/
theorem RanksDistinct.delAt {d : ℕ} (x₀ : Site d) {ω : PData d} (h : RanksDistinct ω) :
    RanksDistinct (Parking.delAt x₀ ω) := h

/-- Relabeling permutes the uniform variables, so it preserves their distinctness. -/
theorem RanksDistinct.relabelAt {d : ℕ} (x₀ : Site d) (σ : Equiv.Perm ℕ) {ω : PData d}
    (h : RanksDistinct ω) : RanksDistinct (Parking.relabelAt x₀ σ ω) := by
  rintro ⟨⟨x, i⟩, t⟩ ⟨⟨y, j⟩, s⟩ hq
  have hq' := h hq
  simp only [Prod.mk.injEq] at hq'
  obtain ⟨⟨hxy, hij⟩, hts⟩ := hq'
  subst hxy
  subst hts
  by_cases hx : x = x₀
  · rw [if_pos hx, if_pos hx] at hij
    rw [σ.injective hij]
  · rw [if_neg hx, if_neg hx] at hij
    rw [hij]

end Parking

end
