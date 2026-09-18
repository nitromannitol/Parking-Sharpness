/-
The algebraic half of `lem:w-martingale`: the error field of
`eq:error-recursion` written as one increment per instruction.

`Parking.wErr` is defined by `w_{k+1} = P w_k + e_k`, where the error of round
`k` is the discrepancy between the arrivals a site actually receives and the
number it receives on average.  Unrolling the recursion writes `w_n` as the
kernel `P^{n-1-k}` applied to the error of each round, and pairing against the
kernel turns each of those into one term for each instruction read in the
round.  Summing over the rounds, the terms belonging to one instruction
telescope into `g_{n-s}(ρ_j(y)) - (P g_{n-s})(y)`, where `s` is the round in
which the instruction is first read.  That is the display of
`parking.tex:1145-1152`, and it is what the martingale of `lem:w-martingale`
is assembled from.
-/
import Parking.Support.GammaSum
import Parking.Support.DeferredIntegral

noncomputable section

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-! ### Sums over the neighbours of a site -/

/-- A sum over the neighbours of `x` is the sum of the `2d` directed terms. -/
theorem sum_nbrFinset_eq (x : Site d) (f : Site d → ℝ) :
    ∑ y ∈ nbrFinset x, f y = ∑ i : Fin d, (f (x + unit i) + f (x - unit i)) := by
  classical
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin d)) : Set (Fin d))
      fun i : Fin d => ({x + unit i, x - unit i} : Finset (Site d)) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr ?_
    intro z hz hz'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
    rcases hz with rfl | rfl <;> rcases hz' with h | h
    · exact hij (unit_add_left_inj h)
    · exact unit_add_ne_sub x i j h
    · exact unit_add_ne_sub x j i h.symm
    · exact hij (unit_sub_left_inj h)
  have hnbr : nbrFinset x = (Finset.univ : Finset (Fin d)).biUnion
      fun i : Fin d => ({x + unit i, x - unit i} : Finset (Site d)) := rfl
  rw [hnbr, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finset.sum_pair (unit_add_ne_sub x i i)

/-- The walk operator is linear over a finite sum. -/
theorem walkOp_sum {ι : Type*} (s : Finset ι) (f : ι → Site d → ℝ) :
    (walkOp fun x => ∑ i ∈ s, f i x) = fun x => ∑ i ∈ s, walkOp (f i) x := by
  funext x
  simp only [walkOp, nbrSum, ← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]

/-! ### The error of one round, and the unrolled recursion -/

/-- The error of round `k`, the discrepancy at `x` between the arrivals it
receives from its neighbours and the number it receives on average. -/
def errorTerm (ω : Data d) (k : ℕ) (x : Site d) : ℝ :=
  ∑ y ∈ nbrFinset x,
    ((arrivals ω.2.1 y x (U ω k y) : ℝ) - (U ω k y : ℝ) / (2 * d))

theorem wErr_succ (ω : Data d) (k : ℕ) :
    wErr ω (k + 1) = fun x => walkOp (wErr ω k) x + errorTerm ω k x := rfl

/-- The error field is the kernel applied to the error of each round. -/
theorem wErr_eq_iterate (ω : Data d) (n : ℕ) :
    wErr ω n = fun x => ∑ k ∈ Finset.range n, (walkOp^[n - (k + 1)] (errorTerm ω k)) x := by
  induction n with
  | zero => funext x; simp [wErr]
  | succ n ih =>
      funext x
      have hstep : ∀ k ∈ Finset.range n,
          walkOp (walkOp^[n - (k + 1)] (errorTerm ω k)) x
            = (walkOp^[n + 1 - (k + 1)] (errorTerm ω k)) x := by
        intro k hk
        rw [Finset.mem_range] at hk
        have hk' : n + 1 - (k + 1) = (n - (k + 1)) + 1 := by omega
        rw [hk', Function.iterate_succ_apply']
      have hlast : (walkOp^[n + 1 - (n + 1)] (errorTerm ω n)) x = errorTerm ω n x := by
        simp
      rw [wErr_succ, ih, Finset.sum_range_succ, hlast]
      simp only [walkOp_sum]
      rw [Finset.sum_congr rfl hstep]

/-! ### Pairing against the kernel -/

theorem heat_eq_zero_of_lt {m : ℕ} {x : Site d} (h : m < graphNorm x) : heat d m x = 0 := by
  rw [heat_eq_srwHeat]
  exact LatticeProb.srwHeat_eq_zero_of_lt (by rw [← graphNorm_eq_srw]; exact h)

theorem heat_eq_zero_of_notMem_box {m : ℕ} {x : Site d}
    (h : x ∉ boxFinset (0 : Site d) m) : heat d m x = 0 := by
  have hsup : m < supNorm x := by
    by_contra hc
    exact h (mem_boxFinset_zero_iff.mpr (by omega))
  exact heat_eq_zero_of_lt (lt_of_lt_of_le hsup (supNorm_le_graphNorm x))

theorem summable_heat_mul (m : ℕ) (u : Site d → ℝ) :
    Summable fun x : Site d => heat d m x * u x := by
  refine summable_of_ne_finset_zero (s := boxFinset (0 : Site d) m) fun x hx => ?_
  rw [heat_eq_zero_of_notMem_box hx, zero_mul]

/-- The kernel pairing: iterating the walk operator `m` times and reading the
value at the origin is integration against `P^m(0, ·)`. -/
theorem iterate_walkOp_apply_zero (m : ℕ) (u : Site d → ℝ) :
    (walkOp^[m] u) 0 = ∑' x : Site d, heat d m x * u x := by
  induction m generalizing u with
  | zero =>
      rw [Function.iterate_zero_apply]
      rw [tsum_eq_single (0 : Site d)]
      · show u 0 = (if (0 : Site d) = 0 then (1 : ℝ) else 0) * u 0
        simp
      · intro x hx
        show (if x = 0 then (1 : ℝ) else 0) * u x = 0
        rw [if_neg hx, zero_mul]
  | succ m ih =>
      rw [Function.iterate_succ_apply, ih]
      have hshift : ∀ i : Fin d,
          (∑' x : Site d, heat d m x * u (x + unit i))
            = ∑' z : Site d, heat d m (z - unit i) * u z := by
        intro i
        have := (Equiv.addRight (unit i)).tsum_eq
          (fun z : Site d => heat d m (z - unit i) * u z)
        rw [← this]
        exact tsum_congr fun x => by simp
      have hshift' : ∀ i : Fin d,
          (∑' x : Site d, heat d m x * u (x - unit i))
            = ∑' z : Site d, heat d m (z + unit i) * u z := by
        intro i
        have := (Equiv.subRight (unit i)).tsum_eq
          (fun z : Site d => heat d m (z + unit i) * u z)
        rw [← this]
        exact tsum_congr fun x => by simp
      have hsum1 : ∀ i : Fin d, Summable fun x : Site d => heat d m x * u (x + unit i) :=
        fun i => summable_heat_mul m _
      have hsum2 : ∀ i : Fin d, Summable fun x : Site d => heat d m x * u (x - unit i) :=
        fun i => summable_heat_mul m _
      have hsumA : ∀ i : Fin d, Summable fun z : Site d => heat d m (z - unit i) * u z := by
        intro i
        rw [← (Equiv.addRight (unit i)).summable_iff]
        refine (hsum1 i).congr fun x => ?_
        simp
      have hsumB : ∀ i : Fin d, Summable fun z : Site d => heat d m (z + unit i) * u z := by
        intro i
        rw [← (Equiv.subRight (unit i)).summable_iff]
        refine (hsum2 i).congr fun x => ?_
        simp
      have hstep : (∑' x : Site d, heat d m x * walkOp u x)
          = (∑ i : Fin d, ((∑' x : Site d, heat d m x * u (x + unit i))
              + ∑' x : Site d, heat d m x * u (x - unit i))) / (2 * d) := by
        have hpt : ∀ x : Site d, heat d m x * walkOp u x
            = (∑ i : Fin d, (heat d m x * u (x + unit i) + heat d m x * u (x - unit i)))
                / (2 * d) := by
          intro x
          show heat d m x * (nbrSum u x / (2 * d)) = _
          rw [nbrSum, ← mul_div_assoc]
          congr 1
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [tsum_congr hpt, tsum_div_const]
        congr 1
        rw [Summable.tsum_finsetSum fun i _ => ((hsum1 i).add (hsum2 i))]
        exact Finset.sum_congr rfl fun i _ => (hsum1 i).tsum_add (hsum2 i)
      rw [hstep]
      have hcollect : (∑ i : Fin d, ((∑' z : Site d, heat d m (z - unit i) * u z)
            + ∑' z : Site d, heat d m (z + unit i) * u z)) / (2 * d)
          = ∑' z : Site d, heat d (m + 1) z * u z := by
        have hpair : ∀ i : Fin d, (∑' z : Site d, heat d m (z - unit i) * u z)
              + ∑' z : Site d, heat d m (z + unit i) * u z
            = ∑' z : Site d, (heat d m (z - unit i) * u z + heat d m (z + unit i) * u z) :=
          fun i => ((hsumA i).tsum_add (hsumB i)).symm
        rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hpair i,
          ← Summable.tsum_finsetSum fun i _ => ((hsumA i).add (hsumB i)), ← tsum_div_const]
        refine tsum_congr fun z => ?_
        show (∑ i : Fin d, ((heat d m (z - unit i) * u z) + heat d m (z + unit i) * u z))
            / (2 * d) = walkOp (heat d m) z * u z
        rw [walkOp, nbrSum, div_mul_eq_mul_div, Finset.sum_mul]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
        congrArg₂ (· + ·) (hshift i) (hshift' i), hcollect]

/-! ### The error of a round, one instruction at a time -/

theorem supNorm_le_succ_of_mem_nbrFinset {y x : Site d} (h : x ∈ nbrFinset y) :
    supNorm y ≤ supNorm x + 1 := by
  have hcoord : ∀ j : Fin d, (y j).natAbs ≤ (x j).natAbs + 1 := by
    obtain ⟨i, hi | hi⟩ := mem_nbrFinset_iff.mp h
    · intro j
      by_cases hj : j = i
      · subst hj
        have : x j = y j + 1 := by rw [hi]; simp [unit]
        omega
      · have : x j = y j := by
          rw [hi]; simp only [unit, Pi.add_apply, Pi.single_eq_of_ne hj, add_zero]
        omega
    · intro j
      by_cases hj : j = i
      · subst hj
        have : x j = y j - 1 := by rw [hi]; simp [unit]
        omega
      · have : x j = y j := by
          rw [hi]; simp only [unit, Pi.sub_apply, Pi.single_eq_of_ne hj, sub_zero]
        omega
  refine Finset.sup_le fun j _ => ?_
  have hle : (x j).natAbs ≤ supNorm x := Finset.le_sup (f := fun i => (x i).natAbs) (mem_univ j)
  exact le_trans (hcoord j) (by omega)

/-- Pairing the kernel against the error of one round at a single site: the
arrivals at the neighbours of `y` are the instructions the odometer has read
there, and the average term is the kernel one step further out. -/
theorem sum_nbr_heat_mul_error (hd : 1 ≤ d) (ω : Data d)
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1) (m k : ℕ) (y : Site d) :
    (∑ x ∈ nbrFinset y, heat d m x
        * ((arrivals ω.2.1 y x (U ω k y) : ℝ) - (U ω k y : ℝ) / (2 * d)))
      = ∑ j ∈ Finset.range (U ω k y), (heat d m (ω.2.1 (y, j)) - heat d (m + 1) y) := by
  classical
  set M := U ω k y with hM
  have hmaps : ∀ j ∈ Finset.range M, ω.2.1 (y, j) ∈ nbrFinset y :=
    fun j _ => hstep (y, j)
  have harr : (∑ x ∈ nbrFinset y, heat d m x * (arrivals ω.2.1 y x M : ℝ))
      = ∑ j ∈ Finset.range M, heat d m (ω.2.1 (y, j)) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps fun j => heat d m (ω.2.1 (y, j))]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hcard : ((Finset.range M).filter fun j => ω.2.1 (y, j) = x).card
        = arrivals ω.2.1 y x M := rfl
    rw [← hcard, Finset.sum_congr rfl (g := fun _ => heat d m x)
      (fun j hj => by rw [(Finset.mem_filter.mp hj).2]), Finset.sum_const, nsmul_eq_mul]
    ring
  have hnbrsum : (∑ x ∈ nbrFinset y, heat d m x) = 2 * (d : ℝ) * heat d (m + 1) y := by
    have h1 : (∑ x ∈ nbrFinset y, heat d m x) = nbrSum (heat d m) y := by
      rw [sum_nbrFinset_eq y (heat d m), nbrSum]
    have h2 : heat d (m + 1) y = walkOp (heat d m) y := rfl
    rw [h1, h2, walkOp]
    field_simp
  have hd0 : (2 : ℝ) * (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hd
    positivity
  have hsplit : (∑ x ∈ nbrFinset y, heat d m x
        * ((arrivals ω.2.1 y x M : ℝ) - (M : ℝ) / (2 * d)))
      = (∑ x ∈ nbrFinset y, heat d m x * (arrivals ω.2.1 y x M : ℝ))
        - (M : ℝ) / (2 * d) * ∑ x ∈ nbrFinset y, heat d m x := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hsplit, harr, hnbrsum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_range]
  field_simp

/-- The kernel paired against the error of round `k`: one term for each
instruction the odometer has read, and the average subtracted one step further
out. -/
theorem tsum_heat_mul_errorTerm (hd : 1 ≤ d) (ω : Data d)
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1) (m k : ℕ) :
    (∑' x : Site d, heat d m x * errorTerm ω k x)
      = ∑' y : Site d, ∑ j ∈ Finset.range (U ω k y),
          (heat d m (ω.2.1 (y, j)) - heat d (m + 1) y) := by
  classical
  set f : Site d → Site d → ℝ :=
    fun y x => (arrivals ω.2.1 y x (U ω k y) : ℝ) - (U ω k y : ℝ) / (2 * d) with hf
  have hA : ∀ i : Fin d, Summable fun x : Site d => heat d m x * f (x + unit i) x :=
    fun i => summable_heat_mul m _
  have hB : ∀ i : Fin d, Summable fun x : Site d => heat d m x * f (x - unit i) x :=
    fun i => summable_heat_mul m _
  have hA' : ∀ i : Fin d, Summable fun y : Site d => heat d m (y - unit i) * f y (y - unit i) := by
    intro i
    rw [← (Equiv.addRight (unit i)).summable_iff]
    exact (hA i).congr fun x => by simp
  have hB' : ∀ i : Fin d, Summable fun y : Site d => heat d m (y + unit i) * f y (y + unit i) := by
    intro i
    rw [← (Equiv.subRight (unit i)).summable_iff]
    exact (hB i).congr fun x => by simp
  have hpt : ∀ x : Site d, heat d m x * errorTerm ω k x
      = ∑ i : Fin d, (heat d m x * f (x + unit i) x + heat d m x * f (x - unit i) x) := by
    intro x
    show heat d m x * (∑ y ∈ nbrFinset x, f y x) = _
    rw [sum_nbrFinset_eq x (fun y => f y x), Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hstep1 : (∑' x : Site d, heat d m x * errorTerm ω k x)
      = ∑ i : Fin d, ((∑' x : Site d, heat d m x * f (x + unit i) x)
          + ∑' x : Site d, heat d m x * f (x - unit i) x) := by
    rw [tsum_congr hpt, Summable.tsum_finsetSum fun i _ => ((hA i).add (hB i))]
    exact Finset.sum_congr rfl fun i _ => (hA i).tsum_add (hB i)
  have hshift : ∀ i : Fin d, (∑' x : Site d, heat d m x * f (x + unit i) x)
      = ∑' y : Site d, heat d m (y - unit i) * f y (y - unit i) := by
    intro i
    have := (Equiv.addRight (unit i)).tsum_eq
      (fun y : Site d => heat d m (y - unit i) * f y (y - unit i))
    rw [← this]
    exact tsum_congr fun x => by simp
  have hshift' : ∀ i : Fin d, (∑' x : Site d, heat d m x * f (x - unit i) x)
      = ∑' y : Site d, heat d m (y + unit i) * f y (y + unit i) := by
    intro i
    have := (Equiv.subRight (unit i)).tsum_eq
      (fun y : Site d => heat d m (y + unit i) * f y (y + unit i))
    rw [← this]
    exact tsum_congr fun x => by simp
  have hpair : ∀ i : Fin d, (∑' y : Site d, heat d m (y - unit i) * f y (y - unit i))
        + ∑' y : Site d, heat d m (y + unit i) * f y (y + unit i)
      = ∑' y : Site d, (heat d m (y - unit i) * f y (y - unit i)
          + heat d m (y + unit i) * f y (y + unit i)) :=
    fun i => ((hA' i).tsum_add (hB' i)).symm
  rw [hstep1, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
    congrArg₂ (· + ·) (hshift i) (hshift' i),
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hpair i,
    ← Summable.tsum_finsetSum fun i _ => ((hA' i).add (hB' i))]
  refine tsum_congr fun y => ?_
  have hlocal : (∑ i : Fin d, (heat d m (y - unit i) * f y (y - unit i)
        + heat d m (y + unit i) * f y (y + unit i)))
      = ∑ x ∈ nbrFinset y, heat d m x * f y x := by
    rw [sum_nbrFinset_eq y (fun x => heat d m x * f y x)]
    exact Finset.sum_congr rfl fun i _ => add_comm _ _
  rw [hlocal]
  exact sum_nbr_heat_mul_error hd ω hstep m k y

/-! ### The error field as one increment per instruction -/

/-- The error at the origin after `n` rounds, written round by round and then
instruction by instruction. -/
theorem wErr_zero_eq_blocks (hd : 1 ≤ d) (ω : Data d)
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1) (n : ℕ) :
    wErr ω n 0 = ∑ k ∈ Finset.range n, ∑' y : Site d,
      ∑ j ∈ Finset.range (U ω k y),
        (heat d (n - (k + 1)) (ω.2.1 (y, j)) - heat d (n - k) y) := by
  rw [wErr_eq_iterate ω n]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [iterate_walkOp_apply_zero, tsum_heat_mul_errorTerm hd ω hstep]
  refine tsum_congr fun y => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have : n - (k + 1) + 1 = n - k := by omega
  rw [this]

/-! ### Grouping the rounds by the instruction they first read -/

/-- A block sum over the rounds, regrouped by the round in which each index is
first read.  `u` is the odometer at one site, which starts at zero and never
decreases. -/
theorem sum_blocks_regroup (n : ℕ) (u : ℕ → ℕ) (hu : Monotone u) (hu0 : u 0 = 0)
    (F : ℕ → ℕ → ℝ) :
    (∑ k ∈ Finset.range n, ∑ j ∈ Finset.range (u k), F (n - (k + 1)) j)
      = ∑ s ∈ Finset.Icc 1 (n - 1), ∑ j ∈ Finset.Ico (u (s - 1)) (u s),
          ∑ m ∈ Finset.range (n - s), F m j := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  set N := u (n - 1) with hN
  have huN : ∀ k, k ≤ n - 1 → u k ≤ N := fun k hk => hu hk
  have hleft : (∑ k ∈ Finset.range n, ∑ j ∈ Finset.range (u k), F (n - (k + 1)) j)
      = ∑ j ∈ Finset.range N, ∑ k ∈ (Finset.range n).filter (fun k => j < u k),
          F (n - (k + 1)) j := by
    rw [Finset.sum_comm' (t := fun k => Finset.range (u k)) (t' := Finset.range N)
      (s' := fun j => (Finset.range n).filter (fun k => j < u k))]
    intro k j
    simp only [Finset.mem_range, Finset.mem_filter]
    constructor
    · rintro ⟨hk, hj⟩
      have hk1 : k ≤ n - 1 := by omega
      exact ⟨⟨hk, hj⟩, lt_of_lt_of_le hj (huN k hk1)⟩
    · rintro ⟨⟨hk, hj⟩, -⟩
      exact ⟨hk, hj⟩
  have hright : (∑ s ∈ Finset.Icc 1 (n - 1), ∑ j ∈ Finset.Ico (u (s - 1)) (u s),
        ∑ m ∈ Finset.range (n - s), F m j)
      = ∑ j ∈ Finset.range N,
          ∑ s ∈ (Finset.Icc 1 (n - 1)).filter (fun s => u (s - 1) ≤ j ∧ j < u s),
            ∑ m ∈ Finset.range (n - s), F m j := by
    rw [Finset.sum_comm' (t := fun s => Finset.Ico (u (s - 1)) (u s))
      (t' := Finset.range N)
      (s' := fun j => (Finset.Icc 1 (n - 1)).filter
        (fun s => u (s - 1) ≤ j ∧ j < u s))]
    intro s j
    simp only [Finset.mem_range, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨⟨h1, h2⟩, h3, h4⟩, lt_of_lt_of_le h4 (huN s h2)⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, -⟩
      exact ⟨⟨h1, h2⟩, h3, h4⟩
  rw [hleft, hright]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hex : ∃ s, j < u s := ⟨n - 1, hj⟩
  set s₀ := Nat.find hex with hs₀
  have hspec : j < u s₀ := Nat.find_spec hex
  have hmin : ∀ s, s < s₀ → u s ≤ j := by
    intro s hs
    have := Nat.find_min hex hs
    omega
  have hs₀1 : 1 ≤ s₀ := by
    rcases Nat.eq_zero_or_pos s₀ with h | h
    · rw [h, hu0] at hspec; omega
    · exact h
  have hs₀n : s₀ ≤ n - 1 := Nat.find_le hj
  have hiff : ∀ k, j < u k ↔ s₀ ≤ k := by
    intro k
    constructor
    · intro h
      by_contra hc
      exact absurd h (by have := hmin k (by omega); omega)
    · intro h
      exact lt_of_lt_of_le hspec (hu h)
  have hK : (Finset.range n).filter (fun k => j < u k) = Finset.Ico s₀ n := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, hiff k]
    tauto
  have hS : (Finset.Icc 1 (n - 1)).filter (fun s => u (s - 1) ≤ j ∧ j < u s) = {s₀} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      have hge : s₀ ≤ s := (hiff s).mp h4
      have hle : s ≤ s₀ := by
        by_contra hc
        have hs1 : s₀ ≤ s - 1 := by omega
        have : j < u (s - 1) := lt_of_lt_of_le hspec (hu hs1)
        omega
      omega
    · rintro rfl
      refine ⟨⟨hs₀1, hs₀n⟩, ?_, hspec⟩
      exact hmin (s₀ - 1) (by omega)
  rw [hK, hS, Finset.sum_singleton]
  rw [Finset.sum_Ico_eq_sum_range]
  have hidx : ∀ i ∈ Finset.range (n - s₀), F (n - (s₀ + i + 1)) j
      = F (n - s₀ - 1 - i) j := by
    intro i hi
    rw [Finset.mem_range] at hi
    have : n - (s₀ + i + 1) = n - s₀ - 1 - i := by omega
    rw [this]
  rw [Finset.sum_congr rfl hidx]
  exact Finset.sum_range_reflect (fun m => F m j) (n - s₀)

/-! ### Summability of the blocks, and the display of the paper -/

theorem summable_heat_block (ω : Data d)
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1) (m : ℕ) (a : Site d → ℕ) :
    Summable fun y : Site d =>
      ∑ j ∈ Finset.range (a y), (heat d m (ω.2.1 (y, j)) - heat d (m + 1) y) := by
  refine summable_of_ne_finset_zero (s := boxFinset (0 : Site d) (m + 1)) fun y hy => ?_
  have hsup : m + 1 < supNorm y := by
    by_contra hc
    exact hy (mem_boxFinset_zero_iff.mpr (by omega))
  refine Finset.sum_eq_zero fun j _ => ?_
  have h1 : heat d (m + 1) y = 0 := heat_eq_zero_of_notMem_box hy
  have h2 : heat d m (ω.2.1 (y, j)) = 0 := by
    refine heat_eq_zero_of_notMem_box ?_
    intro hmem
    have hle : supNorm y ≤ supNorm (ω.2.1 (y, j)) + 1 :=
      supNorm_le_succ_of_mem_nbrFinset (hstep (y, j))
    have hbox : supNorm (ω.2.1 (y, j)) ≤ m := mem_boxFinset_zero_iff.mp hmem
    omega
  rw [h1, h2, sub_zero]

theorem walkOp_green (M : ℕ) (y : Site d) :
    walkOp (green d M) y = ∑ m ∈ Finset.range M, heat d (m + 1) y := by
  have hg : (green d M) = fun z : Site d => ∑ m ∈ Finset.range M, heat d m z := rfl
  rw [hg, walkOp_sum]
  rfl

theorem green_block (M : ℕ) (z y : Site d) :
    green d M z - walkOp (green d M) y
      = ∑ m ∈ Finset.range M, (heat d m z - heat d (m + 1) y) := by
  rw [walkOp_green, green, ← Finset.sum_sub_distrib]

theorem summable_green_block (ω : Data d)
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1) (M : ℕ) (a b : Site d → ℕ) :
    Summable fun y : Site d =>
      ∑ j ∈ Finset.Ico (a y) (b y),
        (green d M (ω.2.1 (y, j)) - walkOp (green d M) y) := by
  refine summable_of_ne_finset_zero (s := boxFinset (0 : Site d) M) fun y hy => ?_
  have hsup : M < supNorm y := by
    by_contra hc
    exact hy (mem_boxFinset_zero_iff.mpr (by omega))
  have hgy : M < graphNorm y := lt_of_lt_of_le hsup (supNorm_le_graphNorm y)
  refine Finset.sum_eq_zero fun j _ => ?_
  have h1 : walkOp (green d M) y = 0 := by
    rw [walkOp_green]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [Finset.mem_range] at hm
    exact heat_eq_zero_of_lt (by omega)
  have h2 : green d M (ω.2.1 (y, j)) = 0 := by
    refine green_eq_zero_of_le ?_
    have hle : graphNorm y ≤ graphNorm (ω.2.1 (y, j)) + 1 := by
      rw [graphNorm_eq_srw, graphNorm_eq_srw]
      exact LatticeProb.graphNorm_le_of_mem_nbrFinset (hstep (y, j))
    omega
  rw [h1, h2, sub_zero]

/-- **The display of `parking.tex:1145-1152`.**  The error at the origin after
`n` rounds is one increment for each instruction, the increment of an
instruction first read at `y` in round `s` being
`g_{n-s}(ρ_j(y)) - (P g_{n-s})(y)`. -/
theorem wErr_zero_eq (hd : 1 ≤ d) (ω : Data d)
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1) (n : ℕ) :
    wErr ω n 0 = ∑ s ∈ Finset.Icc 1 (n - 1), ∑' y : Site d,
      ∑ j ∈ Finset.Ico (U ω (s - 1) y) (U ω s y),
        (green d (n - s) (ω.2.1 (y, j)) - walkOp (green d (n - s)) y) := by
  classical
  have hblocks := wErr_zero_eq_blocks hd ω hstep n
  have hF : ∀ (k : ℕ), k < n → ∀ (y : Site d) (j : ℕ),
      heat d (n - (k + 1)) (ω.2.1 (y, j)) - heat d (n - k) y
        = heat d (n - (k + 1)) (ω.2.1 (y, j)) - heat d (n - (k + 1) + 1) y := by
    intro k hk y j
    have : n - (k + 1) + 1 = n - k := by omega
    rw [this]
  have hswap1 : (∑ k ∈ Finset.range n, ∑' y : Site d,
        ∑ j ∈ Finset.range (U ω k y),
          (heat d (n - (k + 1)) (ω.2.1 (y, j)) - heat d (n - k) y))
      = ∑' y : Site d, ∑ k ∈ Finset.range n,
        ∑ j ∈ Finset.range (U ω k y),
          (heat d (n - (k + 1)) (ω.2.1 (y, j)) - heat d (n - (k + 1) + 1) y) := by
    have hconv : (∑ k ∈ Finset.range n, ∑' y : Site d,
          ∑ j ∈ Finset.range (U ω k y),
            (heat d (n - (k + 1)) (ω.2.1 (y, j)) - heat d (n - k) y))
        = ∑ k ∈ Finset.range n, ∑' y : Site d,
          ∑ j ∈ Finset.range (U ω k y),
            (heat d (n - (k + 1)) (ω.2.1 (y, j)) - heat d (n - (k + 1) + 1) y) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      exact tsum_congr fun y => Finset.sum_congr rfl fun j _ => hF k hk y j
    rw [hconv, ← Summable.tsum_finsetSum fun k _ => summable_heat_block ω hstep (n - (k + 1))
      (fun y => U ω k y)]
  have hswap2 : (∑ s ∈ Finset.Icc 1 (n - 1), ∑' y : Site d,
        ∑ j ∈ Finset.Ico (U ω (s - 1) y) (U ω s y),
          (green d (n - s) (ω.2.1 (y, j)) - walkOp (green d (n - s)) y))
      = ∑' y : Site d, ∑ s ∈ Finset.Icc 1 (n - 1),
        ∑ j ∈ Finset.Ico (U ω (s - 1) y) (U ω s y),
          (green d (n - s) (ω.2.1 (y, j)) - walkOp (green d (n - s)) y) :=
    (Summable.tsum_finsetSum fun s _ => summable_green_block ω hstep (n - s)
      (fun y => U ω (s - 1) y) (fun y => U ω s y)).symm
  rw [hblocks, hswap1, hswap2]
  refine tsum_congr fun y => ?_
  have hu : Monotone fun k => U ω k y := fun a b h => particleOdometer_mono _ _ h
  have hu0 : (fun k => U ω k y) 0 = 0 := rfl
  have hreg := sum_blocks_regroup n (fun k => U ω k y) hu hu0
    (fun m j => heat d m (ω.2.1 (y, j)) - heat d (m + 1) y)
  rw [hreg]
  refine Finset.sum_congr rfl fun s _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (green_block (n - s) (ω.2.1 (y, j)) y).symm

end Parking

end
