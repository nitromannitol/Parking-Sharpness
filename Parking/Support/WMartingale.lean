/-
The pieces of `lem:w-martingale` that do not need the exposure filtration:
the increment bound of the lemma, and the count that collapses its quadratic
variation.

`greenIncrement d n` is the paper's
`max_{m<n} max_y max_{z ∼ y} |g_m(z) - (P g_m)(y)|`, and it is a genuine
supremum rather than a junk value because `g_m` takes values in `[0, m]`, so
the whole family is bounded by `2n`.  The count is
`U_s(y) - U_{s-1}(y) = A_{s-1}(y)`: the departures from `y` in round `s` are
the particles standing there after round `s-1`.

Also here: the block decomposition of the error at the origin with BOTH sums
finite.  The increment of round `s` at a site outside the box of radius `n-s`
vanishes, because the truncated Green function vanishes there and at every
neighbour, so the lattice sum of `parking.tex:1145-1152` is a sum over that
box; `blockPairs ω n s` collects the instructions first read in round `s` at
those sites, a finite set for every realization, and distinct rounds read
distinct instructions.

The block of round `s` is decided before its own instructions are read, which
is the predictability the martingale of `lem:w-martingale` needs.  It has two
halves.  `U_{t+1}` is a function of the configuration and of the state after
round `t`, so overwriting an instruction the odometer has not reached by round
`t` changes no block up to round `t+1`; and the state near a site after `t`
rounds reads only the instructions within `2t²` of it, so overwriting an
instruction further out than that changes no block inside the box either.
-/
import Parking.Support.ErrorUnroll
import Parking.Support.Reads

noncomputable section

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-! ### The truncated Green function takes values in `[0, m]` -/

theorem heat_nonneg (m : ℕ) (x : Site d) : 0 ≤ heat d m x := by
  rw [heat_eq_srwHeat]; exact LatticeProb.srwHeat_nonneg m x

theorem heat_le_one (hd : 1 ≤ d) (m : ℕ) (x : Site d) : heat d m x ≤ 1 := by
  rw [heat_eq_srwHeat]; exact LatticeProb.srwHeat_le_one (by omega) m x

theorem green_nonneg (m : ℕ) (x : Site d) : 0 ≤ green d m x :=
  Finset.sum_nonneg fun j _ => heat_nonneg j x

theorem green_le (hd : 1 ≤ d) (m : ℕ) (x : Site d) : green d m x ≤ m := by
  have h := Finset.sum_le_sum (f := fun j => heat d j x) (g := fun _ : ℕ => (1 : ℝ))
    (s := Finset.range m) fun j _ => heat_le_one hd j x
  rw [green]
  simpa using h

theorem walkOp_green_nonneg (m : ℕ) (y : Site d) : 0 ≤ walkOp (green d m) y := by
  rw [walkOp_green]
  exact Finset.sum_nonneg fun j _ => heat_nonneg (j + 1) y

theorem walkOp_green_le (hd : 1 ≤ d) (m : ℕ) (y : Site d) :
    walkOp (green d m) y ≤ m := by
  rw [walkOp_green]
  have h := Finset.sum_le_sum (f := fun j => heat d (j + 1) y) (g := fun _ : ℕ => (1 : ℝ))
    (s := Finset.range m) fun j _ => heat_le_one hd (j + 1) y
  simpa using h

/-- The increments of `lem:w-martingale` are bounded by twice the horizon. -/
theorem abs_greenDiff_le (hd : 1 ≤ d) (m : ℕ) (y z : Site d) :
    |green d m z - walkOp (green d m) y| ≤ 2 * m := by
  rw [abs_le]
  constructor
  · have h1 := green_nonneg (d := d) m z
    have h2 := walkOp_green_le hd m y
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  · have h1 := green_le hd m z
    have h2 := walkOp_green_nonneg (d := d) m y
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith

/-! ### The supremum defining `greenIncrement` is attained above every term -/

/-- Every term of the paper's `max_{m<n} max_y max_{z ∼ y}` is below the
supremum that defines `greenIncrement`, which is a real supremum because the
whole family is bounded by twice the horizon. -/
theorem le_greenIncrement (hd : 1 ≤ d) {n m : ℕ} (hm : m < n) {y z : Site d}
    (hz : z ∈ nbrFinset y) :
    |green d m z - walkOp (green d m) y| ≤ greenIncrement d n := by
  set F3 : ℕ → Site d → Site d → ℝ :=
    fun m y z => ⨆ _ : z ∈ nbrFinset y, |green d m z - walkOp (green d m) y| with hF3def
  set F2 : ℕ → Site d → ℝ := fun m y => ⨆ z : Site d, F3 m y z with hF2def
  have hF3 : ∀ (m' : ℕ) (y' z' : Site d), F3 m' y' z' ≤ 2 * m' := by
    intro m' y' z'
    by_cases h : z' ∈ nbrFinset y'
    · rw [hF3def]
      simp only
      rw [ciSup_pos h]
      exact abs_greenDiff_le hd m' y' z'
    · rw [hF3def]
      simp only
      rw [ciSup_neg h, Real.sSup_empty]
      positivity
  have hb3 : ∀ (m' : ℕ) (y' : Site d), BddAbove (Set.range fun z' : Site d => F3 m' y' z') := by
    intro m' y'
    exact ⟨2 * m', by rintro x ⟨z', rfl⟩; exact hF3 m' y' z'⟩
  have hF2 : ∀ (m' : ℕ) (y' : Site d), F2 m' y' ≤ 2 * m' :=
    fun m' y' => ciSup_le fun z' => hF3 m' y' z'
  have hb2 : ∀ m' : ℕ, BddAbove (Set.range fun y' : Site d => F2 m' y') := by
    intro m'
    exact ⟨2 * m', by rintro x ⟨y', rfl⟩; exact hF2 m' y'⟩
  set F1 : ℕ → ℝ := fun m' => ⨆ _ : m' ∈ Set.Iio n, ⨆ y' : Site d, F2 m' y' with hF1def
  have hF1 : ∀ m' : ℕ, F1 m' ≤ 2 * n := by
    intro m'
    by_cases h : m' ∈ Set.Iio n
    · rw [hF1def]
      simp only
      rw [ciSup_pos h]
      refine ciSup_le fun y' => le_trans (hF2 m' y') ?_
      have : (m' : ℝ) ≤ n := by exact_mod_cast le_of_lt h
      linarith
    · rw [hF1def]
      simp only
      rw [ciSup_neg h, Real.sSup_empty]
      positivity
  have hb1 : BddAbove (Set.range F1) := ⟨2 * n, by rintro x ⟨m', rfl⟩; exact hF1 m'⟩
  have hstep1 : |green d m z - walkOp (green d m) y| ≤ F2 m y := by
    have h1 : F3 m y z = |green d m z - walkOp (green d m) y| := by
      rw [hF3def]; simp only; rw [ciSup_pos hz]
    rw [← h1]
    exact le_ciSup (hb3 m y) z
  have hstep2 : F2 m y ≤ ⨆ y' : Site d, F2 m y' := le_ciSup (hb2 m) y
  have hstep3 : (⨆ y' : Site d, F2 m y') = F1 m := by
    rw [hF1def]; simp only; rw [ciSup_pos (Set.mem_Iio.mpr hm)]
  have hstep4 : F1 m ≤ greenIncrement d n := le_ciSup hb1 m
  calc |green d m z - walkOp (green d m) y| ≤ F2 m y := hstep1
    _ ≤ ⨆ y' : Site d, F2 m y' := hstep2
    _ = F1 m := hstep3
    _ ≤ greenIncrement d n := hstep4

/-! ### The departures of a round are the particles standing there -/

theorem U_succ (ω : Data d) (t : ℕ) (x : Site d) :
    U ω (t + 1) x = U ω t x + A ω t x :=
  LatticeProb.particleOdometer_succ (toDriver ω) t x




/-- The block of round `s` is supported in the box of radius `n - s`: an
instruction read at a site further out contributes nothing, because the
truncated Green function vanishes there and at every neighbour. -/
theorem green_block_eq_zero_of_far (ω : Data d)
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1) (M : ℕ) {y : Site d}
    (hy : y ∉ boxFinset (0 : Site d) M) (j : ℕ) :
    green d M (ω.2.1 (y, j)) - walkOp (green d M) y = 0 := by
  have hsup : M < supNorm y := by
    by_contra hc
    exact hy (mem_boxFinset_zero_iff.mpr (by omega))
  have hgy : M < graphNorm y := lt_of_lt_of_le hsup (supNorm_le_graphNorm y)
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

/-- The lattice sum of one block is a finite sum over the box of radius `n - s`. -/
theorem tsum_green_block_eq_sum (ω : Data d)
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1) (M : ℕ) (a b : Site d → ℕ) :
    ∑' y : Site d, ∑ j ∈ Finset.Ico (a y) (b y),
        (green d M (ω.2.1 (y, j)) - walkOp (green d M) y)
      = ∑ y ∈ boxFinset (0 : Site d) M, ∑ j ∈ Finset.Ico (a y) (b y),
          (green d M (ω.2.1 (y, j)) - walkOp (green d M) y) :=
  tsum_eq_sum fun _ hy =>
    Finset.sum_eq_zero fun j _ => green_block_eq_zero_of_far ω hstep M hy j

/-- **The error at the origin is a finite sum of per-instruction increments.**
`parking.tex:1145-1152` with both sums finite: the rounds run over
`Icc 1 (n-1)`, the sites over the box of radius `n - s`, and the instruction
indices over those first read in round `s`. -/
theorem wErr_zero_eq_finite (hd : 1 ≤ d) (ω : Data d)
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1) (n : ℕ) :
    wErr ω n 0 = ∑ s ∈ Finset.Icc 1 (n - 1), ∑ y ∈ boxFinset (0 : Site d) (n - s),
      ∑ j ∈ Finset.Ico (U ω (s - 1) y) (U ω s y),
        (green d (n - s) (ω.2.1 (y, j)) - walkOp (green d (n - s)) y) := by
  rw [wErr_zero_eq hd ω hstep n]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact tsum_green_block_eq_sum ω hstep (n - s) (fun y => U ω (s - 1) y) (fun y => U ω s y)

/-- The instructions first read in round `s`, at the sites the increment of
that round can see.  This is the block the martingale of `lem:w-martingale`
reveals in one piece; it is finite for every realization, which is what makes
the round-by-round order an enumeration of the pairs. -/
def blockAt (ω : Data d) (R s : ℕ) : Finset (Site d × ℕ) :=
  (boxFinset (0 : Site d) R).biUnion fun y =>
    (Finset.Ico (U ω (s - 1) y) (U ω s y)).image fun j => (y, j)

/-- The block of round `s` at the radius the increment of that round can see. -/
def blockPairs (ω : Data d) (n s : ℕ) : Finset (Site d × ℕ) := blockAt ω (n - s) s

theorem mem_blockAt {ω : Data d} {R s : ℕ} {q : Site d × ℕ} :
    q ∈ blockAt ω R s ↔
      q.1 ∈ boxFinset (0 : Site d) R ∧ U ω (s - 1) q.1 ≤ q.2 ∧ q.2 < U ω s q.1 := by
  classical
  simp only [blockAt, Finset.mem_biUnion, Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨y, hy, j, hj, rfl⟩
    exact ⟨hy, hj.1, hj.2⟩
  · rintro ⟨hy, h1, h2⟩
    exact ⟨q.1, hy, q.2, ⟨h1, h2⟩, rfl⟩

theorem mem_blockPairs {ω : Data d} {n s : ℕ} {q : Site d × ℕ} :
    q ∈ blockPairs ω n s ↔
      q.1 ∈ boxFinset (0 : Site d) (n - s) ∧ U ω (s - 1) q.1 ≤ q.2 ∧ q.2 < U ω s q.1 :=
  mem_blockAt

theorem sum_blockPairs (ω : Data d) (n s : ℕ) (f : Site d × ℕ → ℝ) :
    ∑ q ∈ blockPairs ω n s, f q
      = ∑ y ∈ boxFinset (0 : Site d) (n - s),
          ∑ j ∈ Finset.Ico (U ω (s - 1) y) (U ω s y), f (y, j) := by
  classical
  rw [blockPairs, blockAt, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun y _ => ?_
    refine Finset.sum_image ?_
    intro a _ b _ h
    exact (Prod.mk.injEq _ _ _ _ ▸ h).2
  · intro y _ y' _ hyy'
    refine Finset.disjoint_left.mpr fun q hq hq' => ?_
    rw [Finset.mem_image] at hq hq'
    obtain ⟨j, _, rfl⟩ := hq
    obtain ⟨j', _, h⟩ := hq'
    exact hyy' (congrArg Prod.fst h).symm

/-- **The error at the origin is a finite sum over the blocks.** -/
theorem wErr_zero_eq_blockPairs (hd : 1 ≤ d) (ω : Data d)
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1) (n : ℕ) :
    wErr ω n 0 = ∑ s ∈ Finset.Icc 1 (n - 1), ∑ q ∈ blockPairs ω n s,
      (green d (n - s) (ω.2.1 q) - walkOp (green d (n - s)) q.1) := by
  rw [wErr_zero_eq_finite hd ω hstep n]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact (sum_blockPairs ω n s
    (fun q => green d (n - s) (ω.2.1 q) - walkOp (green d (n - s)) q.1)).symm

/-- Distinct rounds read distinct instructions: the blocks are pairwise
disjoint, which is the freshness the exploration of `lem:w-martingale` needs. -/
theorem blockAt_disjoint (ω : Data d) (R R' : ℕ) {s s' : ℕ} (hs : 1 ≤ s) (hs' : 1 ≤ s')
    (h : s ≠ s') : Disjoint (blockAt ω R s) (blockAt ω R' s') := by
  classical
  refine Finset.disjoint_left.mpr fun q hq hq' => ?_
  rw [mem_blockAt] at hq hq'
  obtain ⟨-, h1, h2⟩ := hq
  obtain ⟨-, h1', h2'⟩ := hq'
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have : U ω s q.1 ≤ U ω (s' - 1) q.1 :=
      particleOdometer_mono (toDriver ω) q.1 (by omega)
    omega
  · have : U ω s' q.1 ≤ U ω (s - 1) q.1 :=
      particleOdometer_mono (toDriver ω) q.1 (by omega)
    omega

theorem blockPairs_disjoint (ω : Data d) (n : ℕ) {s s' : ℕ} (hs : 1 ≤ s) (hs' : 1 ≤ s')
    (h : s ≠ s') : Disjoint (blockPairs ω n s) (blockPairs ω n s') :=
  blockAt_disjoint ω (n - s) (n - s') hs hs' h



/-! ### The odometer of a round is decided by the state of the round before -/

/-- `U_{t+1}` is a function of the configuration and of the state after round
`t`: the departures of round `t+1` are the particles standing there.  This is
what makes the block of round `t+1` predictable. -/
theorem U_succ_of_state_eq {D D' : Driver d} (heta : D.eta = D'.eta) (t : ℕ)
    (h : state D t = state D' t) (y : Site d) :
    particleOdometer D (t + 1) y = particleOdometer D' (t + 1) y := by
  rw [particleOdometer_succ, particleOdometer_succ]
  show (state D t).departures y + (activeAt D (state D t) t y).card
    = (state D' t).departures y + (activeAt D' (state D' t) t y).card
  rw [h]
  congr 2
  show (candidates D.eta y t).filter _ = (candidates D'.eta y t).filter _
  rw [heta]

/-- Overwriting an instruction the odometer has not reached by round `t` leaves
the state after round `t` unchanged. -/
theorem state_congr_of_le_odometer {D D' : Driver d} (hs : StepsToNeighbour D)
    (heta : D.eta = D'.eta) (hrank : D.rank = D'.rank) (c : Site d × ℕ)
    (hstack : ∀ q : Site d × ℕ, q ≠ c → D.stack q = D'.stack q) (t : ℕ)
    (hun : particleOdometer D t c.1 ≤ c.2) :
    state D t = state D' t := by
  refine state_congr hs heta hrank t fun z i hi => ?_
  by_cases hc : (z, i) = c
  · exfalso
    obtain rfl : z = c.1 := congrArg Prod.fst hc
    obtain rfl : i = c.2 := congrArg Prod.snd hc
    omega
  · exact hstack _ hc

/-- **The block of round `t+1` is decided before its instructions are read.**
Overwriting an instruction that the odometer has not reached by round `t`
changes neither `U_t` nor `U_{t+1}`, hence neither the block of round `t+1`. -/
theorem blockAt_congr_of_le_odometer {ω ω' : Data d}
    (hs : StepsToNeighbour (toDriver ω)) (heta : ω.1 = ω'.1) (hrank : ω.2.2 = ω'.2.2)
    (c : Site d × ℕ) (hstack : ∀ q : Site d × ℕ, q ≠ c → ω.2.1 q = ω'.2.1 q)
    (R t : ℕ) (hun : U ω t c.1 ≤ c.2) :
    blockAt ω R (t + 1) = blockAt ω' R (t + 1) := by
  classical
  have hstate : LatticeProb.state (toDriver ω) t = LatticeProb.state (toDriver ω') t :=
    state_congr_of_le_odometer (D := toDriver ω) (D' := toDriver ω') hs heta hrank c hstack t hun
  have hU : ∀ y : Site d, U ω t y = U ω' t y := fun y => by
    show (LatticeProb.state (toDriver ω) t).departures y
      = (LatticeProb.state (toDriver ω') t).departures y
    rw [hstate]
  have hUsucc : ∀ y : Site d, U ω (t + 1) y = U ω' (t + 1) y := fun y =>
    U_succ_of_state_eq heta t hstate y
  ext q
  rw [mem_blockAt, mem_blockAt]
  simp only [Nat.add_sub_cancel, hU, hUsucc]



/-! ### The odometer of a round is decided far from the site -/

/-- Overwriting an instruction at a site further than `2t²` from `y` leaves the
odometer at `y` after `t` rounds unchanged.  This is the spatial half of the
predictability of the blocks; the index half is
`state_congr_of_le_odometer`. -/
theorem U_congr_of_far {ω ω' : Data d} (hs : StepsToNeighbour (toDriver ω))
    (heta : ω.1 = ω'.1) (hrank : ω.2.2 = ω'.2.2) (c : Site d × ℕ)
    (hstack : ∀ q : Site d × ℕ, q ≠ c → ω.2.1 q = ω'.2.1 q)
    (t : ℕ) (y : Site d) (hfar : c.1 ∉ boxFinset y (2 * t * t)) :
    U ω t y = U ω' t y := by
  have hA : AgreeOn (toDriver ω) (toDriver ω') y (0 + 2 * t * t) := by
    refine ⟨fun z _ => congrFun heta z, fun z hz i => ?_, fun p _ s => congrFun hrank (p, s)⟩
    refine hstack (z, i) fun hc => ?_
    exact hfar (by rw [← congrArg Prod.fst hc]; simpa using hz)
  have hSt := state_agree_box (D := toDriver ω) (D' := toDriver ω') hs y t 0 hA
  show (LatticeProb.state (toDriver ω) t).departures y
    = (LatticeProb.state (toDriver ω') t).departures y
  exact hSt.departures y (mem_boxFinset_iff.mpr (by simp))

/-- **The block of round `t+1` inside a box is decided by what lies near it.**
Overwriting an instruction at a site further than `R + 2(t+1)²` from the origin
leaves that block unchanged. -/
theorem blockAt_congr_of_far {ω ω' : Data d} (hs : StepsToNeighbour (toDriver ω))
    (heta : ω.1 = ω'.1) (hrank : ω.2.2 = ω'.2.2) (c : Site d × ℕ)
    (hstack : ∀ q : Site d × ℕ, q ≠ c → ω.2.1 q = ω'.2.1 q) (R t : ℕ)
    (hfar : c.1 ∉ boxFinset (0 : Site d) (R + 2 * (t + 1) * (t + 1))) :
    blockAt ω R (t + 1) = blockAt ω' R (t + 1) := by
  classical
  have hnear : ∀ y ∈ boxFinset (0 : Site d) R, ∀ u ≤ t + 1,
      c.1 ∉ boxFinset y (2 * u * u) := by
    intro y hy u hu hc
    refine hfar ?_
    refine mem_boxFinset_iff.mpr fun i => ?_
    have h1 := mem_boxFinset_iff.mp hc i
    have h2 := mem_boxFinset_iff.mp hy i
    simp only [Pi.zero_apply, sub_zero] at h2 ⊢
    have habs : |c.1 i| ≤ |c.1 i - y i| + |y i| := by
      rcases abs_cases (c.1 i) with h | h <;> rcases abs_cases (c.1 i - y i) with h' | h' <;>
        rcases abs_cases (y i) with h'' | h'' <;> omega
    have h4 : 2 * u * u ≤ 2 * (t + 1) * (t + 1) := by nlinarith
    have h4' : ((2 * u * u : ℕ) : ℤ) ≤ ((2 * (t + 1) * (t + 1) : ℕ) : ℤ) := by
      exact_mod_cast h4
    have hsum := add_le_add h1 h2
    push_cast at hsum h4' ⊢
    linarith [habs]
  ext q
  rw [mem_blockAt, mem_blockAt]
  simp only [Nat.add_sub_cancel]
  constructor
  · rintro ⟨hy, h1, h2⟩
    refine ⟨hy, ?_, ?_⟩
    · rwa [← U_congr_of_far hs heta hrank c hstack t q.1 (hnear q.1 hy t (by omega))]
    · rwa [← U_congr_of_far hs heta hrank c hstack (t + 1) q.1 (hnear q.1 hy (t + 1) le_rfl)]
  · rintro ⟨hy, h1, h2⟩
    refine ⟨hy, ?_, ?_⟩
    · rwa [U_congr_of_far hs heta hrank c hstack t q.1 (hnear q.1 hy t (by omega))]
    · rwa [U_congr_of_far hs heta hrank c hstack (t + 1) q.1 (hnear q.1 hy (t + 1) le_rfl)]



/-! ### The radii the exploration needs -/

/-- The radius of the box the block of round `s` is read in.  It decreases in
`s` by more than the `2s²` an extra round of the process can reach, so that the
instructions the odometer of round `s` reads inside its own box were all read
inside the boxes of the earlier rounds. -/
def blockRad (n s : ℕ) : ℕ := (n - s) * (2 * n * n) + n

theorem le_blockRad (n s : ℕ) : n - s ≤ blockRad n s := by
  have h : n - s ≤ n := Nat.sub_le n s
  simp only [blockRad]
  omega

theorem blockRad_step {n s : ℕ} (hs : 1 ≤ s) (hsn : s ≤ n) :
    blockRad n s + 2 * s * s ≤ blockRad n (s - 1) := by
  have hsub : n - (s - 1) = (n - s) + 1 := by omega
  have h2 : 2 * s * s ≤ 2 * n * n := by nlinarith
  simp only [blockRad, hsub]
  nlinarith

theorem blockRad_antitone {n s s' : ℕ} (h : s ≤ s') : blockRad n s' ≤ blockRad n s := by
  have : n - s' ≤ n - s := Nat.sub_le_sub_left h n
  simp only [blockRad]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ this) n

/-! ### Enlarging the box of a block costs nothing -/

theorem blockPairs_subset_blockAt (ω : Data d) (n s R : ℕ) (h : n - s ≤ R) :
    blockPairs ω n s ⊆ blockAt ω R s := by
  intro q hq
  rw [mem_blockPairs] at hq
  rw [mem_blockAt]
  exact ⟨boxFinset_mono h hq.1, hq.2.1, hq.2.2⟩

/-- The increment of round `s` reads nothing new when its box is enlarged. -/
theorem sum_blockAt_eq (ω : Data d)
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1) (n s R : ℕ) (h : n - s ≤ R) :
    ∑ q ∈ blockAt ω R s, (green d (n - s) (ω.2.1 q) - walkOp (green d (n - s)) q.1)
      = ∑ q ∈ blockPairs ω n s,
          (green d (n - s) (ω.2.1 q) - walkOp (green d (n - s)) q.1) := by
  refine (Finset.sum_subset (blockPairs_subset_blockAt ω n s R h) ?_).symm
  intro q _ hq
  refine green_block_eq_zero_of_far ω hstep (n - s) ?_ q.2
  intro hbox
  exact hq (mem_blockPairs.mpr ⟨hbox, (mem_blockAt.mp ‹q ∈ blockAt ω R s›).2.1,
    (mem_blockAt.mp ‹q ∈ blockAt ω R s›).2.2⟩)

/-- **The error at the origin, read in the boxes the exploration uses.** -/
theorem wErr_zero_eq_blockRad (hd : 1 ≤ d) (ω : Data d)
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1) (n : ℕ) :
    wErr ω n 0 = ∑ s ∈ Finset.Icc 1 (n - 1), ∑ q ∈ blockAt ω (blockRad n s) s,
      (green d (n - s) (ω.2.1 q) - walkOp (green d (n - s)) q.1) := by
  rw [wErr_zero_eq_blockPairs hd ω hstep n]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact (sum_blockAt_eq ω hstep n s (blockRad n s) (le_blockRad n s)).symm

/-! ### The list the exploration reads -/

/-- The instructions of round `s`, listed. -/
def blockList (ω : Data d) (n s : ℕ) : List (Site d × ℕ) :=
  (blockAt ω (blockRad n s) s).toList

/-- The instructions of the rounds `1` to `k`, listed round by round.  This is
the order in which `lem:w-martingale` reveals them. -/
def blockPrefix (ω : Data d) (n k : ℕ) : List (Site d × ℕ) :=
  (List.range' 1 k).flatMap fun s => blockList ω n s

theorem mem_blockList {ω : Data d} {n s : ℕ} {q : Site d × ℕ} :
    q ∈ blockList ω n s ↔ q ∈ blockAt ω (blockRad n s) s := by
  simp [blockList]

theorem nodup_blockPrefix (ω : Data d) (n k : ℕ) : (blockPrefix ω n k).Nodup := by
  classical
  refine List.nodup_flatMap.mpr ⟨fun s _ => Finset.nodup_toList _, ?_⟩
  refine List.Pairwise.imp_of_mem ?_ (List.nodup_range' (s := 1) (n := k))
  intro s s' hs hs' hne
  have h1 : 1 ≤ s := by
    obtain ⟨i, -, rfl⟩ := List.mem_range'.mp hs
    omega
  have h1' : 1 ≤ s' := by
    obtain ⟨i, -, rfl⟩ := List.mem_range'.mp hs'
    omega
  refine List.disjoint_left.mpr fun q hq hq' => ?_
  have := blockAt_disjoint ω (blockRad n s) (blockRad n s') h1 h1' hne
  exact (Finset.disjoint_left.mp this) (mem_blockList.mp hq) (mem_blockList.mp hq')





theorem mem_blockPrefix {ω : Data d} {n k : ℕ} {q : Site d × ℕ} :
    q ∈ blockPrefix ω n k ↔ ∃ s, 1 ≤ s ∧ s ≤ k ∧ q ∈ blockAt ω (blockRad n s) s := by
  classical
  simp only [blockPrefix, List.mem_flatMap, mem_blockList]
  constructor
  · rintro ⟨s, hs, hq⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hs
    exact ⟨1 + 1 * i, by omega, by omega, hq⟩
  · rintro ⟨s, h1, h2, hq⟩
    exact ⟨s, List.mem_range'.mpr ⟨s - 1, by omega, by omega⟩, hq⟩

theorem blockPrefix_congr {ω ω' : Data d} {n k : ℕ}
    (h : ∀ s, 1 ≤ s → s ≤ k → blockAt ω (blockRad n s) s = blockAt ω' (blockRad n s) s) :
    blockPrefix ω n k = blockPrefix ω' n k := by
  classical
  refine List.flatMap_congr fun s hs => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hs
  show blockList ω n (1 + 1 * i) = blockList ω' n (1 + 1 * i)
  rw [blockList, blockList, h (1 + 1 * i) (by omega) (by omega)]

theorem blockPrefix_append (ω : Data d) (n : ℕ) {k m : ℕ} (h : k ≤ m) :
    blockPrefix ω n m
      = blockPrefix ω n k ++ (List.range' (1 + k) (m - k)).flatMap (fun s => blockList ω n s) := by
  classical
  rw [blockPrefix, blockPrefix, ← List.flatMap_append]
  congr 1
  have h1 : List.range' 1 k ++ List.range' (1 + 1 * k) (m - k) = List.range' 1 (k + (m - k)) :=
    List.range'_append
  have h2 : k + (m - k) = m := by omega
  rw [h2] at h1
  rw [← h1]
  congr 2
  omega

theorem length_blockPrefix_mono (ω : Data d) (n : ℕ) {k m : ℕ} (h : k ≤ m) :
    (blockPrefix ω n k).length ≤ (blockPrefix ω n m).length := by
  rw [blockPrefix_append ω n h, List.length_append]
  omega

/-- **The blocks up to round `k` are decided by the instructions of the blocks
before them.**  If the overwritten instruction is in none of the rounds before
`k`, then every block up to round `k` is unchanged: either the odometer has not
reached it by the round in question, or the round in which it is read leaves it
outside the box that round is read in, and the boxes shrink by more than one
round of reach. -/
theorem blockAt_agree_of_notMem {ω ω' : Data d} (hs : StepsToNeighbour (toDriver ω))
    (heta : ω.1 = ω'.1) (hrank : ω.2.2 = ω'.2.2) (c : Site d × ℕ)
    (hstack : ∀ q : Site d × ℕ, q ≠ c → ω.2.1 q = ω'.2.1 q) (n k : ℕ) (hkn : k ≤ n)
    (hnot : ∀ s, 1 ≤ s → s < k → c ∉ blockAt ω (blockRad n s) s) :
    ∀ s, 1 ≤ s → s ≤ k → blockAt ω (blockRad n s) s = blockAt ω' (blockRad n s) s := by
  classical
  intro s h1s hsk
  by_cases hun : U ω (s - 1) c.1 ≤ c.2
  · have := blockAt_congr_of_le_odometer hs heta hrank c hstack (blockRad n s) (s - 1) hun
    rwa [Nat.sub_add_cancel h1s] at this
  · have hun' : c.2 < U ω (s - 1) c.1 := Nat.lt_of_not_le hun
    have hex : ∃ r, c.2 < U ω r c.1 := ⟨s - 1, hun'⟩
    set r := Nat.find hex with hr
    have hrspec : c.2 < U ω r c.1 := Nat.find_spec hex
    have hrle : r ≤ s - 1 := Nat.find_min' hex hun'
    have hr1 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · exfalso
        have : U ω 0 c.1 = 0 := rfl
        rw [h, this] at hrspec
        omega
      · exact h
    have hprev : U ω (r - 1) c.1 ≤ c.2 := by
      by_contra hc
      exact Nat.find_min hex (m := r - 1) (by omega) (Nat.lt_of_not_le hc)
    have hnotr := hnot r hr1 (by omega)
    have hbox : c.1 ∉ boxFinset (0 : Site d) (blockRad n r) := by
      intro hc
      exact hnotr (mem_blockAt.mpr ⟨hc, hprev, hrspec⟩)
    have hfar : c.1 ∉ boxFinset (0 : Site d) (blockRad n s + 2 * s * s) := by
      intro hc
      refine hbox (boxFinset_mono ?_ hc)
      calc blockRad n s + 2 * s * s ≤ blockRad n (s - 1) := blockRad_step h1s (by omega)
        _ ≤ blockRad n r := blockRad_antitone hrle
    have := blockAt_congr_of_far hs heta hrank c hstack (blockRad n s) (s - 1) ?_
    · rwa [Nat.sub_add_cancel h1s] at this
    · rwa [Nat.sub_add_cancel h1s]

end Parking

end
