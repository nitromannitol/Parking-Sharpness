/-
Lemma 10.1 of parking.tex, frozen.  `parking.tex:2280-2288` (label
`lem:range-lower`), in the setting of `parking.tex:2272-2279` ("Let $\eta$ be
i.i.d. and integer-valued, with a finite first moment, negative mean,
$\P(\eta(0)>0)>0$, and $\E e^{\theta\eta(0)}<\infty$ for some $\theta>0$.  Fix
$k\geq1$ with $\P(\eta(0)=k)>0$ and condition on $\eta(0)=k$.  Follow particle
$1$ among the $k$ particles at the origin.  Let $X_0=0,X_1,\ldots$ be its
assigned walk and $R_t=\{X_0,\ldots,X_t\}$ its range through time $t$"):

  "For every $k\geq1$ with $\P(\eta(0)=k)>0$ and every $t\geq0$,
   $\P(\tau_1>t\mid\eta(0)=k)\geq\E_0[\P(\eta(0)\geq0)^{|R_t|-1}]$,
   and consequently
   $S_t\geq\E[\eta(0)^+]\,\E_0[\P(\eta(0)\geq0)^{|R_t|-1}]$."

The average `E_0` is over the walk alone, so it is an integral against
`walkLaw`; its finiteness is asserted alongside the bounds, so that an
undefined integral cannot satisfy them through its junk value.  Conditioning on `{η(0)=k}` divides by `ν {k}`, which the
hypothesis keeps away from zero.
-/
import Parking.Support.RangeLower

open MeasureTheory

-- The negative mean, the positive chance of a positive value and the
-- exponential moment are the standing hypotheses under which the paper states
-- the lemma; the bound itself holds for every one-site law, so the proof does
-- not read them.
set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.range_lower (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ)
    (hprob : IsProbabilityMeasure ν) (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k, (k : ℝ) ∂ν < 0) (hpos : 0 < ν (Set.Ioi 0))
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν) :
    (∀ t : ℕ, Integrable (fun p => (ν {j : ℤ | 0 ≤ j}).toReal ^
        (Parking.rangeCard (0 : Parking.Site d) p t - 1)) (Parking.walkLaw d)) ∧
    (∀ (k : ℕ), 1 ≤ k → ν {(k : ℤ)} ≠ 0 → ∀ t : ℕ,
        ∫ p, (ν {j : ℤ | 0 ≤ j}).toReal ^ (Parking.rangeCard (0 : Parking.Site d) p t - 1)
            ∂(Parking.walkLaw d)
          ≤ Parking.survivalGiven d ν k t) ∧
      ∀ t : ℕ, (∫ k, max (k : ℝ) 0 ∂ν) *
          ∫ p, (ν {j : ℤ | 0 ≤ j}).toReal ^ (Parking.rangeCard (0 : Parking.Site d) p t - 1)
            ∂(Parking.walkLaw d)
        ≤ Parking.S (Parking.law d ν) t
-- FROZEN-STATEMENT-END
:= by
  classical
  haveI := hprob
  have hlaw : Parking.law d ν = Parking.dataLaw d (LatticeProb.iidLaw d ν) := rfl
  have hti : Parking.TranslationInvariant (LatticeProb.iidLaw d ν) :=
    fun v => Parking.iidLaw_map_shiftConf' ν v
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI := Parking.stackLaw_isProbability (d := d) hd
  haveI := Parking.rankLaw_isProbability d
  haveI : IsProbabilityMeasure (Parking.law d ν) := by
    unfold Parking.law; infer_instance
  have hmap : (LatticeProb.iidLaw d ν).map (fun η : Parking.Site d → ℤ => η 0) = ν := by
    show (MeasureTheory.Measure.infinitePi fun _ : Parking.Site d => ν).map
      (fun η : Parking.Site d → ℤ => η 0) = ν
    exact Measure.infinitePi_map_eval _ 0
  have hint' : Integrable (fun η : Parking.Site d → ℤ => |((η 0 : ℤ) : ℝ)|)
      (LatticeProb.iidLaw d ν) := by
    refine (integrable_map_measure (g := fun k : ℤ => |(k : ℝ)|)
      (f := fun η : Parking.Site d → ℤ => η 0) (μ := LatticeProb.iidLaw d ν) ?_
      (measurable_pi_apply (0 : Parking.Site d)).aemeasurable).mp ?_
    · rw [hmap]; exact hint.aestronglyMeasurable
    · rw [hmap]; exact hint
  set I : ℕ → ℝ := fun t => ∫ p, (ν {j : ℤ | 0 ≤ j}).toReal ^
    (Parking.rangeCard (0 : Parking.Site d) p t - 1) ∂(Parking.walkLaw d) with hI
  have hInonneg : ∀ t, 0 ≤ I t := fun t =>
    integral_nonneg fun p => pow_nonneg ENNReal.toReal_nonneg _
  -- the joint bound, for every value of the configuration at the origin
  have hjoint : ∀ (m : ℤ), 1 ≤ m → ∀ t : ℕ,
      (ν {m}).toReal * I t
        ≤ ((Parking.law d ν) {ω : Parking.Data d | ω.1 0 = m ∧
            (LatticeProb.state (Parking.toDriver ω) t).active (0, 0) = true}).toReal := by
    intro m hm t
    have hle := Parking.measure_conf_active_ge hd ν m hm t
    have hfin : (Parking.law d ν) {ω : Parking.Data d | ω.1 0 = m ∧
        (LatticeProb.state (Parking.toDriver ω) t).active (0, 0) = true} ≠ ⊤ :=
      measure_ne_top _ _
    have := ENNReal.toReal_mono hfin hle
    rwa [ENNReal.toReal_mul, Parking.lintegral_rangePow_toReal ν t] at this
  refine ⟨fun t => Parking.integrable_rangePow hd ν t, fun k hk hνk t => ?_, fun t => ?_⟩
  · have hm : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    have hpos : 0 < (ν {(k : ℤ)}).toReal :=
      ENNReal.toReal_pos hνk (measure_ne_top ν _)
    rw [Parking.survivalGiven, le_div_iff₀ hpos, mul_comm]
    exact hjoint (k : ℤ) hm t
  · obtain ⟨hsum, hSeq⟩ := Parking.S_expansion hd (LatticeProb.iidLaw d ν) t
      (Parking.integrable_survivorsFrom_data hd hti hint' t 0)
    set f : ℕ → ℝ := fun m => ((m : ℝ) + 1) *
      ((Parking.dataLaw d (LatticeProb.iidLaw d ν)) {ω : Parking.Data d |
        ω.1 0 = (m : ℤ) + 1 ∧
        (LatticeProb.state (Parking.toDriver ω) t).active (0, 0) = true}).toReal with hf
    set g : ℕ → ℝ := fun m => ((m : ℝ) + 1) * (ν {(m : ℤ) + 1}).toReal * I t with hg
    have hgle : ∀ m, g m ≤ f m := by
      intro m
      have hm : (1 : ℤ) ≤ (m : ℤ) + 1 := by omega
      have h1 := hjoint ((m : ℤ) + 1) hm t
      have h2 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
      calc g m = ((m : ℝ) + 1) * ((ν {(m : ℤ) + 1}).toReal * I t) := by rw [hg]; ring
        _ ≤ ((m : ℝ) + 1) * ((Parking.law d ν) {ω : Parking.Data d |
              ω.1 0 = (m : ℤ) + 1 ∧
              (LatticeProb.state (Parking.toDriver ω) t).active (0, 0) = true}).toReal :=
            mul_le_mul_of_nonneg_left h1 h2
        _ = f m := rfl
    have hgnn : ∀ m, 0 ≤ g m := by
      intro m
      rw [hg]
      have : (0 : ℝ) ≤ ((m : ℝ) + 1) * (ν {(m : ℤ) + 1}).toReal := by positivity
      exact mul_nonneg this (hInonneg t)
    have hgsum : Summable g := Summable.of_nonneg_of_le hgnn hgle hsum
    have hchain : (∫ k, max (k : ℝ) 0 ∂ν) * I t ≤ ∑' m : ℕ, f m := by
      calc (∫ k, max (k : ℝ) 0 ∂ν) * I t
          = (∑' m : ℕ, ((m : ℝ) + 1) * (ν {(m : ℤ) + 1}).toReal) * I t := by
            rw [Parking.integral_posPart_eq_tsum ν hint]
        _ = ∑' m : ℕ, g m := (tsum_mul_right).symm
        _ ≤ ∑' m : ℕ, f m := hgsum.tsum_le_tsum hgle hsum
    rw [hlaw, hSeq]
    exact hchain
