"""Compare how much each paper statement asserts with how much its Lean node does.

Every other checker here compares a statement with *itself*: the hash pins the
bytes, the axiom check pins the proof.  None of them notices when a frozen
statement quietly asserts less than the paper statement it claims to transcribe.
That is how, in the ORRW formalization this tooling comes from, `lem:schur`
came to be frozen without one of the three displays its paper statement
asserts, while every other gate passed.

This counts assertion units on each side and reports the pairs where the paper
asserts more:

  paper   displayed equations and enumerated items inside the statement
  Lean    top-level conjuncts of the frozen statement's conclusion

The counts are a heuristic, not a proof of correspondence: one Lean conjunct can
faithfully carry two paper displays, and one paper display can need three Lean
conjuncts.  So a mismatch is a prompt to look, not a verdict, and every node is
listed with its counts so the reader can judge.  Nodes whose `source` names no
paper label are skipped: they have no paper statement to compare against.

    python3 tools/check_clauses.py            # report
    python3 tools/check_clauses.py --strict   # exit 1 if any node is unreviewed
"""

from __future__ import annotations

import os
import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    sys.exit("check_clauses.py: PyYAML is required (pip install pyyaml)")

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "ledger" / "manifest.yaml"

# Nodes whose count mismatch has been looked at and explained.  The value is the
# reason, which is printed, so a stale entry is visible rather than silent.
# Every node with a paper statement must appear here, with a sentence saying
# what the paper asserts and what the Lean statement asserts.  The counts below
# are advisory -- a regex cannot decide correspondence -- so the guarantee this
# file gives is the weaker but honest one: every statement has been read against
# the paper and the reading is written down.  A node missing from this table
# fails the check.
REVIEWED: dict[str, str] = {
    "ext-sandpile-growth":
        "cited input (Bou-Rabee-Panagiotis), a Prop assumed as hypothesis; five assertions, five Lean conjuncts in the same order, each an implication on d: "
        "(1) E u_n(0) asymp n^{(4-d)/4} for d<=3; (2) asymp log n for d=4; (3) c(log n)^{2/d} <= E u_n(0) <= C log(n+1) for d>=5; "
        "(4) asymp (log n)^{2/d} for d>=5 if eta(0) bounded below (Lean: exists b, a.e. b <= z); (5) for d<=3 the limit of n^{-(4-d)/4} E u_n(0) exists in (0,inf) (Lean: exists L>0 with Tendsto); "
        "asymp is `exists c C`, 0<c and 0<C separately, placed after d and nu and before `forall n, 2<=n`, and n>=2 is also imposed on the display (3); "
        "hypotheses: d>=1, nu a real probability measure, mean 0, 0<evariance<top, exists theta>0 with E e^{theta|z|}<inf; "
        "E u_n(0) is the integral of Parking.u eta n 0 over iidLaw d nu, with u_{n+1}=(eta+Pu_n)^+ and P the 1/(2d) averaging walkOp as in the paper "
        "(the file header's 'multiplied by 2d' is not reflected in the statement)",
    "lem-deferred":
        "two assertions, two Lean conjuncts; reindexed: paper's rho_j(y), j>=1, is Lean's stack entry `ω.2.1 (y, j)` with j : ℕ, so paper's j is Lean's j+1 and the event is `j+1 <= U ω n y`; "
        "conjunct 1 (measurability) is NOT literal measurability but a pathwise invariance for pairs with neighbour-valued stacks, equal eta, equal uniform variables `ω.2.2`, and stacks equal off (y,j); "
        "conjunct 2 is the displayed identity for every fixed eta, conditioning on eta being integration over stacks and uniforms (`probGiven`), and P(y,x) is `kern d y x` = 1{x~y}/(2d); only hypothesis 1<=d",
    "lem-density-compare":
        "one display 0 <= S~_t - S_t <= E eta~(0) - E eta(0), i.e. two inequalities = Lean conjuncts 3 and 4; Lean prepends two conjuncts (both survivor counts integrable, so S_t and S~_t are not junk integrals), four in all; "
        "eta is mu and eta~ is mu' (laws on Z-valued configurations, probability, integrable |eta(0)|); the coupling is Q with marginals mu, mu', invariant under the diagonal lattice shifts, and eta<=eta~ Q-a.s. at all sites; "
        "no iid assumption, as in the paper; S_t is `S (dataLaw d mu) t`, each system with its own stacks and uniforms; t : ℕ arbitrary; hypothesis 1<=d",
    "thm-master":
        "one display = two inequalities; Lean `exists c c` with 0<c and c<=C outside `forall n, 2<=n`, then the conjunction c(E u_n(0)+log n) <= E U_n(0) and E U_n(0) <= C(E u_n(0)+log n); "
        "hypotheses as explicit binders: nu a probability measure on Z, nonconstant as `forall k, nu {k} <> 1`, mean 0, exists theta>0 (theta, hθ, hexp) with E e^{theta|k|}<inf, 1<=d; "
        "E U_n(0), E u_n(0) are meanU, meanu under `law d nu`; hGrowth, hBernstein, hConcentration, hGreenNorms are cited inputs the proof uses, not in the paper's statement; "
        "the remark after the display (lower bound needs no exponential moment) lies outside the source range and is not in Lean",
    "ext-donsker-varadhan":
        "cited input (Donsker-Varadhan 1979, Theorem 1), assumed as hypothesis; the paper makes one assertion, log E_0[P(eta(0)>=0)^{|R_t|-1}] ~ -k t^{d/(d+2)} for some k>0; "
        "Lean states the general theorem instead: for every d>=1 and every a>0 there is k>0 (depending on a and d) with log E_0 exp(-a|R_t|) / t^{d/(d+2)} -> -k along t : ℕ; "
        "the paper's expectation is this one with a=-log P(eta(0)>=0), up to the constant factor P(eta(0)>=0)^{-1} from the exponent |R_t|-1, which does not affect the limit; "
        "~ is written as ratio -> -k; |R_t| is `rangeCard 0 p t` (distinct sites at times 0..t) under walkLaw from the origin",
    "thm-subcritical-tail":
        "one display = two bounds; Lean `exists c C` with 0<c and c<=C before `forall t, 1<=t`, then the conjunction C^{-1} exp(-C t^{d/(d+2)}) <= S_t and S_t <= C exp(-c t^{d/(d+2)}), with exponent (d:R)/(d+2); "
        "hypotheses: nu an integer-valued probability law with integrable |k|, integral of k < 0, nu(0,inf)>0, exists theta>0 with E e^{theta k}<inf (one-sided, no absolute value, as in the paper), 1<=d; "
        "S_t is `S (law d nu) t`; hDV (Donsker-Varadhan) is a cited input used in the proof, not in the paper's statement",
    "thm-oriented-walk":
        "five assertions: (a) E U_n(0) asymp n^{1/4} for d=2; (b) asymp log n for d>=3; (c) E U_n/E u_n -> 1 for d=2; (d) exists mu in (0,inf) with E U_n ~ mu n^{1/4}; (e) S_t ~ (mu/4) t^{-3/4}, here U, u, S are the oriented-walk quantities; "
        "Lean has three top-level conjuncts: (a) as `d=2 -> exists c C` (0<c<=C, forall n>=2, exponent 1/4); (b) as `3<=d ->` the same with Real.log n; "
        "(c),(d),(e) together under one `d=2 ->`, (c) first, then `exists mu>0` scoping over both (d) and (e); ~ is written as ratio -> 1, with S_t/((mu/4) t^{-3/4}), exponent (-(3:R))/4; "
        "hypotheses: 2<=d (the paper's cases start at d=2) and CriticalLaw nu (integer-valued probability law, nonconstant, mean 0, exponential moment); "
        "the walk is `orientedLaw` (steps +e_i with probability 1/d), u is `uOriented` with P f(x) = (1/d) sum_i f(x-e_i), meanU and meanuOriented are taken under `orientedLaw d nu`; "
        "hBern, hConc, hStability, hBinomial are cited inputs, not in the paper's statement",
    "ext-heat-interior-regularity":
        "cited input, assumed as hypothesis; the paper asserts this only in prose (Step 3: the distribution v = d_s U solving the heat equation on O is represented by a smooth function); "
        "Lean states the continuous-function form: for every d (0 included) and open U inside {s>0}, a continuous u that weakly solves d_s u = L u (L = (2d)^{-1} Laplacian; -integral u d_s psi = integral u L psi for smooth compactly supported psi with tsupport psi inside U) "
        "yields v with three conjuncts: v is C^infty on U; u = v pointwise on U; d_s v = L v classically on U (HasDerivAt); "
        "continuity of u is an extra hypothesis relative to the paper's distribution v (see MISMATCHES)",
    "ext-u-concentration":
        "cited input (BP Remark 3.4), assumed as a hypothesis and not proved here; one assertion "
        "(existence of C plus the displayed moment bound eq:u-concentration), which is one Lean "
        "`exists C, 0 < C /\\ forall n >= 1, forall q >= 2, ...` with C outside n and q; the "
        "quantifiers d >= 1, kernel range r, K with `IsLatticeKernel r K` (nonneg, sup-range <= r, "
        "stochastic, translation invariant), law nu on R, theta > 0 with E e^{theta|z|} < inf all "
        "come before C, so C depends on d, r, K, nu (and formally theta, which is equivalent to the "
        "paper's 'depends on K and the law of eta(0)'); the paper's moment order r is Lean's real "
        "`q >= 2`, because Lean's `r` is the kernel range; ||g_n^K||_2 = `l2Norm (kGreen r K n)`, "
        "||g_n^K||_inf = `supAbs (kGreen r K n)`, v_n = `kSol` (v_0 = 0, v_{n+1} = max 0 (eta + K v_n), "
        "K^j(0,.) by the forward recursion `kIter`), E is the integral against `iidLaw d nu`; eta is "
        "real valued, as in the paper; v_n(0) reads finitely many sites, so the integrals are not "
        "junk values",
    "thm-comparison":
        "one display u_n(x) <= E[U_n(x)|eta]; Lean asserts it as one inequality, for every d >= 1, "
        "every deterministic eta : Site d -> Z, every n and x (order forall eta, n, x, so it holds "
        "for each fixed eta and is not an almost-sure statement); left side is `Parking.u` of the "
        "real cast of eta (u_0 = 0, u_{n+1} = max 0 (eta + P u_n), P = walkOp); right side "
        "E[U_n(x)|eta] is realised as `meanUgiven`, the integral of U_n(x) over the stack-and-uniform "
        "law with eta held fixed (U_n(x) is bounded by an eta-dependent constant, so it is not a "
        "junk value)",
    "lem-transport":
        "paper makes four assertions (E A_t(0)=S_t; E U_n(0)=sum_{s<n} S_s; exchangeability of the k "
        "origin particles given eta(0)=k; the expansion S_t = sum_{k>=1} k P(eta(0)=k) "
        "P(tau_1>t|eta(0)=k)), mapped in that order to the four top-level Lean conjuncts; conjunct 1 "
        "also asserts integrability of A_t(0) and of the survivor count, and conjunct 4 also asserts "
        "summability (strengthenings that exclude junk integral/tsum values); MISMATCH: Lean adds the "
        "hypothesis E|eta(0)| < inf (`hint`), which the paper does not state; law is `Parking.law d nu` "
        "(i.i.d. integer eta, stacks, uniforms); A_t(0) = `activeCount`, which equals U_{t+1}-U_t by "
        "the definition of a round; S_t = E of the number of labels (0,i), i < eta(0)^+, active after "
        "round t, so paper particle i is Lean label (0,i-1) and 'tau_i > t' is 'active after round "
        "t'; exchangeability is read as invariance of the joint law of the activity histories "
        "(t,i) |-> active_t(0,i) under every permutation of N fixing all i >= k, for the law "
        "restricted to {eta(0)=k}, for k >= 1 with nu{k} != 0 (activity histories only, not "
        "positions); the expansion is written with joint probabilities and reindexed, as "
        "sum'_{k>=0} (k+1) P(eta(0)=k+1, active_t(0,0)), the same identity without conditioning on "
        "null events",
    "cor-growth":
        "paper makes four relations: E U_n(0) ≍ n^{(4-d)/4} (d<=3), E U_n(0) ≍ log n (d>=4), "
        "S_t ≍ (t+1)^{-d/4} (d<=3), and c/(t+1) <= S_t <= C log(t+2)/(t+1) (d>=4); Lean has two "
        "top-level conjuncts `d <= 3 -> exists c C ...` and `4 <= d -> exists c C ...`, each holding "
        "the E U_n bound (two-sided, forall n >= 2, the range of n is not stated in the paper and is "
        "taken as that of thm:master) and the S_t bound (forall t >= 0) with ONE shared pair "
        "0 < c <= C (equivalent to the paper's separate constants, by taking min and max); c, C come "
        "after d and nu, so they depend on the dimension and the law only; the assumptions of "
        "thm:master are `CriticalLaw nu` (probability, nonconstant, mean zero, exponential moment) "
        "and d >= 1; Lean also takes the four cited externals hGrowth, hBernstein, hConcentration, "
        "hGreenNorms as hypotheses, which the paper's proof invokes but its statement does not list; "
        "S_t is `Parking.S (law d nu) t`",
    "prop-everyone-settles":
        "paper makes four assertions on one probability-one event (every particle settles in finite "
        "time; every hole is filled in finite time; infinitely many distinct particles leave every "
        "site; U_infinity(x)=infinity for all x); Lean is one `forall^m omega` of four conjuncts in "
        "that order; particle settles = `active p = false` for all t >= some t0, and the quantifier "
        "ranges over all labels, the phantom labels with index >= eta(x)^+ being trivially inactive; "
        "hole filled = for each site x, `H omega t x = 0` for all t >= some t0 (equivalent, since "
        "each site has finitely many holes); 'leave x' = label p with some t such that p is active at "
        "x after round t and stands elsewhere after round t+1, and the set of such labels is "
        "`Set.Infinite`; U_infinity is `Ulimit` in N-infinity equal to top; hypotheses are "
        "`CriticalLaw nu` and d >= 1, plus the four cited externals hGrowth, hBernstein, "
        "hConcentration, hGreenNorms, which the paper's proof uses but its statement does not list",
    "lem-near-tilt":
        "one display S_t^delta <= C E_0 e^{-c delta^2 |R_t|}; Lean has `exists c C > 0, exists delta1 "
        "in (0, delta0], forall delta in (0, delta1], forall t`, with a conjunct asserting "
        "integrability of the survivor count (to exclude a junk integral) alongside "
        "`S (law d (nu delta)) t <= C * rangeExp d (c*delta^2) t`; 'sufficiently small delta' is the "
        "explicit threshold delta1; c, C, delta1 are chosen after d, delta0, the whole family nu, "
        "theta, M, K, so they may depend on all of these but not on delta or t; the hypotheses of "
        "thm:near are `NearFamily delta0 nu theta M K` (probability laws on Z, mean -delta on "
        "[0,delta0], nu 0 nonconstant, E e^{theta|eta|} <= M, and for delta in (0,delta0] a coupling "
        "with E|eta_delta - eta_0| <= K delta); `rangeExp d a t` = E_0 e^{-a |R_t|} with |R_t| the "
        "number of distinct sites among X_0..X_t of an independent simple random walk; S_t^delta is "
        "the expected number of origin particles active after round t",
    "ext-spatial-fixed-time-tightness":
        "cited input (BP Theorem 1.3(i)(b), via the paper's Step 1 of prop:spatial-scaling), assumed "
        "as a hypothesis; MISMATCH: the paper displays no such statement, and Lean states a derived "
        "consequence, namely equicontinuity in probability at one fixed time (limsup form) for the "
        "divisible odometer alone; one assertion, Lean `forall d in {1,2,3}, forall nu with "
        "CriticalLaw, forall T > 0, compact K', eps > 0, eps' > 0, exists delta > 0, exists R0, "
        "forall R >= R0, P(eps < sup_{x,y in K', dist x y <= delta} |ubar_R(T,x) - ubar_R(T,y)|) <= "
        "eps'`, with ubar_R = `barDivisible` = R^{d/2-2} u_{floor(T R^2)}(floor(R x)), dist the "
        "sup metric on Fin d -> R, and the probability taken under `Parking.law d nu`; nothing "
        "about eta_R, the particle odometer, time-joint behaviour or the limit is included",
    "ext-heat-compactness":
        "cited input (classical parabolic compactness), assumed as a hypothesis; MISMATCH: the "
        "paper's Step 3 (lines 1785-1805) contains no compactness statement, only the phrase "
        "'interior parabolic regularity'; one Lean assertion, for d >= 1 and any open "
        "U in R x R^d: if f_n are C^infty on U, nonnegative on U, solve d_s f = (2d)^{-1} Laplacian_x f "
        "pointwise on U (`contOp`), and have sup_n of the L^1 norm over each compact K in U finite, "
        "then there are a strictly increasing r and a C^infty nonnegative classical heat solution v "
        "on U with f_{r n} -> v uniformly on every compact subset of U",
    "ext-bernstein":
        "cited input (Pinelis Thms 4.1 and 3.3), assumed as a hypothesis; the paper makes two assertions "
        "(bounded case; Bernstein-moment case), Lean has exactly two top-level conjuncts under "
        "`exists C, 0 < C` bound before every other datum (universal C, one C for both, "
        "equivalent to the paper's two by taking a max); "
        "conjunct 1: (forall i in 1..k, forall omega, |xi_i| <= a) -> "
        "(E|sum xi|^r)^(1/r) <= C(sqrt r (E[(sum E[xi_i^2|F_{i-1}])^{r/2}])^(1/r) + r a); "
        "conjunct 2: forall v > 0, (a.s. sum_i E[|xi_i|^q|F_{i-1}] <= q!/2 a^(q-2) v for every integer q >= 2) "
        "-> (E|sum xi|^r)^(1/r) <= C(sqrt(r v) + r a), with NO boundedness hypothesis (the paper's 'instead'); "
        "filtration and xi are indexed over all of N (monotone, adapted, integrable for every i) "
        "with the martingale-difference and bound conditions only for 1 <= i <= k; "
        "Lean side conditions the paper lacks, each only narrowing the statement: "
        "Omega : Type (universe 0), xi_i adapted and integrable for i = 0 and i > k, "
        "and integrability of |xi_i|^q for all i and q in conjunct 2 (a junk-value guard, "
        "implied for 1 <= i <= k by the moment hypothesis); "
        "r >= 2 and a > 0 real, conditional expectations are Mathlib `condExp`",
    "lem-activity-holes":
        "one display, E A_t(0) - E H_t(0) = E eta(0) for every t >= 0; "
        "Lean has three conjuncts: Integrable A_t(0), Integrable H_t(0) (junk-value guards, not in the paper), "
        "then the identity, with t a variable before the conclusion; "
        "eta is a translation invariant law mu on (Z^d -> Z), not i.i.d., "
        "with stacks and uniforms an independent product factor (`dataLaw d mu`); "
        "hypotheses: probability measure, `TranslationInvariant`, Integrable |eta(0)|, d >= 1; "
        "A, H are `activeCount`, `holeCount` of the driver built from the data",
    "lem-range-lower":
        "two displayed relations in the paper (P(tau_1 > t | eta(0) = k) >= E_0[P(eta(0) >= 0)^(|R_t| - 1)], "
        "and 'consequently' S_t >= E[eta(0)^+] E_0[...]); Lean has three conjuncts: "
        "(1) forall t, Integrable of the range power under `walkLaw d` (junk-value guard, not in the paper); "
        "(2) forall k >= 1 with nu{k} != 0, forall t: E_0[...] <= `survivalGiven d nu k t`, "
        "which is the joint probability P(eta(0) = k and particle (0,0) active after round t) divided by nu{k} "
        "(paper's particle 1 is label (0,0), tau_1 > t is active after round t); "
        "(3) forall t: (integral of max k 0 dnu) * E_0[...] <= S_t under `law d nu`; "
        "E_0 is an integral over `walkLaw d`, |R_t| is `rangeCard 0 p t` "
        "(natural-number `- 1` is harmless since |R_t| >= 1); "
        "P(eta(0) >= 0) is `(nu {j | 0 <= j}).toReal`; "
        "all the paper's standing hypotheses are present (finite first moment, negative mean, "
        "P(eta(0) > 0) > 0, E e^{theta eta(0)} < inf with no absolute value) "
        "though the proof does not read the last three; nu is the i.i.d. one-site law, d >= 1",
    "prop-discrepancy":
        "two assertions (moment bound with three dimension cases, then the tail bound); "
        "Lean is `exists C, 0 < C` (after d, nu, so C may depend on d and nu, not n) then two conjuncts: "
        "(i) forall n >= 1, Integrable (guard, not in the paper) and "
        "(E|U_n(0) - u_n(0)|^r)^(1/r) <= C * (if d = 1 then n^(5/8) log(n+1)^(3/4) "
        "else if d = 2 then n^(1/4) log(n+1)^(5/4) else n^(1/8) log(n+1)^(3/4)), "
        "with r = `discrepancyExponent n` = max 2 (ceil (log(n+1))) read as a real; "
        "(ii) forall eps > 0, exists c > 0, exists N, forall n >= N, "
        "P(eps * E u_n(0) < |U_n(0) - u_n(0)|) <= exp(-(c (log n)^2)), "
        "'sufficiently large n' is an explicit N depending on eps; "
        "'assumptions of thm:master' is `CriticalLaw nu` (probability, nonconstant, mean 0, "
        "E e^{theta |eta(0)|} < inf), with 1 <= d <= 3 as hypotheses; "
        "the four cited inputs SandpileGrowth, Bernstein, UConcentration, GreenNorms enter as explicit hypotheses",
    "prop-resolvent":
        "two assertions (pointwise bound, then tail sum <= 1); Lean is `exists c C, 0 < c, 0 < C` after d "
        "(so c and C may depend on d) then two conjuncts: "
        "(A) forall a in (0,1], forall t >= 1, three implications: "
        "d = 1 -> E_0 e^{-a|R_t|} <= C exp(-c a^(2/3) t^(1/3)); "
        "d = 2 -> e/a <= t -> ... <= C exp(-c sqrt(a t / log(t+2))); "
        "3 <= d -> ... <= C exp(-c sqrt(a t)); "
        "(B) forall a in (0,1], Summable (guard, not in the paper) and "
        "sum over t > T of E_0 e^{-a|R_t|} <= 1, "
        "where T = `resolventThreshold d C a` is the SAME C times a^(-2) L^3 (d = 1), a^(-1) L^3 (d = 2), "
        "a^(-1) L^2 (d >= 3), L = log(e/a); the paper's C in T is read as the same C "
        "(equivalent to a possibly larger one, both bounds being monotone in C); "
        "E_0 e^{-a|R_t|} is `rangeExp d a t`, an integral over `walkLaw d`",
    "thm-near":
        "one asymptotic-equivalence display (four dimension cases), formalised as "
        "`exists c C, 0 < c <= C, exists delta1 > 0, forall delta in (0, delta1]`: "
        "ofReal(c * rate) <= E U_inf^delta(0) <= ofReal(C * rate) in ENNReal, "
        "so the upper bound also asserts finiteness; rate = delta^(-3), delta^(-1), delta^(-1/3), log(e/delta) "
        "for d = 1, 2, 3, >= 4 (`nearRate`); c, C, delta1 are chosen after "
        "d, delta0, nu, theta, M, K, so they may depend on the whole family and its parameters, not on delta; "
        "the family is `nu : R -> Measure Z`: for delta in [0, delta0] probability with mean -delta, "
        "nu 0 nonconstant, Integrable e^{theta|k|} with integral <= M "
        "(explicit uniform bound M, integrability added as a junk-value guard), "
        "and for delta in (0, delta0] a coupling pi on Z x Z with marginals nu delta, nu 0 and "
        "integral of |p.1 - p.2| <= K delta; E U_inf^delta(0) is `meanUlimit (law d (nu delta))`, "
        "a lintegral of the supremum in N-infinity; "
        "the five cited inputs SandpileGrowth, Stopping, UConcentration, GreenNorms, Bernstein "
        "enter as explicit hypotheses",
    "ext-spatial-stopping-stability":
        "cited input, assumed as a hypothesis; the paper text at the cited lines makes NO such assertion "
        "(see MISMATCHES): it says only that BP's argument gives the joint convergence of (eta_R, u-bar_R) "
        "with estimates uniform on compact time intervals; the Lean statement is a single implication chain, "
        "not a transcription: forall d in [1,3], forall Brownian space (generator Delta/(2d), start 0), forall T > 0, "
        "IF the rescaled simple random walk z/sqrt(n) at step floor(n t_i), t_i in [0,T], converges in finite-dimensional "
        "distributions to B (bounded continuous F on (R^d)^m, any m), then forall M >= 0, "
        "continuous G bounded by M, G'_n bounded by M converging to G uniformly on [0,T] x R^d, "
        "forall eps > 0, exists N, forall n >= N: "
        "|stoppingSup d (k,z -> G'_n(k/n, z/sqrt n)) floor(nT) 0 - spatialContValue B PB G T| <= eps; "
        "N depends on every earlier datum; "
        "nothing about scenery, white noise or the odometer is assumed",
    "ext-spatial-odometer-scaling":
        "cited input, assumed as a hypothesis (BP Thm 1.3(i)(b), strengthened as the paper's Step 1 sentence "
        "claims: 'time variable and scenery retained', 'estimates uniform on compact time intervals'); "
        "the cited lines are a citation sentence, not a display, so the limit objects come from the setup of "
        "prop:spatial-scaling at lines 1679-1699; Lean: forall d in [1,3], forall nu with `CriticalLaw`, "
        "EXISTS a probability space with W, Z, Uc (the limit is exhibited, not given for an arbitrary noise) "
        "satisfying 11 conjuncts: (1) W is a mean-zero linear Gaussian white noise of intensity Var(eta(0)); "
        "(2) W phi measurable; (3) Z is the Green field, given by the L^2 isometry I with ||I f|| = sqrt(Var) ||f|| "
        "extending W; (4) Z jointly continuous; (5) Uc(0,.) = 0; (6) Uc jointly continuous; "
        "(7) Uc nondecreasing in s; (8) Uc(s,x) measurable; "
        "(9) exists a Brownian space (generator Delta/(2d)) with Uc = Z + Brownian optimal-stopping value "
        "(`contUc`, integrable payoffs only) for all T >= 0; "
        "(10) joint finite-dimensional convergence as R -> infinity (real R) of "
        "(scenePair R phi_i, barDivisible R s_j x_j) to (W phi_i, Uc s_j x_j), bounded continuous F, s_j > 0; "
        "(11) equicontinuity in probability of barDivisible on every compact set of positive times; "
        "the paper's 'locally uniformly' is therefore (10) plus (11); "
        "the particle odometer U-bar_R is not part of this input, it is transferred through prop:discrepancy; "
        "the source sandpile.tex is not in the repository, so the strengthening beyond the quoted "
        "fixed-T C_loc statement is unverified",
    "lem-tagged-monotonicity":
        "one assertion (an implication at every round: 'stays active at least as long' is read as "
        "active at round t in the first process implies active at round t in the second); Lean is a "
        "single implication, no conjunction, `forall p, forall t`; reformulation: the coupling is the "
        "particle-driven one (`PDriver` with eta, per-particle moves, per-particle ranks), the second "
        "process is `addParticleDriver x0 D` (eta raised by one at x0, everything else shared), and the "
        "statement is pathwise for every driver D and every x0, not almost sure; 'every particle present "
        "in both' is `forall p : Label d` (a label active in the first process is present in both, so "
        "quantifying over all labels is no stronger); `1 <= d` is unused",
    "lem-shift":
        "one display in the paper; Lean has three conjuncts: (i) for each `l` the sum over `j` of the "
        "squared difference is summable, (ii) the series over `l` of these sums is summable, (iii) the "
        "identity `tsum_l tsum_j (binomLaw l (j-q) - binomLaw l j)^2 = 4*|q|`; (iii) is the paper's "
        "display, (i) and (ii) are additions that exclude a junk `tsum`; no `d = 2` hypothesis, the "
        "layer law `vec p_l` is written directly as `binomLaw l` (Bin(l,1/2) on {0..l}, zero on the rest "
        "of Z), the norm is the l^2 norm over Z, the translate `p_l(.-q)` is `binomLaw l (j-q)`, `q : Z` "
        "is cast to R and quantified outside",
    "lem-w-martingale":
        "paper: one existence claim with five assertions (w_n(0)=sum xi_i; finitely many xi_i nonzero "
        "a.s.; E[xi_i|F_{i-1}]=0; the bound |xi_i| <= max_{m<n} max_y max_{z~y}|g_m(z)-(Pg_m)(y)|; the "
        "quadratic-variation identity); Lean: `exists F xi` then ten conjuncts: F monotone; F i below the "
        "ambient sigma-algebra; xi i is F(i+1)-measurable; xi i integrable; a.e. `exists N, forall i>=N, "
        "xi i = 0`; a.e. `wErr omega n 0 = tsum_i xi i omega`; `condExp[xi i | F i] =ae 0`; "
        "`forall i omega, |xi i omega| <= greenIncrement d n` (everywhere, not only a.e.); a.e. "
        "summability of `i |-> condExp[xi_i^2|F i]` and, for every `s : N`, of `y |-> A omega (s-1) y * "
        "gamma d (n-s) y`; the a.e. identity of `tsum_i condExp[xi_i^2|F i]` with `sum_{s in Icc 1 (n-1)} "
        "tsum_y A_{s-1}(y) Gamma_{n-s}(y)`; the filtration properties, adaptedness, integrability and "
        "summability conjuncts are not in the paper (implicit or junk-value guards); reindexing: xi is "
        "indexed from 0, Lean `xi i` is the paper's xi_{i+1} and the filtration is NOT shifted (Lean `F i` "
        "is the paper's F_i), so `condExp[xi i|F i]` is E[xi_{i+1}|F_i]; the file header's 'paper's "
        "F_{i-1} is F i' is off by one but the statement is as described here; setting: `law d ν` with ν "
        "a probability measure on Z (i.i.d. eta, stacks, uniforms), `1 <= d`, `2 <= n`, `wErr omega n 0` "
        "is w_n(0), `gamma` is Gamma",
    "thm-four-sparse":
        "one display; Lean: `exists c>0` bound before `forall eps in (0,1/2]`, then `eventually n, c * "
        "log(e/eps) <= meanU/meanu` on `law 4 (threePointLaw (eps/2))` (mass eps/2 at 1, eps/2 at -1, "
        "1-eps at 0, i.i.d. on Z^4); the paper's `liminf >= c log(e/eps)` is written as an eventual "
        "inequality, which implies the paper's liminf with the same c (the paper's implies it with a "
        "smaller c), avoiding a junk real liminf; the quotient is real division of E U_n(0) by E u_n(0), "
        "and a junk 0 from a zero denominator or non-integrable numerator is excluded because the right "
        "side is positive; `hGrowth` (`SandpileGrowth`, BP growth of the mean odometer) and `hStopping` "
        "(`Stopping`, optimal-stopping representation) are cited inputs entering as hypotheses, absent "
        "from the paper's statement; the threshold in n depends on eps, c does not",
    "lem-mean-horizon":
        "one displayed inequality; Lean: `exists C>0` fixed before `forall delta in [0,delta0], forall n, "
        "forall sigma`, then two conjuncts: integrability of `eta |-> E_walk sum_{j<sigma} xi_delta(X_j)` "
        "(added, junk guard) and `E_eta E_walk sum_{j<sigma} xi_delta(X_j) <= C * phi d Mσ` (the paper's "
        "display); renaming: the paper's `M = E sigma` is `Mσ`, given by hypothesis `Mσ = int_eta int_X "
        "sigma eta X` (average over configuration and walk), while Lean's `M` (with theta, K, delta0) "
        "belongs to `NearFamily delta0 ν θ M K`, the hypotheses of thm:near (mean -delta, ν 0 "
        "nonconstant, uniform exponential moment <= M, coupling with E|.|<=K delta) which the paper "
        "leaves to its ambient setting; `xi_delta = eta_delta + delta` is `xi delta eta` with eta ~ "
        "`iidLaw d (ν delta)`; 'conditionally on xi_delta' is `sigma : config -> path -> N` with each "
        "`sigma eta` a walk stopping time, `sigma eta X <= n` for one n, and measurable in eta for each "
        "X; C may depend on d and the family but not on delta, n, sigma, Mσ; the paper's 'sufficiently "
        "small delta' is not imposed, Lean covers all delta in [0,delta0] (a stronger range); `phi d` is "
        "(s+1)^{(4-d)/4} for d<=3 and log(s+2) otherwise; four cited inputs are hypotheses "
        "(`SandpileGrowth`, `Stopping`, `UConcentration`, `GreenNorms`), absent from the paper's statement",
    "ext-variance-scale":
        "cited input, assumed as a hypothesis and not proved here; the named parking.tex lines state none "
        "of it (see MISMATCHES), so this describes the Lean `Prop` only; it is a conjunction of three "
        "parts: (1) `forall d>=1, exists c C>0, forall t>=2`, `c*varianceRate d t <= tsum_y greenTime d t "
        "0 y ^2 <= C*varianceRate d t`, rate t^{3/2}, t, t^{1/2}, log t, 1 for d=1,2,3,4,>=5 "
        "(eq:Qt-table); (2) `forall 1<=d<=4, exists C>0, forall 1<=m<=n`, `sum_x g_m(0,x) g_n(0,x) <= "
        "C*corrRate d m n*||g_m||_2*||g_n||_2` with corrRate (1+log(n/m))sqrt(m/n) for d=2, "
        "sqrt((1+log m)/(1+log n)) for d=4, (m/n)^{1/4} for d=1,3 (eq:corr-bound); (3) d=4 only, one "
        "`exists C>0` shared by: for `1<=m<n` and all x, `sum_z windowKernel m n x z ^2 <= C(1+log((n+2)/"
        "(m+2)))` and `windowKernel m n x z <= C/m`, and for `n>=2` and all x, `sum_z greenTime 4 n x z "
        "^2 <= C log(n+2)` and `greenTime 4 n x z <= C`; c and C depend on d in (1) and (2), are "
        "absolute in (3)",
    "ext-srw-local-clt":
        "cited input (BP eq. (25), quoting Lawler-Limic Thm 2.1.3 Eq. (2.8)), assumed as a hypothesis and "
        "not proved here; the named parking.tex lines do not state it (see MISMATCHES); one quantified "
        "statement, no conjunction: `forall d>=1, forall delta T C0` with `0<delta<=T`, `0<=C0`, `forall "
        "eps>0, exists R0, forall R>=R0`, for all `l : N` with `delta R^2 <= l <= T R^2` and all sites "
        "x,y with `|x-y|^2 <= (C0 R)^2` and `srwHeat d l (x-y) > 0`: `R^d * |srwHeat d l (x-y) - 2 "
        "R^{-d} contHeatKernel d (l/R^2) (x/R) (y/R)| < eps`; this is BP's `lim_{R->inf} R^d sup{...} = "
        "0` unfolded into a uniform eps bound (Lean allows delta=T where BP has delta<T); p_l(x,y) is "
        "`srwHeat d l (x-y)` = P^l(0,x-y); `contHeatKernel` is (4 pi t/(2d))^{-d/2} exp(-d|x-y|^2/(2t)), "
        "the Brownian kernel with generator (2d)^{-1} Delta (BP eq. (14)), the factor 2 being the parity "
        "correction; it is not a hypothesis of `spatial_scaling`",
    "prop-spatial-scaling":
        "paper: four displays plus one sentence, five assertions after the setup (joint convergence "
        "eq:space-time-scaling; driven equation on O eq:continuum-equation; signed-density limit "
        "eq:signed-density-limit, jointly with the first; v smooth on O; v>0 on O "
        "eq:strict-time-derivative); Lean: `exists Omega Q W Uc v` (the limit objects are asserted to "
        "exist on a probability space, the paper takes W and U as given) then 13 conjuncts: (1) "
        "`IsSpatialWhiteNoise` of intensity Var nu (linear, mean 0, covariance v*int phi psi, Gaussian "
        "marginals); (2)-(4) measurability of `W phi`, `Uc s x`, `v s x`; (5)-(7) `Uc(0,.)=0`, jointly "
        "continuous, monotone in s; (8) `exists Z` a continuous Green field paired with W plus a "
        "Brownian space B with `Uc = contUc` (Z plus the Brownian optimal-stopping value) for T>=0, which "
        "is Lean's definition of 'continuous Brownian optimal-stopping value driven by W'; (9) "
        "finite-dimensional convergence, for finite families of test functions and positive-time points, "
        "of (<eta_R,phi_i>, u_R, U_R, <nu_R,chi_l>) to (W phi_i, U, U, W chi_l + int U(1,x) L chi_l(x) "
        "dx) against bounded continuous F, carrying the finite-dimensional content of "
        "eq:space-time-scaling and eq:signed-density-limit together (L U(1,.) is tested by integration "
        "by parts); (10) for compact K in (0,inf) x R^d, sup_K |U_R - u_R| -> 0 in probability; (11) "
        "equicontinuity in probability of u_R on such K; (9)-(11) are Lean's reformulation of 'converging "
        "as a random distribution / locally uniformly' (finite-dimensional convergence plus asymptotic "
        "equicontinuity plus closeness), not literally convergence in law in a topology; (12) a.e. omega, "
        "for every space-time test psi with tsupport psi inside O: `-int U d_s psi = int U L psi + "
        "W(int psi ds)`; (13) a.e. omega: v is C^infinity on O, v is the distributional d_s U on O, and "
        "`0<U s x -> 0<v s x`; rescalings: `barDivisible`, `barOdometer` are R^{d/2-2}(.)_{floor(sR^2)}"
        "(floor(Rx)), `scenePair` is <eta_R,phi>, `signedPair` is <nu_R,phi> with A-H at floor(R^2), "
        "R real to infinity, law `law d nu`, `nu : CriticalLaw` (probability, nonconstant, mean 0, "
        "exponential moment), `1<=d<=3`; eight cited inputs enter as hypotheses (`SandpileGrowth`, "
        "`Bernstein`, `UConcentration`, `GreenNorms`, `SpatialOdometerScaling`, `HeatInteriorRegularity`, "
        "`HeatStrongMinimum`, `HeatCompactness`), absent from the paper's statement",
    "lem-parallel":
    "two assertions: `U_0 = 0` is the first Lean conjunct (forall x); the recursion for every n, x is the second, "
    "with `(.)^+` as `max 0`, U cast to Z, eta integer-valued; the paper's sum over all y is Lean's sum over "
    "`nbrFinset x` and the two agree only under the added hypothesis `hstep` (every stack entry `omega.2.1 q` is a "
    "neighbour of `q.1`, i.e. neighbour-valued stacks, the model's realizations; not written in the paper's statement); "
    "stacks are indexed from zero so `rho_{j+1}(y) = omega.2.1 (y,j)` and `I_{y,x}(m)` is `arrivals ... y x m`; "
    "d is unconstrained (d = 0 makes `hstep` unsatisfiable, vacuous)",
    "lem-nearest-close-pair":
    "one display with explicit constant 2, no free constants: `P(H_t(x)=H_t(z)=1) <= 2 p h_t` for every t : N and "
    "distinct x z; the setting of parking.tex:1835-1866 is carried as hypotheses `5 <= d`, `0 < p <= 1/4` and law "
    "`threePointLaw p` (P(+1)=P(-1)=p, P(0)=1-2p); `h_t` is `holeProb d (threePointLaw p) t` = P(H_t(0)=1); "
    "probabilities are `(law ...).toReal` of the event",
    "ext-green-norms":
    "cited input (Bou-Rabee-Panagiotis Section 3.1), assumed as a hypothesis, not proved; the display holds two "
    "relations `asymp` and Lean has two conjuncts, each with its own `exists c C > 0`, inside `forall d >= 1` so the "
    "constants depend on d only, each valid for all `n >= 2` (the paper's 'throughout the range'); "
    "l2 rates n^{3/4}, n^{1/2}, n^{1/4}, sqrt(log n), 1 for d = 1, 2, 3, 4, >=5; max rates n^{1/2}, log n, 1 for "
    "d = 1, 2, >=3; g_n = sum_{j<n} P^j(0,.) is `green d n`, `l2Norm` is sqrt of the tsum of squares (finite support), "
    "`greenMax` the iSup",
    "thm-trichotomy":
    "five cited inputs as explicit hypotheses (SandpileGrowth, Bernstein, UConcentration, GreenNorms, Stopping); "
    "`1 <= d` and three conjuncts by d (`d <= 3`, `d = 4`, `5 <= d`); the theorem's hypotheses are `CriticalLaw nu` "
    "(probability, non-Dirac, mean zero, exponential moment for some theta) quantified inside each part; "
    "(i) four assertions: a.s. convergence of (U_n(0)-u_n(0))/E u_n(0) to 0; L^r convergence for every r >= 1 written as "
    "integrability for every n plus E|.|^r -> 0; E U_n/E u_n -> 1; n^{-(4-d)/4} E U_n -> L with 0 < L real; "
    "(ii) three assertions: ratio >= 1 for n >= 1 and `exists B` bounding it for n >= 1 (both under forall nu, B "
    "depends on nu), then forall B > 0 exists a critical nu with `B <= liminf` (real liminf, not a junk escape since "
    "the ratio is >= 1 and bounded for each nu); the paper's 'no uniform bound' sentence is that last clause; "
    "(iii) for nu bounded below (`exists b, nu (Iio b) = 0`): one shared `exists c C`, `0 < c <= C`, for n >= 2 "
    "giving c log n <= E U_n <= C log n and c log n <= E|U_n-u_n| <= C log n (positive lower bounds rule out the "
    "junk zero of a Bochner integral), plus ratio -> infinity; U is `U omega n 0`, u_n is `uOf omega n 0`, "
    "expectations are `meanU`, `meanu`",
    "prop-near-divisible":
    "four cited inputs as hypotheses (SandpileGrowth, Stopping, UConcentration, GreenNorms); the assumptions of "
    "thm:near are `NearFamily delta0 nu theta M K` (mean -delta, nonconstant nu 0, exponential moment <= M, coupling "
    "with `E|eta_delta - eta_0| <= K delta`); four assertions as four conjuncts: (a) upper bound C*`nearRate` for "
    "all d (delta^-3, delta^-1, delta^-1/3, log(e/delta) for d = 1, 2, 3, >=4); (b) reverse bound c*`nearRate` for "
    "d <= 4; (c) for d >= 5 lower bound c [log(e/delta)]^{2/d}; (d) for d >= 5 and support in [-B,B] for every "
    "delta' in [0,delta0] two-sided [log(e/delta)]^{2/d}; "
    "`exists c C > 0, exists delta1 <= delta0` outside `forall delta in (0, delta1]` ('sufficiently small'), "
    "constants may depend on d and the whole family; E u_infty is `meanuLimit` in ENNReal (sup of E u_n) compared "
    "through `ENNReal.ofReal`",
    "ext-multivariate-berry-esseen":
    "cited input, assumed as a hypothesis, not proved; parking.tex:1807-1833 contains no such statement (see "
    "MISMATCHES), the reading is against the sibling display sandpile.tex:1770-1782 (Raic Thm 1.1 standardized), "
    "one display `|P(Y_j<=h_j all j) - P(G_j<=h_j all j)| <= C m^{1/4} sum|a(x)|^3`; Lean is a Prop "
    "`forall M delta (0<M, 0<delta<1), exists C > 0, forall N m >= 1, forall nu, ...` so C depends on (M, delta) only; "
    "coordinates are i.i.d. `Measure.pi nu` on `Fin N` and unnormalized, so the Gaussian has covariance "
    "`gram = Var(nu) sum a a^T` and the bound carries Var(nu)^{3/2}; extra hypotheses: mean zero, 0 < Var, "
    "`int|z|^3 <= M Var^{3/2}`, quadratic form of `gram` in [(1-delta), (1+delta)] |v|^2; orthant events, "
    "real `toReal` difference; identical to the sibling repo's statement",
    "thm-oriented":
    "three assertions as three conjuncts (d = 2 upper, d >= 3 upper, lower); `2 <= d` as in the section; the law is "
    "`nu : Measure ℤ`, integer-valued only (see MISMATCHES); standing hypotheses `hprob`, `hint` (|k| integrable, "
    "implicit in 'mean zero') and `hmean`; d = 2: `forall r > 4` with the r-th moment finite, `exists C`, "
    "`E u_n(0) <= C n^{1/4}` for all n >= 1; d >= 3: `forall theta > 0` with exponential moment, `exists C`, "
    "`<= C log(n+1)`; lower: `0 < evariance < top` gives `exists c > 0`, `c sqrt(kappa_d(n)) <= E u_n(0)` for all "
    "n >= 1, with kappa = sqrt n (d = 2), log(n+1) (d = 3), 1 (d >= 4) as `orientedKappa`, no exponential-moment "
    "hypothesis; `forall r/theta` then `exists C` equals the paper's 'for some r/theta' since the conclusion does not "
    "mention them; C may depend on d, nu (and r, theta); `E u_n(0)` is `meanuOriented (orientedLaw d nu) n` with "
    "`(P f)(x) = (1/d) sum_i f(x - e_i)`",
    "thm-nearest":
    "one assertion: `Tendsto` of `(law d nu {HoleCloser omega t}).toReal` to 0 as t : N (rounds) -> infinity; "
    "`HoleCloser` is graph (l^1) distance to the nearest unfilled hole strictly less than that to the nearest active "
    "particle, both in `N∞` (inf over empty set is top, so holes present and no active particle counts as hole "
    "closer); hypotheses `1 <= d <= 3` and `CriticalLaw nu` (integer-valued, non-Dirac, mean zero, exponential "
    "moment); the paper's statement is unconditional but Lean carries eleven cited inputs the proof uses as explicit "
    "hypotheses (SandpileGrowth, Bernstein, UConcentration, GreenNorms, SpatialOdometerScaling, HeatInteriorRegularity, "
    "HeatStrongMinimum, HeatCompactness, CriticalScaleLowerTail, VarianceScale, MultivariateBerryEsseen); "
    "conclusion unchanged",
    "lem-one-particle":
        "one sentence, two alternatives (H~=H and A~-A is a unit at one site, or A~=A and H-H~ is a unit at one site), for every t>=0; "
        "Lean is the same disjunction, each branch a `forall x` equality plus `exists z` (+1 at z, equal at every x != z), t an argument; "
        "'eta~ = eta + 1 at one site, shared particles keep their walks and uniforms' is `addParticleDriver x0 D` in the particle-driven "
        "construction (PDriver: per-particle moves and ranks; `addParticle` raises eta at x0, existing labels keep moves and ranks), "
        "stated pathwise for every driver D with no probability; H_t = `pHoleCount`, A_t = `pActiveCount` (= U_{t+1}-U_t); `hd : 1 <= d` unused",
    "lem-gamma-sum":
        "one display; Lean asserts two conjuncts (`Summable` of y |-> sup_{m<=n} Gamma_m(y), and tsum <= C kappa_d(n)) with `exists C` (0<C) "
        "outside `forall n>=1`, so C depends on d only; sup over m<=n is `⨆ m ∈ Set.Iic n` (m=0 contributes 0, no junk effect since Gamma>=0), "
        "Gamma_m = `gamma d m y` = sum_{z~y}(1/2d)(g_m(z)-(Pg_m)(y))^2 with g_m = `green`, kappa = `kappa` (sqrt n, log(n+2), 1); "
        "extra hypothesis not in the lemma: `hgrad : 2<=d -> GreenGradient d` (eq:green-gradient, cited from Lawler-Limic; proved as External.greenGradient)",
    "thm-upper":
        "two displays (eq:target for n>=2, eq:critical-moment for r>=2); Lean has one `exists C` (0<C, after d and nu, so depends on d and the law) "
        "outside two conjuncts, each carrying an added `Integrable` fact next to the inequality: (i) forall n>=2, meanU <= C(meanu + log n); "
        "(ii) forall n>=1, forall real r>=2, (int U^r)^{1/r} <= C(meanu + sqrt r ||g_n||_2 + r max g_n + r(n+1)^{2/r} kappa_d(n)) "
        "(n-range widened from the paper's n>=2, same C for both displays); ||g_n||_2 = `l2Norm (green d n)`, max_x g_n = `greenMax`, "
        "E U_n(0) = `meanU`, E u_n(0) = `meanu`; hypotheses 'nonconstant, integer valued, mean zero, exponential moment' = `CriticalLaw nu`; "
        "four extra hypotheses hGrowth, hBernstein, hConcentration, hGreenNorms are the cited results the proof quotes",
    "lem-nearest-one-point":
        "one lemma, three assertions: the moment bound (E U_t(x)^r)^{1/r} <= C(m_t+r) for all t,x,r>=2, m_t <= C log(1/h_t), and h_t decreasing to 0; "
        "Lean is `exists C` (0<C, depending on d only, bound before p) then `forall p in (0,1/4]` with four conjuncts: moment bound with an added "
        "`Integrable`, `meanU <= C log(1/holeProb)` for all t, `Antitone` of h, `Tendsto h atTop (nhds 0)` (h_t ↓ 0 split in two); "
        "setting from the surrounding section, not the lemma: d>=5 (`hd : 5<=d`), eta iid `threePointLaw p` (P(±1)=p, P(0)=1-2p), "
        "m_t = `meanU` at 0, h_t = `holeProb` = P(H_t(0)=1) (were h_t=0, Lean's 1/0=0 would force m_t<=0, so no escape); extra hypothesis `hBernstein`",
    "ext-oriented-stopping-stability":
        "cited input, assumed and not proved; the paper's lines 3199-3203 state no formula (only that BP's cutoff and stability estimates, "
        "with eq:oriented-heat and lem:shift, prove the displayed convergence), so the Lean statement is a reconstruction of the stability step, "
        "not a transcription; it is one Prop: for every probability space carrying a quarter-Brownian B (Var B_t=t/4, B_0=0, a.s. continuous) and every T>0, "
        "IF the rescaled oriented walk (site (z2-z1)/(2 sqrt n), positions at floor(n t_i)) converges to B in finite-dimensional law on [0,T] "
        "(tested on bounded continuous F) THEN for every M>=0, continuous G with |G|<=M and G'_n with |G'_n|<=M converging to G uniformly on [0,T] x R, "
        "every eps>0 has an N with |orientedStoppingSup 2 (k,z |-> G'_n(k/n, scaled z)) floor(nT) 0 - contValue B PB G T| <= eps for n>=N; "
        "the reward is read at elapsed time k/n; the walk's convergence is a hypothesis, and the scenery, white noise and the displayed odometer convergence are not assumed",
    "ext-critical-scale-lower-tail":
        "cited input, assumed and not proved; the paper's lines 1807-1833 (proof of thm:nearest) only say BP's scaling limit and critical-scale lower-tail estimate give "
        "U(1,0)>0 a.s., with no displayed estimate, so the Lean statement (the sibling repository's sealed `critical_toppling`) cannot be checked clause by clause against the paper; "
        "Lean is an implication with antecedents `VarianceScale` and `MultivariateBerryEsseen` (separate ext nodes), then forall 1<=d<=3, nu0>0, M, 0<a<4/(4-d), "
        "`exists c,C>0` (depending on d, nu0, M, a only, bound before nu, t, L) such that for every mean-zero probability nu on R with finite variance >= nu0^2 and "
        "int|z|^3 <= M var^{3/2}, every t>=3 and L>=2 with L^a<=t/2, P(odometer_t(0) <= t^{(4-d)/4}/L) <= C L^{-c} + C*remainder, "
        "remainder = (log t)^{3/4} t^{-1/4} L^{a/4} for d=1,3 and (log t)^{7/4} t^{-1/2} L^{a/2} for d=2; "
        "odometer in the source mass normalization sigma=1+2d*zeta (`centeredMassLaw`), which the repository shows equals u_n(0) of eta=zeta",
    "prop-w-moment":
        "two displays (max_{m<=n}(E|w_m(0)|^r)^{1/r} <= C(sqrt(r kappa_d(n)(E U_n(0)^r)^{1/r}) + r), and (E w*_n(0)^r)^{1/r} <= (n+1)^{1/r} max_{m<=n}(E|w_m(0)|^r)^{1/r}, no constant); "
        "Lean has `exists C` (0<C, d only, bound before nu, theta, n, r, matching 'dimension-dependent') and four conjuncts: added `Integrable` of |w_m(0)|^r for all m<=n and of w*_n(0)^r, "
        "then the two displays, max over m<=n as `⨆ m ∈ Set.Iic n` (values >=0, no junk effect); 'E e^{theta eta(0)^+}<infty' = `Integrable (exp(theta * max k 0)) nu` "
        "with nu an integer probability law; w_m = `wErr`, w*_n = `wStar` (average over the independent walk); integrability of U_n(0)^r is not asserted, and a junk 0 there would only strengthen the claim; extra hypothesis `hBernstein`",
    "lem-pathwise-comparison":
        "two displays (eq:pathwise-error and eq:pathwise-comparison); Lean is a conjunction of exactly those two, "
        "`|U - wErr - uOf| <= wStar` and `|U - uOf| <= 2*wStar`, for every `n : N` and `x`, `U` cast N->R; "
        "extra hypotheses `hd : 1 <= d` and `hstep` (every instruction `omega.2.1 q` is a lattice neighbour of its site, "
        "true almost surely under the stack law), with omega a deterministic realization rather than an a.s. statement; "
        "`wStar` is the walk average of the max over j in range(n+1) taken as an iSup of nonnegative terms (no junk value); "
        "instruction stacks are 0-indexed so I_{y,x}(m) counts j < m",
    "ext-green-gradient":
        "cited input (also proved in the shared library for d >= 2 by the theorem after the frozen block); "
        "paper display has two relations joined by 'hence', Lean states only the first, "
        "`exists C > 0` outside `forall m >= 1, forall y, forall z ~ y`, `|g_m(y) - g_m(z)| <= C(1+|y|)^(1-d)` "
        "with a real power and |y| = graphNorm (l1 distance); the Gamma_m bound is not in the node; "
        "the Prop has no `2 <= d` restriction despite the header comment (true for d = 1, vacuous for d = 0)",
    "lem-critical-density":
        "two assertions (liminf t S_t >= c with c universal, and E U_n(0) >= c log n - C for n >= 2 with the same c); "
        "Lean has `exists c > 0` outside `forall d >= 1, forall nu`, then a conjunction of "
        "`forall^f t, c <= t * S t` (eventual bound, stronger than the liminf) and `exists C > 0, forall n >= 2, "
        "c * log n - C <= meanU`, with C bound after d and nu; hypotheses: nu a probability measure on Z, nonconstant "
        "(`nu{k} != 1`), `|k|` integrable, mean zero, no exponential moment; S = expected survivors started at the origin",
    "prop-nearest-two-hole":
        "one display; Lean asserts it with `exists C > 0` (depends on d only) outside `forall p in (0,1/4]`, "
        "`forall t`, `forall x != z`; the setting of Section 9 is built into the statement: d >= 5, three-point law "
        "P(+-1) = p, P(0) = 1 - 2p, h_t = holeProb = P(H_t(0) = 1); probability is `.toReal` of a probability measure, "
        "exponent (4-d) a real power, |x-z| = graphNorm (x-z); extra hypothesis `hBernstein : External.Bernstein` "
        "(the martingale moment inequality of lem:bernstein, a cited input not in the paper's proposition)",
    "lem-product":
        "one display |Cov_lambda(F,Z)| <= 3 d/dlambda E_lambda F; Lean concludes a conjunction of two: "
        "`Integrable (F*Z)` (extra, makes Cov meaningful) and `|∫FZ - ∫F * ∫Z| <= 3*D`; "
        "the derivative is a hypothesis `hD : HasDerivAt (s => ∫F d restrictLaw(tilt s)) D lam` (two-sided, D real); "
        "'finitely many tilted sites, condition on the rest' is `restrictLaw d N (tiltLaw nu lam) omega0` for finite N "
        "and arbitrary background omega0; lam_1 is encoded by theta > 0, one-sided `Integrable exp(theta k)` "
        "(weaker than the paper's E e^{theta|eta|} < inf), 0 < lam1 < theta, `hnonpos` (tilted mean integrable and "
        "<= 0 for all s in [0,lam1]) and lam in [0,lam1]; F in [0,1] for every omega, nondecreasing under `addAt` at every "
        "site; Z >= 0, integrable, nonincreasing under `addAt`, and `|Z(add)-Z| <= 1` and `|Z(del)-Z| <= 1`; F and Z depend "
        "only on N; 'invariant under relabeling' is formalized as `RelabelInvariant` (symmetric in the present particles "
        "and reading only present particles); measurability of F and Z and integrability of |k| added",
    "ext-binomial-local-clt":
        "cited input; the paper states no formula (only 'the binomial local central limit theorem gives convergence of "
        "the convolved potentials'); Lean is one explicit inequality: `exists C > 0` outside `forall m >= 1, forall j : Z` "
        "with j = m mod 2, `|sqrt m * binomLaw m ((j+m)/2) - 2 exp(-(j/sqrt m)^2/2)/sqrt(2 pi)| <= C/m`; "
        "reindexed to the sign-sum coordinate j = 2k - m of Bin(m,1/2), binomLaw extended by zero outside [0,m]; "
        "the rate C/m is the formalizers' quantitative choice, stronger than the paper's qualitative sentence",
    "ext-linear-field-scaling":
        "cited input, but not the paper's own sentence (which cites BP's argument for joint convergence of (eta_R, "
        "u-bar_R)); Lean is a forall over 1 <= d <= 3 and `CriticalLaw nu`, then an exists of (Omega', Q', W, Z, hZcont) "
        "with a conjunction of eight clauses: W unit-intensity spatial white noise, measurability of W(phi), "
        "pairing identity Z = sqrt(Var) * W(g_t^BM(x,.)) (vacuous: W is unconstrained off test functions), Z(0,.) = 0, "
        "measurability of Z(r,x), covariance Var * int_0^r int_0^s p_{a+b}, convergence of the cutoff interpolated "
        "linear field (chi smooth, compactly supported, in positive times; F bounded continuous on the cutoff "
        "field), cross-covariance E[W(phi)Z(t,x)] = sqrt(Var) * int phi g_t, and a joint convergence of scenery pairings "
        "with the cutoff linear field to (sqrt(Var) W(phi_i), Z); this is BP Prop 4.3 in scenery-retained form, "
        "with limit field sqrt(Var)*W for the paper's calligraphic-W of intensity Var",
    "ext-stopping":
        "cited input (BPRS Thm 3.2; the Lean file also proves it as `Parking.External.stopping`); one display; "
        "Lean states `IsLUB (zdStopValues eta n x) (Parking.u eta n x)` under `forall d>=1, forall eta, forall n, forall x`, "
        "so the sup is asserted as a least upper bound of the set of `E_x sum_{k<tau} eta(X_k)` "
        "over `IsWalkStopping` times of the walk's own path filtration with `tau X <= n` for every path, "
        "including the constant 0; tau ranges over all rules for the fixed eta; E_x is the integral against `siteWalkLaw d x`; "
        "u is `Parking.u` (u_{n+1}=max 0 (eta+walkOp u_n), walkOp = simple random walk average); d>=1 is explicit",
    "lem-exposure":
        "two assertions, two top-level conjuncts, for every d>=1 and every probability measure nu on Z under `law d nu`; "
        "(1) `U_{k+1}` is `G_k`-measurable becomes, for all k>=0 and all x, exists a `G_k`-measurable g with `U_{k+1}(x) =ae g` "
        "(a.e. form, NOT pathwise; `G_k` is `expFiltration d k`, not null-completed); "
        "(2) conditional independence with law P(y,.) of unread instructions becomes a product rule: "
        "for every k, every finite family s of (site, index) and every f, "
        "`E[prod_{q in s} 1{unread, rho_q = f q} | G_k] =ae (prod 1{unread}) * prod kern(q.1, f q)`; "
        "reindexed from 0: paper rho_{j+1}(y) is `omega.2.1 (y,j)`, 'j+1>U_k(y)' is `U omega k y <= j`, kern = 1{neighbour}/(2d); "
        "G_0 = sigma(eta), G_{k+1} = G_k joined with generateFrom {j+1<=U_{k+1}(y), rho_{j+1}(y)=x}; "
        "the data also carry independent uniforms that G_k ignores",
    "cor-critical":
        "one display; Lean has `exists c>0` outside `forall d>=1, forall nu` (c universal), "
        "then hypotheses nu probability on Z, nonconstant (`nu {k} != 1`), integrable |k| "
        "(added so that 'mean zero' is genuine and not a junk integral), mean zero, "
        "then `exists C>0` (may depend on d and nu) outside `forall n>=2`, "
        "and conclusion `max (meanu) (c log n - C) <= meanU`, i.e. E U_n(0) dominates both terms; "
        "meanu = E u_n(0) and meanU = E U_n(0) under `law d nu`",
    "thm-nearest-counterexample":
        "one display; d>=5 fixed first, then `exists p in (0,1/2)`, then `exists c>0`, then `c <= liminf_{t:N}` "
        "of the real probability (values in [0,1], so the liminf is genuine); "
        "law is `threePointLaw p` (P(+-1)=p, P(0)=1-2p) i.i.d. under the stack construction `law d`; "
        "event `HoleCloser` is holeDistance < activeDistance strictly, graph (l^1) distances in N-infinity "
        "with inf over empty = top (immaterial a.s. because holes and active particles both exist a.s.); "
        "carries an EXTRA hypothesis `hBernstein : Parking.External.Bernstein` (cited martingale inequality, assumed) "
        "that the paper's statement does not have",
    "thm-subcritical":
        "three assertions, three top-level conjuncts: (i) `0 < a`; "
        "(ii) the displayed bound, for all k>=1 with `nu {k} != 0` (k in the support), all t:N and every prescribed walk w "
        "(pointwise in w, stronger than the paper's a.s. conditioning): "
        "`survivalGivenWalk d nu k t w <= exp((1/3) int_0^lam1 int |j| d tilt_s) * exp(lam1 (k-1)/3 - a * rangeCard 0 w t)`, "
        "where |R_t| = `rangeCard` counts X_0..X_t and survival is label (0,0) active after round t with its moves set to w, "
        "divided by nu{k}, in the particle-driven construction; "
        "(iii) `exists C>0` (may depend on d, nu, theta, lam1; not t) `forall t`, `S_t <= C * int exp(-a |R_t|) d walkLaw d` "
        "(S in the stack construction, E_0 the walk average), with added integrability of the survivor count; "
        "the standing setting becomes hypotheses: integer-valued nu, integrable |k|, negative mean, `0 < nu (Ioi 0)`, "
        "theta>0 with exp(theta k) integrable, lam1 in (0,theta) with tilt_s of integrable nonpositive mean for every s in [0,lam1] "
        "(lam1 universally quantified, matching 'choose lam1'), and `a = (1/3) int_0^lam1 drift s` "
        "given as a hypothesis, with `drift s = -E_s eta(0)`",
    "prop-oriented-scaling":
        "four assertions (convergence in distribution for every T>0; U(T) =d T^{1/4} U(1); mu = E U(1) in (0,inf); "
        "n^{-1/4} E u_n(0) -> mu) mapped onto Lean conjuncts under `exists (Omega, Q probability, Uc : R -> Omega -> R, mu)`: "
        "measurability of `Uc T` for T>0 (added, so the law is genuine); "
        "convergence via bounded continuous F, `int F(n^{-1/4} uOriented eta (floor(nT)) 0) d orientedLaw 2 nu -> int F(Uc T) dQ`; "
        "`Q.map (Uc T) = Q.map (T^{1/4} * Uc 1)`; "
        "`Integrable (Uc 1)`, `mu = int Uc 1 dQ`, `0 < mu` (this is mu in (0,inf)); "
        "`n^{-1/4} meanuOriented (orientedLaw 2 nu) n -> mu`; "
        "the limit is asserted to exist and is not identified with the proof's construction; d=2 is fixed by `orientedLaw 2`, "
        "with orientedOp f x = (1/d) sum_i f(x-e_i), i.e. 1/2 each; hypothesis `CriticalLaw nu` = probability on Z (integer-valued, "
        "not in the proposition's own text), nonconstant, mean 0, exp(theta|k|) integrable; "
        "carries EXTRA hypotheses `hStability` and `hBinomial` (cited inputs from Step 1) not in the paper's statement",
    "ext-heat-strong-minimum":
        "cited input (classical strong minimum principle; the paper only invokes it in Step 4 at parking.tex:1785-1805 and never states it); "
        "one implication in general form: for every d, open U in R x R^d, v that is C-infinity on U (`ContDiffOn ... (top : N-infinity)`), "
        "v >= 0 on U, and `HasDerivAt (s -> v(s,x)) (contOp d v(s,.) x) s` at every point of U "
        "(contOp = (2d)^{-1} Delta, i.e. the paper's L, so this is d_s v = L v), "
        "then for every (s0,x0) in U with v(s0,x0)=0 and every tau<s0 with (tau,s0] x {x0} in U, "
        "`v(s,x0)=0` for all s in (tau,s0]; the paper's use is the instance v = d_s U on O",
}


def paper_path() -> Path:
    """The paper: the copy pinned in this repository, or `$PARKING_PAPER`."""
    env = os.environ.get("PARKING_PAPER")
    return Path(env) if env else ROOT / "paper" / "parking.tex"


RELATION = re.compile(r"\\leq|\\geq|\\neq|\\subseteq|(?<!\\not)\\in\b|<|>|=")


def paper_units(segment: str) -> int:
    """Assertions in a statement: relations inside displays, plus enumerated items.

    Counting displays alone undercounts, because the paper often puts three
    assertions in one display separated by `\\qquad` -- `lem:max-exit` does.
    Counting relation symbols inside displayed math tracks the real number of
    things asserted.  `\\coloneqq` is a definition, not an assertion, and is not
    counted; nor is anything outside a display."""
    body = []
    for m in re.finditer(r"\\begin\{(?:equation|align|gather)\*?\}(.*?)\\end\{(?:equation|align|gather)\*?\}",
                         segment, re.S):
        body.append(m.group(1))
    for m in re.finditer(r"(?<!\\)\\\[(.*?)(?<!\\)\\\]", segment, re.S):
        body.append(m.group(1))
    n = 0
    for b in body:
        b = re.sub(r"\\text\{[^}]*\}", " ", b)
        b = b.replace("\\coloneqq", " ").replace("\\colon", " ")
        b = re.sub(r"\\begin\{cases\}.*?\\end\{cases\}", " ", b, flags=re.S)
        n += len(RELATION.findall(b))
    n += len(re.findall(r"\\item\b", segment))
    return max(n, 1) if body or "\\item" in segment else 0


def lean_conjuncts(block: str) -> int:
    """Top-level `∧` of the conclusion.

    The conclusion begins after the last `:` that sits at bracket depth zero:
    every binder is inside `(`, `{` or `[`, so its own `:` is at depth one or
    more.  Conjuncts are then the depth-zero `∧` after that point."""
    depth, last_colon = 0, None
    for i, ch in enumerate(block):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == ":" and depth == 0 and not block.startswith(":=", i):
            last_colon = i
    concl = block[last_colon + 1:] if last_colon is not None else block
    depth, n = 0, 1
    for ch in concl:
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == "∧" and depth == 0:
            n += 1
    return n


def main() -> int:
    strict = "--strict" in sys.argv[1:]
    lines = paper_path().read_text(encoding="utf-8").splitlines()
    manifest = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))

    rows, flagged, unreviewed = [], [], []
    for node in manifest.get("nodes") or []:
        src = node["source"]
        rng = re.search(re.escape(paper_path().name) + r":(\d+)-(\d+)", src)
        lab = re.search(r"label ([A-Za-z][A-Za-z0-9:_-]*)", src)
        if not (rng and lab):
            continue
        a, b = int(rng.group(1)), int(rng.group(2))
        segment = "\n".join(lines[a - 1:b])
        text = (ROOT / node["file"]).read_text(encoding="utf-8")
        blk = text[text.index("-- FROZEN-STATEMENT-BEGIN"):text.index("-- FROZEN-STATEMENT-END")]
        p, l = paper_units(segment), lean_conjuncts(blk)
        rows.append((node["id"], lab.group(1), p, l))
        if p > l:
            flagged.append(node["id"])
        if node["id"] not in REVIEWED:
            unreviewed.append(node["id"])

    print(f"{'node':26s} {'label':22s} paper  lean")
    for nid, lab, p, l in rows:
        mark = "  <-- paper asserts more" if p > l else ""
        print(f"  {nid:24s} {lab:22s} {p:5d} {l:5d}{mark}")

    print("\nRecorded correspondence, one line per statement:")
    for nid, _, _, _ in rows:
        print(f"  {nid}: {REVIEWED.get(nid, 'NOT REVIEWED')}")

    if unreviewed:
        print(f"\ncheck_clauses: {len(unreviewed)} statement(s) have no recorded "
              f"correspondence: {', '.join(unreviewed)}", file=sys.stderr)
        return 1
    print(f"\ncheck_clauses: OK ({len(rows)} statements, each read against the paper "
          f"and its correspondence recorded; {len(flagged)} where the count heuristic "
          f"says the paper asserts more, all explained above)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
