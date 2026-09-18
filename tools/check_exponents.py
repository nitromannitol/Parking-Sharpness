"""Compare every exponent in a paper statement with those in its Lean statement.

The exponents `2/3`, `1/3`, `-2/3`, `-1/3` and the `e^{-cR}` tails carry the
content of this paper, and `2/3` versus `1/3` is a transposition that no type
error would catch.  So they are compared directly:
every exponent is extracted from the paper's statement and from the frozen Lean
statement and the two multisets are matched.

Three kinds of difference are expected and are recorded per node rather than
silently ignored:

  notation   the paper writes `\\gamma`, Lean writes `γ`
  general    the paper writes the `d = 2` case as `2/3` and `1/3`; Lean carries
             the general `d/(d+1)` and `1/(d+1)`, which agree at `d = 2`
  split      `thm:return` is one theorem in the paper and three nodes here, so
             each node sees the whole theorem's line range but carries only its
             own display

    python3 tools/check_exponents.py
"""

from __future__ import annotations

import os
import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    sys.exit("check_exponents.py: PyYAML is required (pip install pyyaml)")

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "ledger" / "manifest.yaml"


def paper_path() -> Path:
    env = os.environ.get("PARKING_PAPER")
    return Path(env) if env else ROOT / "paper" / "parking.tex"


# Superscripts that are not exponents of a quantity: set names like `ℤ^d`, the
# inverse in `Δ^{-1}`, the summation limits, and the `θ`-expressions of lem:exp,
# which Lean writes with `Real.exp` rather than with `^`.
NOISE = {"2", "+", "-1", "\Z", "\R", "\infty", "\ast", "\star", "j", "n", "m", "k", "i"}

# A superscript that decorates a symbol instead of raising it to a power: the
# paper's rescaling label `f^{(R)}`, the density label `\sigma^{(\rho)}`, the
# roman decorations `g^{\rm BM}` and `\P^{\rm tr}`, and the transpose star.
DECORATION = re.compile(
    r"^(\\(rm|mathrm|mathbf|mathcal|text|operatorname).*"
    r"|\((\\rho|\\rho\'|R|T|\\varepsilon)\)"
    r"|\*|\\ast|\\star|\\top|\\dagger|\\prime|\'|\\|)$")

# Bases whose superscript is a dimension or a set name, never a power of a
# quantity: `\Z^d`, `\R^d`, `\N^d`, `\T^d`.
SET_BASE = re.compile(r"(\\(Z|R|N|T|mathbb\{[A-Za-z]\})|\bC_{\\rm loc}|\bH)\s*$")

# Per node: exponents present in the paper's line range but legitimately absent
# from this node's Lean statement, with the reason.
EXPECTED_ABSENT: dict[str, dict[str, str]] = {
    "ext-binomial-local-clt": {
        "-3/4": "context: the exponent -3/4 is the prefactor n^{-3/4} of the rescaled-scenery display that opens the range at line 3192, the previous display in the proof of prop:oriented-scaling (formalized by the node prop-oriented-scaling), not part of the statement of `Parking.External.BinomialLocalCLT`; that statement is the binomial local central limit theorem the next sentence invokes, in the quantitative form |sqrt(m) binomLaw m ((j+m)/2) - 2 exp(-(j/sqrt m)^2/2)/sqrt(2 pi)| <= C/m for m >= 1 and j with j - m even, where I read `Parking.binomLaw` (Parking/Support/Oriented.lean:36: choose l j.toNat / 2^l for j >= 0, zero for j < 0) and checked that `-(j / sqrt m) ^ 2 / 2` parses as -((j/sqrt m)^2)/2; the paper writes no formula for this step, so the error term C/m is the library's cited-input choice (Lawler-Limic Theorem 2.1.1)",
    },
    "ext-critical-scale-lower-tail": {
        "1": "context: the superscript is the ell^1 in 'supported in the ell^1-ball of radius r' (parking.tex line 1813), prose in the proof of thm:nearest where the cited critical-scale lower-tail estimate is applied to get U(1,0) > 0 almost surely; it is not part of the cited statement formalized here. Reading: the Lean node is the one cited theorem BP thm:critical-toppling (sandpile.tex:1696-1720), stated as VarianceScale -> MultivariateBerryEsseen -> forall d in [1,3], nu0 > 0, M, a in (0, 4/(4-d)), exists c C > 0 (bound before the law, depending only on d, a, nu0, M as in the source), forall probability measures nu on R that are mean zero with 0 < evariance < top, integrable |z|^3, nu0^2 <= evariance and E|z|^3 <= M * variance^(3/2), forall t : N and real L with 3 <= t, 2 <= L, L^a <= t/2, centeredMassLaw d nu {sigma | odometer sigma t 0 <= t^((4-d)/4)/L} <= ofReal(C L^(-c) + C * lowerTailRemainder d t L a); the paper's single displayed bound P(u_t(0) <= t^{(4-d)/4}/L) <= C L^{-c} + C * (cases) is one Lean conclusion, and the two source hypotheses VarianceScale and MultivariateBerryEsseen are carried as explicit antecedents (their own nodes); the source's standing d <= 3, iid mean-zero, 0 < Var < infinity, E|zeta|^3 < infinity are the Lean d range and the hypotheses on nu; the exponents in the Lean statement (t^((4-d)/4), L^a, L^(-c), 3/2) match the source, and the case exponents (log t)^(3/4) t^(-1/4) L^(a/4) for d in {1,3} and (log t)^(7/4) t^(-1/2) L^(a/2) for d = 2 sit in the definition Parking.CriticalScale.lowerTailRemainder, read and matching the source cases; Parking.CriticalScale.odometer/relax (u_{n+1} = (zeta + P u_n)^+ after the mass shift sigma = 1 + 2d zeta, division by 2d built in) and centeredMassLaw (iidLaw of nu pushed forward by z -> 1 + 2 d z) were read and match the divisible recursion and the iid scenery.",
    },
    "ext-green-gradient": {
        "2-2d": "the display eq:green-gradient asserts two relations, the gradient bound and, introduced by \"hence\", Gamma_m(y) <= C(1+|y|)^{2-2d}; this node states only the gradient bound, which is the only one the development consumes (Parking/Support/SpatGreenShift.lean).  Recorded in CORRESPONDENCE.md.",
        "-(d+1)/2": "context: this exponent occurs only in the proof sketch inside lines 1019-1030 (the bound sum_{j>=0} (j+1)^{-(d+1)/2} exp(-c|y|^2/(j+1)) obtained from the first-difference local CLT and Gaussian bound of Lawler-Limic), which is the paper's derivation of the cited estimate and not the statement; the Lean Prop Parking.External.GreenGradient d is the gradient bound itself: exists C, 0 < C (bound before m, y, z, so depends only on d) such that for all m >= 1, all y z : Site d with z in LatticeProb.nbrFinset y, |Parking.green d m y - Parking.green d m z| <= C * (1 + graphNorm y)^(1 - d) with a real power; definitions read: Parking.green d m = sum_{j<m} heat d j with heat d 0 = delta_0 and heat d (j+1) = walkOp (heat d j), i.e. P^j(0,.), so green is the truncated Green function g_m (Parking/Support/Walk.lean); graphNorm y = sum_i |y_i|, the graph distance from the origin fixed at parking.tex:588-601; the Prop carries no 2 <= d hypothesis (it is discharged by Parking.External.greenGradient only for 2 <= d and used only under 2 <= d in Frozen/GammaSum.lean, matching the paper's use of the local CLT for d >= 2).",
    },
    "ext-linear-field-scaling": {
        "d+2": "context: the superscript is the O(R^{d+2}) count of space-time mesh points in the union bound over eq:discrepancy-tail that transfers the cited joint convergence of (eta_R, ubar_R) to Ubar_R, in the proof of prop:spatial-scaling (parking.tex line 1747); it is not part of the cited statement formalized here, which is BP Proposition 4.3 (joint convergence of the scenery pairings with the rescaled interpolated LINEAR field Z_R^lin) and involves no mesh-point count. Reading: the paper range is the proof-step prose 'the argument ... with the time variable and scenery retained gives the joint convergence of (eta_R, ubar_R); its estimates are uniform on compact time intervals', which Lean transcribes as one external Prop with hypotheses d in [1,3] and nu with Parking.CriticalLaw (integer valued, nonconstant, mean zero, exponential moment: the paper's iid hypotheses) and, in the existential, a probability space (Omega', Q'), a unit-intensity white noise W (IsSpatialWhiteNoise d 1), and a jointly continuous Z vanishing at time 0 with the pairing identity Z t x = sqrt(Var) * W(g_t^BM(x,.)) for t >= 0, the covariance Var * int_0^r int_0^s contHeatKernel d (a+b) x y da db (Chapman-Kolmogorov reduction of Var * <g_r, g_s>), the cross-covariance E[W(phi) Z(t,x)] = sqrt(Var) * int phi(y) g_t(x,y) dy, a weak-convergence clause for the cutoff field (every IsSpaceTimeTest chi, every bounded continuous F, via cutoffBC of linHatInterp, law Parking.law d nu, R -> infinity) and a joint clause for (scenePair w R (phi i))_i with the cutoff field, limit (sqrt(Var) * W(phi i), cutoff Z); the paper's mean-zero white noise of intensity Var eta(0) is Lean's sqrt(Var) times a unit-intensity W; the paper's ubar_R is not in the Lean statement, it is recovered downstream from the linear field through the optimal-stopping representation and the extended continuous mapping theorem (a cited-result modelling choice, not a dropped conclusion); the Lean exponents -d/2 and d/2-2 lie in the definitions Parking.scenePair (R^{-d/2} sum eta(y) phi(y/R), read, matches the paper's <eta_R,phi>) and Parking.linHatInterp (R^{d/2-2} times the interpolation of linPotential, V_{n+1} = eta + P V_n, i.e. sum_z g_n(x,z) eta(z), read, matches BP's Z_R^lin), and the contHeatKernel prefactor (4 pi t/(2d))^{-d/2} is BP eq. (14), read.",
    },
    "ext-multivariate-berry-esseen": {
        "1": "context: the only superscript 1 in the range is the ell^1-ball in the proof of Theorem nearest (line 1813), prose of a proof that cites [BP]; it is not part of what `Parking.External.MultivariateBerryEsseen` states (the orthant form of Raic Theorem 1.1 used at sandpile.tex:1770-1782, with error C m^{1/4} Var^{3/2} sum |a(i)|^3, whose exponents 1/4, 3/2 and 3 all appear in the Lean statement), carried as an antecedent of `ext-critical-scale-lower-tail`, and parking.tex:1807-1833 displays no relation that this node states",
    },
    "ext-spatial-fixed-time-tightness": {
        "d+2": "context: R^{d+2} is the size of the space-time mesh in the paper's union-bound sentence (parking.tex 1745-1748, transferring the convergence of u_R to U_R through eq:discrepancy-tail), which is prose of the proof step and not part of this External; the External states only the fixed-time, spatial equicontinuity in probability of Parking.barDivisible (d in 1..3, Parking.CriticalLaw nu, T>0, compact K', eps, eps'; exists delta>0 and R0 such that for R>=R0 the Parking.law probability that the oscillation over pairs at distance <= delta exceeds eps is <= eps'), read off BP Theorem 1.3(i)(b); the union bound with the R^(d+2) mesh count is carried out in Parking/Support/SpatialVanishingDistance.lean (mesh_card_le) for the vanishing-distance clause of Parking.Frozen.spatial_scaling",
    },
    "ext-spatial-odometer-scaling": {
        "d+2": "context: R^{d+2} is the size of the space-time mesh in the paper's union-bound sentence (parking.tex 1745-1748, transferring convergence from u_R to U_R), prose of the proof step and not part of this External; the External is the sentence just before it, BP Theorem 1.3(i)(b) with time and scenery retained (joint finite-dimensional convergence of (scenePair, barDivisible) to (W, Uc) at positive times, the Brownian representation of Uc through Parking.contUc, and space-time equicontinuity in probability of barDivisible on compacts of positive time), whose exponents d/2-2 and -d/2 sit inside the definitions Parking.barDivisible and Parking.scenePair, which I read and which match; the union bound with the R^(d+2) mesh count is proved in Parking/Support/SpatialVanishingDistance.lean (mesh_card_le) and feeds the vanishing-distance clause of Parking.Frozen.spatial_scaling",
    },
    "ext-spatial-stopping-stability": {
        "d+2": "context: R^{d+2} is the size of the space-time mesh in the paper's union-bound sentence (parking.tex 1745-1748), prose of the proof step and not part of this External, whose Lean statement contains no exponent at all; the External states only the stability of the discrete optimal-stopping value Parking.stoppingSup against Parking.spatialContValue under uniform convergence of rewards bounded by M on [0,T] x (Fin d -> R), with the walk's finite-dimensional convergence to Brownian motion as a hypothesis, which is the stability estimate the paper's sentence 'its estimates are uniform on compact time intervals' cites; the R^(d+2) mesh count is used in Parking/Support/SpatialVanishingDistance.lean (mesh_card_le) for the vanishing-distance clause of Parking.Frozen.spatial_scaling",
    },
    "ext-srw-local-clt": {
        "d+2": "context: R^{d+2} is the size of the space-time mesh in the paper's union-bound sentence (parking.tex 1745-1748), prose of the proof step and not part of this External; the External is BP equation (25), the uniform local CLT for srwHeat on delta R^2 <= l <= T R^2, |x-y| <= C0 R, with the factor 2 for parity and the kernel Parking.External.contHeatKernel (its exponent -d/2 is inside that definition, which I read: (4 pi t/(2d))^(-d/2) exp(-d|x-y|^2/(2t)), generator Laplacian/(2d)); the R^d appearing in it is the lattice-scaling factor R^d, unrelated to the mesh count; the mesh count itself is bounded in Parking/Support/SpatialVanishingDistance.lean (mesh_card_le)",
    },
    "ext-stopping": {
        "\\Z^d": "notation: the paper's Z^d in eta in R^{Z^d} and x in Z^d is Lean's Parking.Site d (LatticeProb.Site d = Fin d -> Z), so eta : Site d -> R and x : Site d; the paper makes one assertion (the displayed equality u_n(x) = sup over stopping times sigma <= n of E_x sum_{j<sigma} eta(X_j)) and the Lean conclusion is one assertion IsLUB (LatticeProb.Graph.Zd.zdStopValues eta n x) (Parking.u eta n x), the supremum written as a least upper bound so that an unbounded or unattained supremum cannot satisfy it through a junk value; definitions read: Parking.u (Parking/Basic.lean) is u_0 = 0, u_{n+1} = max 0 (eta + walkOp u_n), the paper's P-normalized odometer (the paper's own remark that BPRS Theorem 3.2 is multiplied by 2d is already absorbed); zdStopValues (LatticeProb/Graph/ZdRepresentation.lean) is the set of integrals over siteWalkLaw d x (law of the nearest-neighbour walk from x, incLaw steps uniform on the 2d neighbours) of sceneryPartialSum eta (tau X) X over tau : (N -> Site d) -> N with IsWalkStopping tau (tau X = k is settled by X j, j <= k, the natural filtration) and tau X <= n for every path X, tau chosen after eta is fixed so the rule may depend on eta, and the constant rule tau = 0 (sigma = 0) is allowed; hypotheses d >= 1, every eta, every n : N (so n >= 0), every x, all bound inside the Prop; Lean adds nothing beyond d >= 1.",
        "\u03c3-1": "notation: the paper's sum_{j=0}^{sigma-1} eta(X_j) is Lean's LatticeProb.Graph.Zd.sceneryPartialSum eta (tau X) X = sum over k in Finset.range (tau X) of eta (X k), whose indices are exactly 0,...,tau X - 1 and which is the empty sum when tau X = 0, so the upper limit sigma-1 is carried by Finset.range; the paper's stopping time sigma is Lean's tau; the reward is integrated against siteWalkLaw d x as E_x.",
    },
    "ext-u-concentration": {
        "1/r": "notation: the paper's moment order r (real, r >= 2) is Lean's q : R with 2 <= q, so (E|v_n(0)-E v_n(0)|^r)^{1/r} is (integral of |kSol r K eta n 0 - integral of kSol r K eta' n 0 d(iidLaw d nu)| ^ q d(iidLaw d nu)) ^ (1 / q) with real powers; Lean's own r : N is a different variable, the range of the kernel in IsLatticeKernel r K; the paper makes one assertion (the displayed inequality) and Lean's conclusion is that one inequality, under exists C, 0 < C bound before n and q, so C depends only on d, the range r, K, nu and theta and not on n or q, as in the paper; definitions read in Parking/Support/Kernel.lean and matching: IsLatticeKernel r K = nonnegative, supported within sup-distance r, rows sum to 1 over boxFinset y r, invariant under all translations (the paper's finite-range translation-invariant transition kernel); kIter = K^j(0,.) by the recursion kIter (j+1) x = sum_y kIter j y * K y x; kGreen r K n = sum_{j<n} kIter j = g_n^K; kSol = v_0 = 0, v_{n+1} = max 0 (eta + K v_n) with (K f)(x) = sum_y K x y * f y; l2Norm = sqrt of the tsum of squares (finitely supported) and supAbs = iSup of |f x|; hypotheses in the Prop are d >= 1, IsLatticeKernel r K, nu a probability measure on R, and exp(theta*|z|) nu-integrable for a given theta > 0 (equivalent to 'for some theta > 0' since C is chosen after theta), n >= 1 and q >= 2 bound after C; the law of eta is LatticeProb.iidLaw d nu, the i.i.d. field with one-site law nu; Lean adds d >= 1 and the probability hypothesis and leaves out nothing of the paper's statement.",
    },
    "ext-variance-scale": {
        "1": "context: the only superscript 1 in the range is the ell^1-ball in the proof of Theorem nearest (line 1813), prose of a proof that cites [BP] for the critical-scale lower-tail estimate; it is not part of what `Parking.External.VarianceScale` states (the finite-time variance scale, the membrane correlation bound and the d=4 window bounds in Green-kernel form, transcribed from sandpile.tex:1117-1240 and carried as an antecedent of `ext-critical-scale-lower-tail`), and parking.tex:1807-1833 displays no relation that this node states",
    },
    "lem-range-lower": {
        "|R_t|-1": "notation: the paper's |R_t| - 1 with R_t = {X_0,...,X_t} is Lean's Parking.rangeCard (0 : Site d) p t - 1 in the exponent of (nu {j : Z | 0 <= j}).toReal (the paper's P(eta(0) >= 0)); Parking.rangeCard (Parking/Support/Range.lean:30, read) is the card of the image of j -> walkPath 0 p j over Finset.range (t+1), and the natural-number subtraction is exact because the image contains X_0 so rangeCard >= 1; E_0 is the integral against Parking.walkLaw d, the law of the direction sequence of the walk from 0; the paper makes two assertions (P(tau_1 > t | eta(0)=k) >= E_0[...], and 'consequently' S_t >= E[eta(0)^+] E_0[...]) and the Lean conclusion has three conjuncts in order: (1) for each t the range power is integrable against walkLaw d (added by Lean so that E_0 is not a junk integral); (2) for each k >= 1 with nu {k} != 0 and each t, the integral is <= Parking.survivalGiven d nu k t, read as P(eta(0)=k and label (0,0) active after t rounds) / P(eta(0)=k), i.e. P(tau_1 > t | eta(0)=k) with particle 1 the label (0,0); (3) for each t, (integral of max k 0 d nu) * integral <= Parking.S (Parking.law d nu) t, with S = expectation of the number of the (eta 0).toNat particles at the origin still active after round t, the paper's S_t; the paper's standing hypotheses (integer valued as nu on Z, finite first moment as Integrable |k|, negative mean, P(eta(0) > 0) > 0 as 0 < nu (Ioi 0), exp moment for some theta > 0) are explicit hypotheses of the theorem together with d >= 1 and IsProbabilityMeasure nu, and the proof does not read the last three (noted in the file); conditioning on eta(0)=k is division by (nu {k}).toReal.",
    },
    "lem-w-martingale": {
        "n-1": "notation: the upper limit of the paper's sum_{s=1}^{n-1} in eq:qv is Lean's Finset.Icc 1 (n - 1) with natural subtraction, exact because hn : 2 <= n, and the subscripts s-1 in A_{s-1} and n-s in Gamma_{n-s} are Lean's (s - 1) and (n - s), exact for 1 <= s <= n-1; the paper's statement is an existence claim followed by the identity eq:qv, and the Lean conclusion is exists F : N -> MeasurableSpace (Data d) and xi : N -> Data d -> R with ten conjuncts in order: F monotone; each F i at most the ambient sigma algebra; xi i measurable for F (i+1); xi i integrable (these four are the structure the paper leaves implicit in 'filtration' and 'random variables'); xi i eventually zero a.s. (the paper's 'only finitely many nonzero a.s.'); wErr omega n 0 = tsum_i xi i omega a.s. (w_n(0) = sum_i xi_i; wErr in Parking/Support/Error.lean is read and is the recursion eq:error-recursion with w_0 = 0, using walkOp and sum over nbrFinset x of arrivals minus U/(2d)); E[xi i | F i] = 0 a.e.; |xi i omega| <= Parking.greenIncrement d n for every omega (greenIncrement, Support/Walk.lean, read: sup over m in Iio n, y, z in nbrFinset y of |green d m z - walkOp (green d m) y|, the paper's max_{m<n} max_y max_{z~y}); summability of the series of conditional variances and, for each s, of y -> A omega (s-1) y * gamma d (n-s) y, added so that no tsum is a junk value; and the a.e. identity tsum_i E[xi i ^ 2 | F i] = sum_{s in Icc 1 (n-1)} tsum_y (A omega (s-1) y) * gamma d (n-s) y (eq:qv); reindexing: the paper's i >= 1 is Lean's i >= 0, with the paper's xi_i = Lean's xi (i-1) and the conditioning sigma algebra of xi i in Lean being F i, which under F_Lean i = F_paper i is the paper's E[xi_i | F_{i-1}] and adaptedness of xi_i to F_i (the file docstring's gloss 'the paper's F_{i-1} is F i' is off by one relative to the statement, harmless since F is existentially quantified); A omega t y is A_t(y) (active count, Basic.lean) and gamma d m y is Gamma_m(y) read at Support/Walk.lean; hypotheses d >= 1, nu a probability measure on Z, 2 <= n, all bound before the existence.",
    },
    "prop-resolvent": {
        "3": "definition: the exponent 3 is the power of Lambda in eq:range-threshold (a^{-2} Lambda^3 for d=1, a^{-1} Lambda^3 for d=2, a^{-1} Lambda^2 for d>=3), which the Lean statement takes from `Parking.resolventThreshold` (Parking/Support/Near.lean:50); I read it: C times (a^(-2:R) * Real.log (Real.exp 1 / a) ^ (3:N) if d = 1, a^(-1) * Real.log (Real.exp 1 / a) ^ (3:N) if d = 2, a^(-1) * Real.log (Real.exp 1 / a) ^ (2:N) otherwise), with Lambda = log(e/a) spelled Real.log (Real.exp 1 / a) and the same C as the pointwise bound, so it matches the paper case by case; the gate sees `3:N` in the unfolded definition against the paper's `3`, which is the same exponent; the paper's two assertions (pointwise bound in three cases, tail sum at most one) are the two Lean conjuncts after the positivity of c and C, the second adding Summable of the truncated series",
    },
    "prop-spatial-scaling": {
        "d": "notation: the paper's superscript d in Z^d, R^d and C_c^infty(R^d) is the ambient dimension, spelled in Lean as Parking.Site d (= Fin d -> Z) for the lattice and (Fin d -> R) for R^d, with d bound as (d : Nat), 1 <= d, d <= 3 (the paper's d<=3 with d>=1 implicit); the exponents d/2-2 and -d/2 that are present sit inside the definitions Parking.barOdometer and Parking.barDivisible (R^((d:R)/2-2) times U resp. uOf at floor(s R^2), floor(R x) via Parking.latticePoint) and Parking.scenePair and Parking.signedPair (R^(-(d:R)/2) times the sum over y of the summand times phi(y/R), with A and H taken at floor(R^2)), all of which I read and which match the paper's definitions",
    },
    "thm-subcritical": {
        "\u03bb_1": "notation: lambda_1 is the theorem variable `lam\u2081` (hypotheses `0 < lam\u2081`, `lam\u2081 < \u03b8`, and the tilted-mean condition `hnonpos` on [0, lam\u2081]), appearing in the paper's e^{lambda_1(k-1)/3 - a|R_t|} as Lean's `Real.exp (lam\u2081 * ((k : \u211d) - 1) / 3 - a * (Parking.rangeCard (0 : Parking.Site d) w t : \u211d))` and as the upper limit of the two interval integrals; |R_t| is `Parking.rangeCard`, which I read in Parking/Support/Range.lean (cardinality of the image of `walkPath` over `Finset.range (t + 1)`), and the prefactor exp{(1/3) int_0^{lambda_1} E_lambda|eta(0)| d lambda} is the first `Real.exp` factor over `Parking.tiltLaw \u03bd s`; the paper's three assertions (a > 0; eq:range-upper for every t, every k >= 1 with P(eta(0)=k) > 0; S_t <= C E_0 e^{-a|R_t|}) are the three Lean conjuncts in order, the second quantified over every prescribed walk `w` (stronger than conditioning on X_0..X_t alone, since the right side depends on w only through the range up to t), the third adding Integrable of `survivorsFrom` and taking C independent of t",
    },
}


GREEK = {"\\alpha": "α", "\\beta": "β", "\\gamma": "γ", "\\delta": "δ",
         "\\theta": "θ", "\\kappa": "κ", "\\lambda": "λ", "\\rho": "ρ",
         "\\sigma": "σ", "\\tau": "τ", "\\varepsilon": "ε", "\\eta": "η"}


def top_level_sum(e: str) -> bool:
    """True when `e` has a `+` or `-` outside every bracket, so that dropping a
    wrapping parenthesis after a minus sign would change what it means."""
    depth = 0
    for j, ch in enumerate(e):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch in "+-" and depth == 0 and j > 0:
            return True
    return False


def canon(e: str) -> str:
    """One spelling for an exponent, applied to the paper and to Lean alike.

    `-(2 - d/2)` and `-2 - d/2` are different numbers, so the parenthesis after
    a minus sign is kept whenever the operand is itself a sum; it is dropped
    only when it is redundant, which is what makes the two sides comparable.
    """
    for k, v in GREEK.items():
        e = e.replace(k, v)
    e = re.sub(r"\\(cdot|times|,|!|;|\s)", "", e)
    e = re.sub(r"[\s*]", "", e)
    for _ in range(3):
        e = re.sub(r":ℝ$", "", e)
        m = re.fullmatch(r"\((.*)\)", e)
        if m and not top_level_sum(m.group(1)):
            e = m.group(1)
        if e.startswith("-(") and e.endswith(")") and not top_level_sum(e[2:-1]):
            e = "-" + e[2:-1]
        e = re.sub(r":ℝ$", "", e)
    return e


def balanced(s: str, i: int, op: str, cl: str) -> str | None:
    depth = 0
    for j in range(i, len(s)):
        if s[j] == op:
            depth += 1
        elif s[j] == cl:
            depth -= 1
            if depth == 0:
                return s[i + 1:j]
    return None


DECL_START = re.compile(
    r"^(noncomputable\s+)?(private\s+|protected\s+)?"
    r"(def|abbrev|theorem|lemma|instance|structure|inductive|class|namespace|end|open|variable|@\[|/-)")


def definition_bodies() -> dict[str, str]:
    """Every `def` in `Sandpile/`, by fully qualified name, with its body.

    An exponent of a paper statement often sits in a definition the statement
    names -- an exponent of the paper often lives in a definition -- so the text a
    statement is compared against is the frozen block together with the bodies
    of the definitions it mentions.
    """
    bodies: dict[str, str] = {}
    for path in sorted((ROOT / "Parking").rglob("*.lean")):
        lines = path.read_text(encoding="utf-8").splitlines()
        i = 0
        while i < len(lines):
            m = re.match(r"^(noncomputable\s+)?def\s+([A-Za-z_][A-Za-z0-9_.']*)", lines[i])
            if not m:
                i += 1
                continue
            name = m.group(2)
            j = i + 1
            while j < len(lines) and not DECL_START.match(lines[j]):
                j += 1
            bodies[name] = "\n".join(lines[i:j])
            bodies[name.split(".")[-1]] = bodies[name]
            i = j
    return bodies


def with_definitions(blk: str, bodies: dict[str, str]) -> str:
    """The frozen block plus the body of each definition it names."""
    out = [blk]
    for name in sorted(set(re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", blk))):
        # a statement writes the qualified `Parking.nearRate`; the declaration
        # inside `namespace Parking` writes the short name
        body = bodies.get(name) or bodies.get(name.split(".")[-1])
        if body is not None and body not in out:
            out.append(body)
    return "\n".join(out)


def paper_exponents(seg: str) -> tuple[set[str], bool]:
    """The exponents of the segment, and whether it contains an exponential.

    A superscript is not an exponent when its base is a set name (`\\Z^d` is a
    lattice, not a power) and when it decorates rather than raises (`f^{(R)}`).
    A superscript on `e` is an exponential: Lean writes it `Real.exp`, not `^`,
    so it is reported separately and checked by name instead of by text.
    """
    out, exponential = [], False
    for m in re.finditer(r"\^", seg):
        i = m.end()
        if i >= len(seg):
            continue
        if seg[i] == "{":
            g = balanced(seg, i, "{", "}")
            if g is None:
                continue
        else:
            g = seg[i]
        base = seg[:m.start()]
        if SET_BASE.search(base):
            continue
        if re.search(r"(^|[^A-Za-z\\])e\s*$", base):
            exponential = True
            continue
        out.append(g)
    cleaned = set()
    for e in out:
        e = re.sub(r"\s|\\,|\\!|\\bigl|\\bigr", "", e)
        # `^{}_{\rm loc}` and friends leave a brace-wrapped decoration behind
        while e.startswith("{") and e.endswith("}"):
            e = e[1:-1]
        if e and not DECORATION.match(e):
            cleaned.add(canon(e))
    return cleaned - NOISE, exponential


def lean_exponents(blk: str) -> set[str]:
    out = []
    for m in re.finditer(r"\^\s*", blk):
        i = m.end()
        if i >= len(blk):
            continue
        if blk[i] == "(":
            g = balanced(blk, i, "(", ")")
            if g is not None:
                out.append(g)
        else:
            g = re.match(r"[A-Za-zγβ0-9]+", blk[i:])
            if g:
                out.append(g.group(0))
    cleaned = set()
    for e in out:
        e = re.sub(r"\(\s*([a-zA-Zβγ])\s*:\s*ℝ\s*\)", r"\1", e)
        e = re.sub(r"\(\s*(\d+)\s*:\s*ℝ\s*\)", r"\1", e)
        cleaned.add(canon(e))
    return cleaned - {"2"}


def main() -> int:
    lines = paper_path().read_text(encoding="utf-8").splitlines()
    manifest = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))
    unexplained: list[tuple[str, list[str]]] = []
    compared = 0
    bodies = definition_bodies()

    for node in manifest.get("nodes") or []:
        rng = re.search(re.escape(paper_path().name) + r":(\d+)-(\d+)", node["source"])
        if not rng:
            continue
        a, b = int(rng.group(1)), int(rng.group(2))
        seg = "\n".join(lines[a - 1:b])
        text = (ROOT / node["file"]).read_text(encoding="utf-8")
        blk = text[text.index("-- FROZEN-STATEMENT-BEGIN"):
                   text.index("-- FROZEN-STATEMENT-END")]
        pe, pexp = paper_exponents(seg)
        le = lean_exponents(with_definitions(blk, bodies))
        if pexp and not re.search(r"Real\.exp|rexp|Real\.log",
                                  with_definitions(blk, bodies)):
            unexplained.append((node["id"], ["e^{...}: the paper's statement has an "
                                            "exponential and the Lean statement has no `Real.exp`"]))
        compared += 1
        allowed = EXPECTED_ABSENT.get(node["id"], {})
        missing = [e for e in sorted(pe) if e not in le and e not in allowed]
        print(f"  {node['id']:24s} paper {sorted(pe)}")
        print(f"  {'':24s} lean  {sorted(le)}")
        for e in sorted(pe):
            if e in allowed:
                print(f"  {'':24s}   {e}: {allowed[e]}")
        if missing:
            unexplained.append((node["id"], missing))

    if unexplained:
        print("\ncheck_exponents: a paper exponent has no counterpart in Lean:",
              file=sys.stderr)
        for nid, ms in unexplained:
            print(f"  {nid}: {', '.join(ms)}", file=sys.stderr)
        return 1
    print(f"\ncheck_exponents: OK ({compared} statements; every paper exponent "
          f"appears in its Lean statement or is explained above)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
