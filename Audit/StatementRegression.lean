import Audit.Support.Statements
import Audit.SubcriticalTail.Solution
import Audit.Master.Solution
import Audit.Growth.Solution
import Audit.Trichotomy.Solution
import Audit.Nearest.Solution
import Audit.NearestCounterexample.Solution
import Audit.Near.Solution
import Audit.OrientedWalk.Solution

/-!
# Statement regression for the comparator solutions

For each audited theorem, checks that the type of the solution theorem is
exactly the proposition elaborated in the challenge environment
(`Audit/Support/Statements.lean`), and that it mentions no constant of the
repository namespace `Parking` or of the libraries `LatticeProb` and
`Sandpile`.  Building this module prints one line per theorem; any mismatch
is an error.  This is a local proxy for the statement-identity part of
`leanprover/comparator`.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (thm, stmt) in [
    (`ParkingAudit.subcritical_tail, `ParkingAudit.Statements.subcritical_tail),
    (`ParkingAudit.master, `ParkingAudit.Statements.master),
    (`ParkingAudit.growth, `ParkingAudit.Statements.growth),
    (`ParkingAudit.trichotomy, `ParkingAudit.Statements.trichotomy),
    (`ParkingAudit.nearest, `ParkingAudit.Statements.nearest),
    (`ParkingAudit.nearest_counterexample, `ParkingAudit.Statements.nearest_counterexample),
    (`ParkingAudit.near, `ParkingAudit.Statements.near),
    (`ParkingAudit.oriented_walk, `ParkingAudit.Statements.oriented_walk)] do
    let some ti := env.find? thm | throwError "missing theorem {thm}"
    let some si := env.find? stmt | throwError "missing statement {stmt}"
    let some v := si.value? | throwError "statement {stmt} has no value"
    unless ti.levelParams == si.levelParams do
      throwError "{thm}: universe parameters differ from the challenge statement"
    -- A `def` abstracts the proofs inside its value into auxiliary lemmas
    -- (`ParkingAudit.Statements.*._proof_i`, shared between declarations);
    -- put their proof terms back before comparing.
    let v := v.replace fun e => match e with
      | .const n ls =>
        if (`ParkingAudit.Statements).isPrefixOf n && n.isInternal then
          (env.find? n).bind fun ci => (ci.value? (allowOpaque := true)).map (·.instantiateLevelParams ci.levelParams ls)
        else none
      | _ => none
    let v ← liftCoreM (Core.betaReduce v)
    let ty ← liftCoreM (Core.betaReduce ti.type)
    unless ty == v do
      throwError "{thm}: the solution statement differs from the challenge statement"
    for c in ti.type.getUsedConstants do
      if (`Parking).isPrefixOf c || (`LatticeProb).isPrefixOf c || (`Sandpile).isPrefixOf c then
        throwError "{thm} mentions the repository or library constant {c}"
    logInfo m!"{thm}: identical to the challenge statement; no repository or library constant"

#print axioms ParkingAudit.subcritical_tail
#print axioms ParkingAudit.master
#print axioms ParkingAudit.growth
#print axioms ParkingAudit.trichotomy
#print axioms ParkingAudit.nearest
#print axioms ParkingAudit.nearest_counterexample
#print axioms ParkingAudit.near
#print axioms ParkingAudit.oriented_walk
