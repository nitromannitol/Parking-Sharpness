import Parking.MainTheorems

/-!
# Axioms audit

Building this module prints the axiom dependencies of the eight main theorems of
`Parking/MainTheorems.lean`.  Each must report exactly the three standard foundational axioms
of Mathlib: `propext`, `Classical.choice`, `Quot.sound`.

The results the paper cites without proof are not axioms here: each is a `Prop` in
`Parking/External/` taken as an explicit hypothesis of the theorems that use it, so it
appears in the statement, not in this list.

This file is not imported by the library root; the report runs when it is built explicitly
(`lake build Parking.Meta.AxiomsAudit`), as continuous integration does on every push.
-/

#print axioms Parking.subcritical_tail
#print axioms Parking.master
#print axioms Parking.growth
#print axioms Parking.trichotomy
#print axioms Parking.nearest
#print axioms Parking.nearest_counterexample
#print axioms Parking.near
#print axioms Parking.oriented_walk
