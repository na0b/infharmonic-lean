/- Run with `lake env lean Axioms.lean` after `lake build`.
Every result below should depend only on `propext`, `Classical.choice` and `Quot.sound`. -/
import InfHarmonic

#print axioms MainEstimate
#print axioms InteriorC1
#print axioms Liouville
