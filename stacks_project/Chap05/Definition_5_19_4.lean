module

public import Mathlib.Topology.Inseparable
import StacksCheckRecall

@[expose] public section

/- Definition 5.19.4 (1): `SpecializingMap` is Mathlib's canonical predicate
for lifting specializations.  Its definition has the source lifting
quantifiers; continuity is orthogonal extra setup. -/
@[stacks 0063 "specializations lift along a continuous map"]
#check SpecializingMap

/- Definition 5.19.4 (2): `GeneralizingMap` is Mathlib's canonical predicate
for lifting generalizations.  Its definition has the source lifting
quantifiers; continuity is orthogonal extra setup. -/
@[stacks 0063 "generalizations lift along a continuous map"]
#check GeneralizingMap
