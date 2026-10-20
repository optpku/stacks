module

public import ReasLib.CategoryTheory.Sites.QuasiCompact.Basis
import StacksCheckRecall

@[expose] public section

/- Situation 18.30.5 (1): every site object is covered by objects in the selected basis. -/
@[stacks 0937 "(1)"]
#check @CategoryTheory.Coverage.HasEnoughObjectsWithProperty

/- Situation 18.30.5 (2): every object in the selected basis is quasi-compact. -/
@[stacks 0937 "(2)"]
#check @CategoryTheory.Coverage.Basis.IsQuasiCompact

/- Situation 18.30.5 (3): basis covers have pairwise pullbacks with quasi-compact overlap
objects. -/
@[stacks 0937 "(3)"]
#check @CategoryTheory.Coverage.Basis.HasQuasiCompactOverlaps

/- Sieve-saturated specializations remain available for clients whose input is already a
Grothendieck topology rather than a chosen coverage. -/
#check @CategoryTheory.GrothendieckTopology.HasEnoughObjectsWithProperty
#check @CategoryTheory.GrothendieckTopology.Basis.IsQuasiCompact
#check @CategoryTheory.GrothendieckTopology.Basis.HasQuasiCompactOverlaps
