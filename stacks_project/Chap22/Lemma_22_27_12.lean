module

public import ReasLib.Algebra.Category.DifferentialGraded.AdmissibleCone.Triangle
import StacksCheckRecall

@[expose] public section

open DifferentialGradedCategory

/- Lemma 22.27.12 (09QT): in a morphism of admissible-cone triangles, a homotopy equivalence on
the first two components forces a homotopy equivalence on the cone component. -/
@[stacks 09QT]
#check CompBoundaryAssignment.AdmissibleCone.homotopyEquivalences_coneMap

#check CompBoundaryAssignment.AdmissibleCone.homInK
