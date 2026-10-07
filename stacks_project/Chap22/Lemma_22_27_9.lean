module

public import ReasLib.Algebra.Category.DifferentialGraded.AdmissibleCone.Triangle
import StacksCheckRecall

@[expose] public section

open DifferentialGradedCategory

/- Lemma 22.27.9 (09QQ): the triangle associated to a graded-split short complex is canonically
independent of the splitting through the identity on its three vertices. -/
@[stacks 09QQ]
#check CompBoundaryAssignment.associatedTriangleIso

#check CompBoundaryAssignment.boundary_inK_eq
