module

public import ReasLib.AlgebraicGeometry.Scheme.Reduction
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) (Z : TopologicalSpace.Closeds X)

/- Definition 26.12.5 (1): a scheme structure on a closed subset is the fixed-support fiber of
ideal-sheaf data. -/
@[stacks 01J4] #check ClosedSubschemeStructure Z
#check ClosedSubschemeStructure.ideal
#check ClosedSubschemeStructure.support_eq
#check ClosedSubschemeStructure.subscheme
#check ClosedSubschemeStructure.ι

/- Definition 26.12.5 (2): the vanishing ideal gives the reduced induced structure. -/
@[stacks 01J4] #check ClosedSubschemeStructure.reduced Z
#check IdealSheafData.support_vanishingIdeal

/- Definition 26.12.5 (3): reduction is the nilradical closed subscheme. -/
@[stacks 01J4] #check reduction
#check reductionι
#check ClosedSubschemeStructure.reduced_top_ideal X
#check ClosedSubschemeStructure.reduced_top_subscheme X
#check ClosedSubschemeStructure.reduced_top_ι X
#check IdealSheafData.vanishingIdeal_top
#check (inferInstance : IsReduced (reduction X))

end AlgebraicGeometry.Scheme
