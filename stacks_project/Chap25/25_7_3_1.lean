module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Coskeleton.Projection
import StacksCheckRecall

namespace CategoryTheory

/- Equation 25.7.3.1 [stacks 01GJ]: functorially in the repeated object, the displayed
coskeleton-unit map is the finite product projection indexed by the inclusion of nonsurjective
simplex maps into all simplex maps. -/
@[stacks 01GJ] #check
  @SimplicialObject.CostandardPower.MatchingIso.unit

end CategoryTheory
