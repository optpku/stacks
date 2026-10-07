module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.MorphismProperty.Limits
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/- Lemma 26.18.2 (1): immersions are stable under arbitrary base change. -/
@[stacks 01JY] #check IsImmersion.isStableUnderBaseChange

/- Lemma 26.18.2 (2): closed immersions are stable under arbitrary base change. -/
@[stacks 01JY] #check IsClosedImmersion.isStableUnderBaseChange

/- Lemma 26.18.2 (3): open immersions are stable under arbitrary base change. -/
@[stacks 01JY] #check isOpenImmersion_stableUnderBaseChange

#check MorphismProperty.overPullbackMap

end AlgebraicGeometry
