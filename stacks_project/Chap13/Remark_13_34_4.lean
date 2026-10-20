module

import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Morphism
import StacksCheckRecall

@[expose] public section

/-!
# Remark 13.34.4

The general completion statement is mathlib's distinguished-triangle API.
For Milnor triangles, `HomotopyLimit.Presentation.Hom` additionally retains
the induced product map and compatibility with every stage projection.
-/

/- Remark 13.34.4 (Stacks 0H9J): a commuting square between the two
Milnor difference maps extends to a morphism of the chosen triangles. -/
@[stacks 0H9J] #check
  @CategoryTheory.Pretriangulated.complete_distinguished_triangle_morphism₁

/- Milnor specialization: a tower morphism induces a compatible map between any two explicit
homotopy-limit presentations without selecting that generally nonunique map publicly. -/
@[stacks 0H9J] #check @CategoryTheory.HomotopyLimit.Presentation.nonemptyHom

#check @CategoryTheory.HomotopyLimit.Presentation.Hom.triangleMorphism
#check @CategoryTheory.HomotopyLimit.Presentation.Hom.stageProjection_naturality
