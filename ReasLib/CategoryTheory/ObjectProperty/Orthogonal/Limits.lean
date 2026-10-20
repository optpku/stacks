module

public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal

/-!
# Limits and colimits of orthogonal object properties

Right orthogonals are closed under arbitrary limits because representable hom functors preserve
limits.  Dually, left orthogonals are closed under arbitrary colimits.  These instances are
independent of triangulated or differential graded applications.
-/

@[expose] public section

open CategoryTheory.Limits

universe u v uJ vJ

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable (P : ObjectProperty C)
variable (J : Type uJ) [Category.{vJ} J]

namespace RightOrthogonal

/-- The right orthogonal of any object property is closed under limits of every shape. -/
instance closedUnderLimitsOfShape :
    P.rightOrthogonal.IsClosedUnderLimitsOfShape J := sorry

end RightOrthogonal

namespace LeftOrthogonal

/-- The left orthogonal of any object property is closed under colimits of every shape. -/
instance closedUnderColimitsOfShape :
    P.leftOrthogonal.IsClosedUnderColimitsOfShape J := sorry

end LeftOrthogonal

end CategoryTheory.ObjectProperty
