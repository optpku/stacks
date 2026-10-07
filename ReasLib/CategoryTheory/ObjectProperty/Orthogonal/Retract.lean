module

public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Retract Stability of Orthogonals

Right and left orthogonals are stable under retracts in any category with zero
morphisms.  The instances are attached directly to the canonical orthogonal
object properties, independently of triangulated-category applications.
-/

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]

namespace RightOrthogonal

/-- Stacks 0FXC: the right orthogonal of an object property is stable under
retracts. -/
@[stacks 0FXC]
instance stableUnderRetracts (P : ObjectProperty C) :
    P.rightOrthogonal.IsStableUnderRetracts := sorry

end RightOrthogonal

namespace LeftOrthogonal

/-- Stacks 0FXC: the left orthogonal of an object property is stable under
retracts. -/
@[stacks 0FXC]
instance stableUnderRetracts (P : ObjectProperty C) :
    P.leftOrthogonal.IsStableUnderRetracts := sorry

end LeftOrthogonal

end CategoryTheory.ObjectProperty
