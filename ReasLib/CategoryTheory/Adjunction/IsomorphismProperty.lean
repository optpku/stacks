module

public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Isomorphism loci of an adjunction

This module packages the objects on which the unit or counit of an adjunction is invertible.  The
properties are owned by the adjunction itself, so downstream declarations do not need to repeat
the two functors as explicit parameters.
-/

open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe vC vD uC uD

namespace CategoryTheory.Adjunction

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

/-- The objects on which the unit of an adjunction is invertible. -/
@[stacks 0D7Q "unit-isomorphism object property"]
abbrev unitIsoProperty : ObjectProperty C :=
  fun X ↦ IsIso (adj.unit.app X)

/-- The objects on which the counit of an adjunction is invertible. -/
@[stacks 0D7Q "counit-isomorphism object property", stacks 0D7R]
abbrev counitIsoProperty : ObjectProperty D :=
  fun X ↦ IsIso (adj.counit.app X)

/-- The unit-isomorphism property is invariant under isomorphism. -/
@[stacks 0D7Q "unit-isomorphism property is replete"]
instance unitIsoProperty_isClosedUnderIsomorphisms :
    adj.unitIsoProperty.IsClosedUnderIsomorphisms := sorry

/-- The counit-isomorphism property is invariant under isomorphism. -/
@[stacks 0D7Q "counit-isomorphism property is replete", stacks 0D7R]
instance counitIsoProperty_isClosedUnderIsomorphisms :
    adj.counitIsoProperty.IsClosedUnderIsomorphisms := sorry

/-- The unit-isomorphism property is stable under retracts. -/
@[stacks 0D7Q "unit-isomorphism property is retract-stable"]
instance unitIsoProperty_isStableUnderRetracts :
    adj.unitIsoProperty.IsStableUnderRetracts := sorry

/-- The counit-isomorphism property is stable under retracts. -/
@[stacks 0D7Q "counit-isomorphism property is retract-stable", stacks 0D7R]
instance counitIsoProperty_isStableUnderRetracts :
    adj.counitIsoProperty.IsStableUnderRetracts := sorry

section Triangulated

variable [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
variable [HasShift C ℤ] [HasShift D ℤ]
variable [∀ n : ℤ, (shiftFunctor C n).Additive]
variable [∀ n : ℤ, (shiftFunctor D n).Additive]
variable [Pretriangulated C] [Pretriangulated D]

/-- The right adjoint's `CommShift` and triangulated structure make the unit-isomorphism locus
triangulated; the corresponding adjunction coherence is inferred canonically. -/
@[stacks 0D7Q "unit-isomorphism property is triangulated"]
instance unitIsoProperty_isTriangulated
    [G.CommShift ℤ] [G.IsTriangulated] :
    adj.unitIsoProperty.IsTriangulated := sorry

/-- The left adjoint's `CommShift` and triangulated structure make the counit-isomorphism locus
triangulated; the corresponding adjunction coherence is inferred canonically. -/
@[stacks 0D7Q "counit-isomorphism property is triangulated", stacks 0D7R]
instance counitIsoProperty_isTriangulated
    [F.CommShift ℤ] [F.IsTriangulated] :
    adj.counitIsoProperty.IsTriangulated := sorry

end Triangulated

end CategoryTheory.Adjunction
