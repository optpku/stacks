module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.ObjectProperty.Retract.InverseImage

@[expose] public section

/-!
# The Object Property of Being Zero

The canonical object property `IsZero` is invariant under isomorphisms, retracts, shifts, and
distinguished triangles.  Together with inverse-image instances, these facts make the kernel of
a functor inherit the corresponding closure structure automatically.
-/

universe v u

namespace CategoryTheory.ObjectProperty

open Limits Pretriangulated

/-- The property of being a zero object is invariant under isomorphisms. -/
@[stacks 05RC "zero objects are invariant under isomorphisms"]
instance isZero_isClosedUnderIsomorphisms
    {C : Type u} [Category.{v} C] :
    IsClosedUnderIsomorphisms (IsZero : ObjectProperty C) := sorry

/-- In a category with zero morphisms, a retract of a zero object is zero. -/
@[stacks 05RC "zero objects are stable under retracts"]
instance isZero_isStableUnderRetracts
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] :
    IsStableUnderRetracts (IsZero : ObjectProperty C) := sorry

/-- In a pretriangulated category, zero objects form a triangulated object property. -/
@[stacks 05RC "zero objects form a triangulated object property"]
instance isZero_isTriangulated
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] :
    ObjectProperty.IsTriangulated (IsZero : ObjectProperty C) := sorry

end CategoryTheory.ObjectProperty
