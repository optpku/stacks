module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.MorphismProperty.SaturatedMultiplicativeSystem

@[expose] public section

/-!
# Saturation of Cone-Defined Morphism Properties

For a triangulated object property `P`, the cone-defined morphism property `P.trW` only depends
on the isomorphism closure of `P`.  This module identifies saturation of that morphism property
with closure of the corresponding object property under retracts.
-/

universe v u

namespace CategoryTheory.ObjectProperty

open Limits MorphismProperty Pretriangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (P : ObjectProperty D)

namespace IsoClosure.TrW

/-- Stacks 05RG, isomorphism-invariant form: `P.isoClosure.trW` is saturated exactly when
`P.isoClosure` is stable under retracts.  This is the canonical statement for an arbitrary
object property `P`. -/
@[stacks 05RG "saturation of the Verdier system of an isomorphism closure"]
theorem saturated_iff_stableUnderRetracts
    [IsTriangulated D] [P.IsTriangulated] :
    P.isoClosure.trW.IsSaturatedMultiplicativeSystem ↔
      P.isoClosure.IsStableUnderRetracts := sorry

end IsoClosure.TrW

namespace TrW

/-- Stacks 05RG: for an isomorphism-closed triangulated object property, its cone-defined
morphism property is saturated exactly when the object property is stable under retracts. -/
@[stacks 05RG "saturation of a Verdier system"]
theorem saturated_iff_stableUnderRetracts
    [IsTriangulated D] [P.IsTriangulated] [P.IsClosedUnderIsomorphisms] :
    P.trW.IsSaturatedMultiplicativeSystem ↔ P.IsStableUnderRetracts := sorry

/-- A retract-stable triangulated object property canonically determines a saturated
multiplicative system through its cone-defined morphism property. -/
@[stacks 05RG "retract-stable Verdier systems are saturated"]
instance saturated
    [IsTriangulated D] [P.IsTriangulated] [P.IsStableUnderRetracts] :
    P.trW.IsSaturatedMultiplicativeSystem := sorry


end TrW


end CategoryTheory.ObjectProperty
