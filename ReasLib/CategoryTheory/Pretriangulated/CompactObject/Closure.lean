module

public import ReasLib.CategoryTheory.Preadditive.CompactObject
public import ReasLib.CategoryTheory.Pretriangulated.IdempotentComplete
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Closure of Compact Objects

This module records the closure properties of the compact-object predicate in
preadditive pretriangulated categories.  The underlying notions of retract,
strict fullness, and triangulated object property are owned by mathlib's
`CategoryTheory.ObjectProperty` API; this file supplies their compact-object
instances and object-level bridges.
-/

namespace CategoryTheory

open Limits
open Pretriangulated

universe v u

section

variable {D : Type u} [Category.{v} D] [Preadditive D]
  [HasCoproducts.{max u v} D]

/-- Compact objects are stable under retracts (equivalently, direct summands). -/
@[stacks 09QH]
instance isCompactObject_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts (IsCompactObject : ObjectProperty D) := sorry

/-- A retract of a compact object is compact. -/
theorem isCompactObject_of_retract {K L : D} (r : Retract K L)
    (hL : IsCompactObject L) : IsCompactObject K := sorry

/-- An object isomorphic to a compact object is compact. -/
theorem isCompactObject_of_iso {K L : D} (e : K ≅ L)
    (hK : IsCompactObject K) : IsCompactObject L := sorry

/-- Compactness is invariant under isomorphism. -/
theorem isCompactObject_iff_of_iso {K L : D} (e : K ≅ L) :
    IsCompactObject K ↔ IsCompactObject L := sorry

/-- If the ambient category is idempotent complete, so is its compact full subcategory. -/
instance compactObjectSubcategory_isIdempotentComplete [IsIdempotentComplete D] :
    IsIdempotentComplete (compactObjectSubcategory D) := sorry

end

section

variable {D : Type u} [Category.{v} D] [Preadditive D]
  [HasCoproducts.{max u v} D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Compact objects form a triangulated object property. -/
@[stacks 09QH]
instance isCompactObject_isTriangulated :
    ObjectProperty.IsTriangulated (IsCompactObject : ObjectProperty D) := sorry

/-- In a distinguished triangle, a third object is compact when the first two are compact. -/
theorem isCompactObject_of_distinguished (T : Triangle D) (hT : T ∈ distTriang D)
    (h1 : IsCompactObject T.obj₁) (h2 : IsCompactObject T.obj₂) :
    IsCompactObject T.obj₃ := sorry

/-- In a distinguished triangle, the first object is compact when the second and third objects
are compact. -/
theorem isCompactObject_of_distinguished_left (T : Triangle D) (hT : T ∈ distTriang D)
    (h2 : IsCompactObject T.obj₂) (h3 : IsCompactObject T.obj₃) :
    IsCompactObject T.obj₁ := sorry

/-- In a distinguished triangle, the middle object is compact when the first and third objects
are compact. -/
theorem isCompactObject_of_distinguished_middle (T : Triangle D) (hT : T ∈ distTriang D)
    (h1 : IsCompactObject T.obj₁) (h3 : IsCompactObject T.obj₃) :
    IsCompactObject T.obj₂ := sorry

end

end CategoryTheory
