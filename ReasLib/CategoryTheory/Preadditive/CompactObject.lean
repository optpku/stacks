module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Compact Objects in Preadditive Categories

@stack 07LS
@stack 09QH

This module owns the coproduct-preservation notion of compact object.  It is
independent of derived categories: in a preadditive category, compactness asks
for preservation of every existing small coproduct.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open Opposite
open scoped ZeroObject

universe w v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [Preadditive D]

/-- An object is compact when its preadditive coyoneda functor preserves all small coproducts.
Here small means indexed in the morphism universe of the category, as in Mathlib's limit API. -/
@[stacks 07LS, mk_iff isCompactObject_iff]
class IsCompactObject (K : D) : Prop where
  /-- Preservation of coproducts indexed in the category's morphism universe. -/
  preservesCoproducts (I : Type v) :
    PreservesColimitsOfShape (Discrete I) (preadditiveCoyoneda.obj (op K))

/-- A compact object preserves coproducts indexed by every universe that embeds in the ambient
universe. -/
instance instPreservesCoproductsOfIsCompactObject (K : D) [IsCompactObject K]
    (I : Type w) [UnivLE.{w, v}] :
    PreservesColimitsOfShape (Discrete I) (preadditiveCoyoneda.obj (op K)) := sorry

/-- The full subcategory of compact objects. -/
@[stacks 09QH]
abbrev compactObjectSubcategory (D : Type u) [Category.{v} D] [Preadditive D] :
    Type u := ObjectProperty.FullSubcategory (IsCompactObject : ObjectProperty D)

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D]

/-- The zero object is compact. -/
instance isCompactObject_zero : IsCompactObject (0 : D) := sorry

end

end CategoryTheory
