module

public import ReasLib.CategoryTheory.Presheaf.Basic

/-!
# Unique sections on a class of objects

This module records the reusable property that a `Type`-valued presheaf has a
unique section over every object satisfying a predicate.  The predicate is
kept independent of sites so that site-specific sources can provide canonical
instances without making the property itself topology-specific.
-/

@[expose] public section

open Opposite

universe u v w

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C]

/-- `F` has a unique section over every object satisfying `P`. -/
class HasUniqueSectionsOn (F : Cᵒᵖ ⥤ Type w) (P : C → Prop) : Prop where
  /-- The section type is uniquely inhabited on each object satisfying `P`. -/
  uniqueSections : ∀ U : C, P U → Nonempty (Unique (F.obj (op U)))

/-- A presheaf with `HasUniqueSectionsOn F P` has a unique section at every `P`-object. -/
theorem uniqueSections (F : Cᵒᵖ ⥤ Type w) {P : C → Prop} [HasUniqueSectionsOn F P]
    (U : C) (hU : P U) :
    Nonempty (Unique (F.obj (op U))) := sorry

end CategoryTheory.Presheaf
