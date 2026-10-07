module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Maps Between Chosen Binary Biproducts

This leaf exposes the morphism between two explicit binary-biproduct models that is the identity
on a common left summand and a specified morphism on the right summand.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Limits.BinaryBiproductData

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The morphism between chosen binary-biproduct models which is the identity on their common
left summand and is induced by f on their right summands. -/
def map {X Y Z : C} (source : BinaryBiproductData X Y) (target : BinaryBiproductData X Z)
    (f : Y ⟶ Z) :
    source.bicone.pt ⟶ target.bicone.pt :=
  target.isBilimit.isLimit.lift
    (BinaryFan.mk source.bicone.fst (source.bicone.snd ≫ f))

/-- The binary-biproduct map preserves the projection to the common left summand. -/
@[reassoc]
theorem map_fst {X Y Z : C} (source : BinaryBiproductData X Y) (target : BinaryBiproductData X Z)
    (f : Y ⟶ Z) :
    map source target f ≫ target.bicone.fst = source.bicone.fst := sorry

/-- The binary-biproduct map acts by f after projection to the right summand. -/
@[reassoc]
theorem map_snd {X Y Z : C} (source : BinaryBiproductData X Y) (target : BinaryBiproductData X Z)
    (f : Y ⟶ Z) :
    map source target f ≫ target.bicone.snd = source.bicone.snd ≫ f := sorry

/-- Reading the right coordinate of a binary-biproduct map recovers its input morphism. -/
@[reassoc]
theorem inr_map_snd {X Y Z : C} (source : BinaryBiproductData X Y)
    (target : BinaryBiproductData X Z) (f : Y ⟶ Z) :
    source.bicone.inr ≫ map source target f ≫ target.bicone.snd = f := sorry

/-- A morphism preserving the common left projection is determined by its right coordinate. -/
theorem eq_map_of_comp_fst {X Y Z : C} (source : BinaryBiproductData X Y)
    (target : BinaryBiproductData X Z) (g : source.bicone.pt ⟶ target.bicone.pt)
    (hg : g ≫ target.bicone.fst = source.bicone.fst) :
    g = map source target (source.bicone.inr ≫ g ≫ target.bicone.snd) := sorry

/-- The map induced by the zero morphism is the inclusion of the common left summand followed by
its projection. -/
theorem map_zero {X Y Z : C} (source : BinaryBiproductData X Y)
    (target : BinaryBiproductData X Z) :
    map source target 0 = source.bicone.fst ≫ target.bicone.inl := sorry

/-- Binary-biproduct maps compose by composing their right coordinates. -/
theorem map_comp {W X Y Z : C} (source : BinaryBiproductData X W)
    (middle : BinaryBiproductData X Y) (target : BinaryBiproductData X Z)
    (f : W ⟶ Y) (g : Y ⟶ Z) :
    map source middle f ≫ map middle target g = map source target (f ≫ g) := sorry

end CategoryTheory.Limits.BinaryBiproductData
