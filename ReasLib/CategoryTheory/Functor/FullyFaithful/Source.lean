module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

@[expose] public section

/-!
# Full Faithfulness at a Source Object

This is the sourcewise dual of `Functor.FullyFaithfulTo`: only hom-sets whose source is a fixed
object are required.  The corresponding identity structured arrow is initial.
-/

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

/-- Explicit inverse data for the maps on all hom-sets whose source is `X`.

This objectwise owner is the sourcewise dual of `Functor.FullyFaithfulTo` and avoids choosing an
inverse again from a bare bijectivity proof. -/
structure FullyFaithfulFrom (F : C ⥤ D) (X : C) where
  /-- The inverse image of a morphism starting at `F.obj X`. -/
  preimage {Y : C} (f : F.obj X ⟶ F.obj Y) : X ⟶ Y
  /-- Mapping a sourcewise preimage recovers the original morphism. -/
  map_preimage {Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage f) = f
  /-- Taking the sourcewise preimage of a mapped morphism recovers that morphism. -/
  preimage_map {Y : C} (f : X ⟶ Y) : preimage (F.map f) = f

namespace FullyFaithfulFrom

variable {F : C ⥤ D} {X : C} (hF : F.FullyFaithfulFrom X)

attribute [simp] map_preimage preimage_map

/-- Sourcewise full-faithfulness data is unique when it exists. -/
theorem subsingleton : Subsingleton (F.FullyFaithfulFrom X) := sorry

/-- The sourcewise hom-set equivalence carried by `FullyFaithfulFrom`. -/
def homEquiv {Y : C} : (X ⟶ Y) ≃ (F.obj X ⟶ F.obj Y) where
  toFun := F.map
  invFun := hF.preimage
  left_inv := hF.preimage_map
  right_inv := hF.map_preimage

/-- The sourcewise hom-set equivalence acts by the functor on ordinary morphisms. -/
@[simp]
theorem homEquiv_apply {Y : C} (f : X ⟶ Y) :
    hF.homEquiv f = F.map f := sorry

/-- The inverse sourcewise hom-set equivalence is the stored preimage map. -/
@[simp]
theorem homEquiv_symm_apply {Y : C} (f : F.obj X ⟶ F.obj Y) :
    hF.homEquiv.symm f = hF.preimage f := sorry

/-- A sourcewise fully faithful functor is injective on each hom-set starting at `X`. -/
theorem map_injective {Y : C} (hF : F.FullyFaithfulFrom X) :
    Function.Injective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := sorry

/-- A sourcewise fully faithful functor is surjective on each hom-set starting at `X`. -/
theorem map_surjective {Y : C} (hF : F.FullyFaithfulFrom X) :
    Function.Surjective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := sorry

/-- A sourcewise fully faithful functor is bijective on each hom-set starting at `X`. -/
theorem map_bijective (Y : C) (hF : F.FullyFaithfulFrom X) :
    Function.Bijective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := sorry

/-- The sourcewise preimage of the identity is the identity. -/
@[simp]
theorem preimage_id : hF.preimage (𝟙 (F.obj X)) = 𝟙 X := sorry

/-- Sourcewise preimages commute with postcomposition by a mapped morphism. -/
@[reassoc]
theorem preimage_postcomp {Y Y' : C} (g : F.obj X ⟶ F.obj Y) (f : Y ⟶ Y') :
    hF.preimage (g ≫ F.map f) = hF.preimage g ≫ f := sorry

/-- Global full-faithfulness data restricts to any fixed source object. -/
def ofFullyFaithful (h : F.FullyFaithful) (X : C) : F.FullyFaithfulFrom X where
  preimage := h.preimage
  map_preimage := h.map_preimage
  preimage_map := h.preimage_map

/-- The sourcewise preimage satisfies the triangle defining the canonical map from the identity
structured arrow. -/
theorem desc_fac (Y : StructuredArrow (F.obj X) F) :
    (StructuredArrow.mk (𝟙 (F.obj X))).hom ≫ F.map (hF.preimage Y.hom) = Y.hom := sorry

/-- The canonical map from the identity structured arrow at a sourcewise fully faithful object. -/
def desc (Y : StructuredArrow (F.obj X) F) :
    StructuredArrow.mk (𝟙 (F.obj X)) ⟶ Y :=
  StructuredArrow.homMk (hF.preimage Y.hom) (desc_fac hF Y)

/-- The underlying target morphism of the canonical descent is the stored sourcewise preimage. -/
@[simp]
theorem desc_right (Y : StructuredArrow (F.obj X) F) :
    (desc hF Y).right = hF.preimage Y.hom := sorry

/-- The sourcewise preimage gives the unique map from the identity structured arrow. -/
theorem desc_unique (Y : StructuredArrow (F.obj X) F)
    (f : StructuredArrow.mk (𝟙 (F.obj X)) ⟶ Y) : f = desc hF Y := sorry

/-- The identity structured arrow at a sourcewise fully faithful object is initial. -/
def mkIdInitial : IsInitial (StructuredArrow.mk (𝟙 (F.obj X))) :=
  IsInitial.ofUniqueHom (desc hF) (desc_unique hF)



end FullyFaithfulFrom

end CategoryTheory.Functor
