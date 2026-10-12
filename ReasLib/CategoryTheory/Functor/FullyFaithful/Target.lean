/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

@[expose] public section

/-!
# Full Faithfulness at a Target Object

Global full faithfulness is stronger than many localization arguments require.  This file records
the targetwise fragment: the maps on all hom-sets whose target is a fixed object are equivalences.
The corresponding identity costructured arrow is then terminal.
-/

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

/-- Explicit inverse data for the maps on all hom-sets whose target is `Y`.

Unlike global `Functor.FullyFaithful`, this is an objectwise condition.  Keeping the inverse as
data lets localization applications supply a canonical model-specific inverse without making a
second choice from a bare bijectivity proof. -/
structure FullyFaithfulTo (F : C ⥤ D) (Y : C) where
  /-- The inverse image of a morphism ending at `F.obj Y`. -/
  preimage {X : C} (f : F.obj X ⟶ F.obj Y) : X ⟶ Y
  /-- Mapping a targetwise preimage recovers the original morphism. -/
  map_preimage {X : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage f) = f
  /-- Taking the targetwise preimage of a mapped morphism recovers that morphism. -/
  preimage_map {X : C} (f : X ⟶ Y) : preimage (F.map f) = f

namespace FullyFaithfulTo

variable {F : C ⥤ D} {Y : C} (hF : F.FullyFaithfulTo Y)

attribute [simp] map_preimage preimage_map

/-- Targetwise full-faithfulness data is unique when it exists. -/
theorem subsingleton : Subsingleton (F.FullyFaithfulTo Y) := sorry

/-- The targetwise hom-set equivalence carried by `FullyFaithfulTo`. -/
def homEquiv {X : C} : (X ⟶ Y) ≃ (F.obj X ⟶ F.obj Y) where
  toFun := F.map
  invFun := hF.preimage
  left_inv := hF.preimage_map
  right_inv := hF.map_preimage

/-- The targetwise hom-set equivalence acts by the functor on ordinary morphisms. -/
@[simp]
theorem homEquiv_apply {X : C} (f : X ⟶ Y) :
    hF.homEquiv f = F.map f := sorry

/-- The inverse targetwise hom-set equivalence is the stored preimage map. -/
@[simp]
theorem homEquiv_symm_apply {X : C} (f : F.obj X ⟶ F.obj Y) :
    hF.homEquiv.symm f = hF.preimage f := sorry

/-- A targetwise fully faithful functor is injective on each hom-set ending at `Y`. -/
theorem map_injective {X : C} (hF : F.FullyFaithfulTo Y) :
    Function.Injective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := sorry

/-- A targetwise fully faithful functor is surjective on each hom-set ending at `Y`. -/
theorem map_surjective {X : C} (hF : F.FullyFaithfulTo Y) :
    Function.Surjective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := sorry

/-- A targetwise fully faithful functor is bijective on each hom-set ending at `Y`. -/
theorem map_bijective (X : C) (hF : F.FullyFaithfulTo Y) :
    Function.Bijective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := sorry

/-- The targetwise preimage of the identity is the identity. -/
@[simp]
theorem preimage_id : hF.preimage (𝟙 (F.obj Y)) = 𝟙 Y := sorry

/-- Targetwise preimages commute with precomposition by a mapped morphism. -/
@[reassoc]
theorem preimage_precomp {X X' : C} (f : X' ⟶ X) (g : F.obj X ⟶ F.obj Y) :
    hF.preimage (F.map f ≫ g) = f ≫ hF.preimage g := sorry

/-- Global full-faithfulness data restricts to any fixed target object. -/
def ofFullyFaithful (h : F.FullyFaithful) (Y : C) : F.FullyFaithfulTo Y where
  preimage := h.preimage
  map_preimage := h.map_preimage
  preimage_map := h.preimage_map

/-- The targetwise preimage supplies the canonical map to the identity costructured arrow. -/
theorem lift_fac (X : CostructuredArrow F (F.obj Y)) :
    F.map (hF.preimage X.hom) ≫ (CostructuredArrow.mk (𝟙 (F.obj Y))).hom = X.hom := sorry

/-- The canonical map from a costructured arrow to the identity arrow at a targetwise fully
faithful object. -/
def lift (X : CostructuredArrow F (F.obj Y)) :
    X ⟶ CostructuredArrow.mk (𝟙 (F.obj Y)) :=
  CostructuredArrow.homMk (hF.preimage X.hom) (lift_fac hF X)

/-- The underlying source morphism of the canonical lift is the stored targetwise preimage. -/
@[simp]
theorem lift_left (X : CostructuredArrow F (F.obj Y)) :
    (lift hF X).left = hF.preimage X.hom := sorry

/-- The targetwise preimage gives the unique map to the identity costructured arrow. -/
theorem lift_unique (X : CostructuredArrow F (F.obj Y))
    (f : X ⟶ CostructuredArrow.mk (𝟙 (F.obj Y))) : f = lift hF X := sorry

/-- The identity costructured arrow at a targetwise fully faithful object is terminal. -/
def mkIdTerminal : IsTerminal (CostructuredArrow.mk (𝟙 (F.obj Y))) :=
  IsTerminal.ofUniqueHom (lift hF) (lift_unique hF)



end FullyFaithfulTo

end CategoryTheory.Functor
