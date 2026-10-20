/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Category.Pointed
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.WithTerminal.Cone
import Mathlib.Tactic.CrossRefAttribute

/-!
# Limits and zero morphisms in pointed types

The category of pointed types is canonically equivalent to the under category of the singleton
type.  This file makes that equivalence the common owner for limits and colimits in `Pointed`.
It also gives zero morphisms directly as constant maps to the target point, so their computational
content does not depend on a chosen zero object.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Pointed

/-- The map from the singleton type selecting the distinguished point of a pointed type. -/
def pointMap (X : Pointed.{u}) : PUnit.{u + 1} → X :=
  fun _ ↦ X.point

/-- A pointed type regarded as an object under the singleton type. -/
def toUnderObj (X : Pointed.{u}) : Under PUnit.{u + 1} :=
  Under.mk (↾(pointMap X))

/-- A pointed morphism gives a commuting triangle under the singleton type. -/
theorem toUnderMap_comm {X Y : Pointed.{u}} (f : X ⟶ Y) :
    (toUnderObj X).hom ≫ ↾f.toFun = (toUnderObj Y).hom := sorry

/-- The morphism under the singleton type induced by a pointed morphism. -/
def toUnderMap {X Y : Pointed.{u}} (f : X ⟶ Y) : toUnderObj X ⟶ toUnderObj Y :=
  Under.homMk (↾f.toFun) (toUnderMap_comm f)

/-- The map from pointed types to the under category preserves identities. -/
theorem toUnderMap_id (X : Pointed.{u}) :
    toUnderMap (𝟙 X) = 𝟙 (toUnderObj X) := sorry

/-- The map from pointed types to the under category preserves composition. -/
theorem toUnderMap_comp {X Y Z : Pointed.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    toUnderMap (f ≫ g) = toUnderMap f ≫ toUnderMap g := sorry

/-- The functor identifying pointed types with objects under the singleton type. -/
def toUnder : Pointed.{u} ⥤ Under PUnit.{u + 1} where
  obj := toUnderObj
  map := toUnderMap
  map_id := toUnderMap_id
  map_comp := toUnderMap_comp

/-- The object under the singleton type has the original pointed type as its carrier. -/
@[simp]
theorem toUnder_obj_right (X : Pointed.{u}) : (toUnder.obj X).right = X.X := sorry

/-- The structural map of `toUnder.obj X` evaluates to the distinguished point. -/
@[simp]
theorem toUnder_obj_hom_apply (X : Pointed.{u}) (x : PUnit.{u + 1}) :
    (toUnder.obj X).hom x = X.point := sorry

/-- The underlying map of `toUnder.map f` is the original pointed map. -/
@[simp]
theorem toUnder_map_right_apply {X Y : Pointed.{u}} (f : X ⟶ Y) (x : X) :
    (toUnder.map f).right x = f.toFun x := sorry

/-- The pointed type carried by an object under the singleton type. -/
def fromUnderObj (X : Under PUnit.{u + 1}) : Pointed.{u} :=
  Pointed.of (X.hom PUnit.unit)

/-- A morphism under the singleton type preserves the induced distinguished points. -/
theorem fromUnderMap_point {X Y : Under PUnit.{u + 1}} (f : X ⟶ Y) :
    f.right (fromUnderObj X).point = (fromUnderObj Y).point := sorry

/-- The pointed morphism induced by a morphism under the singleton type. -/
def fromUnderMap {X Y : Under PUnit.{u + 1}} (f : X ⟶ Y) :
    fromUnderObj X ⟶ fromUnderObj Y :=
  ⟨f.right, fromUnderMap_point f⟩

/-- The map from the under category to pointed types preserves identities. -/
theorem fromUnderMap_id (X : Under PUnit.{u + 1}) :
    fromUnderMap (𝟙 X) = 𝟙 (fromUnderObj X) := sorry

/-- The map from the under category to pointed types preserves composition. -/
theorem fromUnderMap_comp {X Y Z : Under PUnit.{u + 1}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    fromUnderMap (f ≫ g) = fromUnderMap f ≫ fromUnderMap g := sorry

/-- The functor recovering a pointed type from an object under the singleton type. -/
def fromUnder : Under PUnit.{u + 1} ⥤ Pointed.{u} where
  obj := fromUnderObj
  map := fromUnderMap
  map_id := fromUnderMap_id
  map_comp := fromUnderMap_comp

/-- Recovering a pointed type preserves the carrier of the object under the singleton type. -/
@[simp]
theorem fromUnder_obj_carrier (X : Under PUnit.{u + 1}) :
    (fromUnder.obj X).X = X.right := sorry

/-- The recovered distinguished point is the image of the unique singleton element. -/
@[simp]
theorem fromUnder_obj_point (X : Under PUnit.{u + 1}) :
    (fromUnder.obj X).point = X.hom PUnit.unit := sorry

/-- Recovering a pointed morphism preserves its underlying carrier map. -/
@[simp]
theorem fromUnder_map_apply {X Y : Under PUnit.{u + 1}} (f : X ⟶ Y) (x : X.right) :
    (fromUnder.map f).toFun x = f.right x := sorry

namespace EquivUnder

/-- The identity carrier equivalence preserves the point in the unit component. -/
theorem unitApp_point (X : Pointed.{u}) :
    (Equiv.refl X) X.point = ((toUnder ⋙ fromUnder).obj X).point := sorry

/-- The component at a pointed type of the unit for the equivalence with the under category. -/
def unitApp (X : Pointed.{u}) : X ≅ (toUnder ⋙ fromUnder).obj X :=
  Pointed.Iso.mk (Equiv.refl X) (unitApp_point X)

/-- The unit components for the equivalence with the under category are natural. -/
theorem unit_naturality {X Y : Pointed.{u}} (f : X ⟶ Y) :
    f ≫ (unitApp Y).hom = (unitApp X).hom ≫ (toUnder ⋙ fromUnder).map f := sorry

/-- The unit natural isomorphism for the equivalence with the under category. -/
def unit : Functor.id Pointed.{u} ≅ toUnder ⋙ fromUnder :=
  NatIso.ofComponents unitApp unit_naturality

namespace Counit

/-- The forward carrier map in the counit component is the identity function. -/
def forward (X : Under PUnit.{u + 1}) : (toUnderObj (fromUnderObj X)).right → X.right :=
  fun x ↦ x

/-- The inverse carrier map in the counit component is the identity function. -/
def backward (X : Under PUnit.{u + 1}) : X.right → (toUnderObj (fromUnderObj X)).right :=
  fun x ↦ x

/-- The counit carrier maps are inverse in the forward order. -/
theorem leftInverse (X : Under PUnit.{u + 1}) :
    Function.LeftInverse (backward X) (forward X) := sorry

/-- The counit carrier maps are inverse in the backward order. -/
theorem rightInverse (X : Under PUnit.{u + 1}) :
    Function.RightInverse (backward X) (forward X) := sorry

/-- The identity carrier equivalence in the counit component. -/
def rightEquiv (X : Under PUnit.{u + 1}) :
    (toUnderObj (fromUnderObj X)).right ≃ X.right where
  toFun := forward X
  invFun := backward X
  left_inv := leftInverse X
  right_inv := rightInverse X

/-- The identity carrier equivalence gives a commuting triangle under the singleton type. -/
theorem app_comm (X : Under PUnit.{u + 1}) :
    (toUnderObj (fromUnderObj X)).hom ≫ (rightEquiv X).toIso.hom = X.hom := sorry

/-- The component at an object under the singleton type of the counit equivalence. -/
def app (X : Under PUnit.{u + 1}) : (fromUnder ⋙ toUnder).obj X ≅ X :=
  Under.isoMk (rightEquiv X).toIso (app_comm X)

/-- The counit components for the equivalence with the under category are natural. -/
theorem naturality {X Y : Under PUnit.{u + 1}} (f : X ⟶ Y) :
    (fromUnder ⋙ toUnder).map f ≫ (app Y).hom = (app X).hom ≫ f := sorry

/-- The counit natural isomorphism for the equivalence with the under category. -/
def iso : fromUnder ⋙ toUnder ≅ Functor.id (Under PUnit.{u + 1}) :=
  NatIso.ofComponents app naturality

end Counit

end EquivUnder

/-- Remark 17.6.4 (01B0): pointed types are canonically equivalent to types under the singleton
type, providing the categorical foundation for pointed sections with support. -/
@[stacks 01B0 "pointed-set categorical foundation for sections with support"]
def equivUnder : Pointed.{u} ≌ Under PUnit.{u + 1} :=
  CategoryTheory.Equivalence.mk toUnder fromUnder EquivUnder.unit EquivUnder.Counit.iso

/-- The category of pointed types has all limits. -/
noncomputable instance hasLimits : HasLimits Pointed.{u} :=
  Adjunction.has_limits_of_equivalence equivUnder.functor

/-- The category of pointed types has all colimits. -/
noncomputable instance hasColimits : HasColimits Pointed.{u} :=
  Adjunction.has_colimits_of_equivalence equivUnder.functor

/-- The underlying function of the zero morphism between two pointed types. -/
def zeroFunction (X Y : Pointed.{u}) : X → Y :=
  fun _ ↦ Y.point

/-- The zero function sends the source point to the target point. -/
theorem zeroFunction_map_point (X Y : Pointed.{u}) :
    zeroFunction X Y X.point = Y.point := sorry

/-- Remark 17.6.4 (01B0): the zero morphism between pointed types is explicitly the constant map
to the target point. -/
@[stacks 01B0 "zero morphisms for pointed sections with support"]
def zeroHom (X Y : Pointed.{u}) : X ⟶ Y :=
  ⟨zeroFunction X Y, zeroFunction_map_point X Y⟩

/-- Evaluating the zero morphism gives the distinguished point of the target. -/
@[simp]
theorem zeroHom_apply (X Y : Pointed.{u}) (x : X) :
    (zeroHom X Y).toFun x = Y.point := sorry

/-- Postcomposition with a zero morphism gives the corresponding zero morphism. -/
theorem comp_zeroHom {X Y : Pointed.{u}} (f : X ⟶ Y) (Z : Pointed.{u}) :
    f ≫ zeroHom Y Z = zeroHom X Z := sorry

/-- Precomposition of a zero morphism gives the corresponding zero morphism. -/
theorem zeroHom_comp (X : Pointed.{u}) {Y Z : Pointed.{u}} (f : Y ⟶ Z) :
    zeroHom X Y ≫ f = zeroHom X Z := sorry

/-- Pointed types have the canonical zero morphisms given by constant maps to target points. -/
instance hasZeroMorphisms : HasZeroMorphisms Pointed.{u} where
  zero X Y := ⟨zeroHom X Y⟩
  comp_zero := comp_zeroHom
  zero_comp := zeroHom_comp

/-- The standard zero morphism in pointed types is the explicit constant pointed map. -/
@[simp]
theorem zero_eq_zeroHom (X Y : Pointed.{u}) : (0 : X ⟶ Y) = zeroHom X Y := sorry

/-- The standard zero morphism evaluates to the distinguished point of its target. -/
@[simp]
theorem zero_apply (X Y : Pointed.{u}) (x : X) : (0 : X ⟶ Y).toFun x = Y.point := sorry

/-- The canonical singleton pointed type. -/
def singleton : Pointed.{u} :=
  Pointed.of (PUnit.unit : PUnit.{u + 1})

/-- The singleton pointed type is a zero object in pointed types. -/
theorem singleton_isZero : IsZero singleton := sorry

/-- The category of pointed types has the canonical singleton zero object. -/
instance hasZeroObject : HasZeroObject Pointed.{u} :=
  singleton_isZero.hasZeroObject

end Pointed

#synth HasLimits Pointed
#synth HasColimits Pointed
#synth HasZeroMorphisms Pointed
#synth HasZeroObject Pointed

/- The raw point map, counit carrier maps, zero function, and singleton object have no `sorryAx`;
the object constructors additionally use only `propext`, `Classical.choice`, and `Quot.sound`.
Any `sorryAx` reported for bundled morphisms, functors, equivalences, or categorical-existence
instances is confined to Prop-valued compatibility, functoriality, inverse, naturality, or
universal-property fields. -/
