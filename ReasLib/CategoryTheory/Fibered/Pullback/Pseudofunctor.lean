/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Pullback.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pseudofunctoriality of pullback at a fixed base functor

For a fixed `u : C ⥤ D`, categorical pullback acts on fibred categories over `D`, cartesian
functors, and vertical natural transformations. This file packages the computational owners from
`Pullback.Map` as a pseudofunctor and exposes the identity, composition, and whiskering laws used
by downstream bicategorical calculations.
-/

@[expose] public section

noncomputable section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Bicategory Limits
open scoped Bicategory

namespace FiberedCategoryOver.Pullback

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable (u : C ⥤ D)

/-- Pullback of fibred-category morphisms preserves identity morphisms. -/
@[simp]
theorem mapCanonical.id (X : FiberedCategoryOver.{uD, vD, w₀, w₁} D) :
    mapCanonical u (𝟙 X) = 𝟙 (FiberedCategoryOver.pullback u X) := sorry

/-- Pullback of fibred-category morphisms preserves composition. -/
@[simp]
theorem mapCanonical.comp
    {X Y Z : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    mapCanonical u (F ≫ G) = mapCanonical u F ≫ mapCanonical u G := sorry

/-- Pullback preserves left whiskering up to its canonical composition comparisons. -/
theorem map₂.whiskerLeft
    {X Y Z : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    (F : X ⟶ Y) {G H : Y ⟶ Z} (eta : G ⟶ H) :
    map₂ u (F ◁ eta) =
      eqToHom (mapCanonical.comp u F G) ≫
        mapCanonical u F ◁ map₂ u eta ≫
          eqToHom (mapCanonical.comp u F H).symm := sorry

/-- Pullback preserves right whiskering up to its canonical composition comparisons. -/
theorem map₂.whiskerRight
    {X Y Z : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) (H : Y ⟶ Z) :
    map₂ u (eta ▷ H) =
      eqToHom (mapCanonical.comp u F H) ≫
        map₂ u eta ▷ mapCanonical u H ≫
          eqToHom (mapCanonical.comp u G H).symm := sorry

namespace pseudofunctorConstruction

/-- The prelax core of fixed-base pullback, assembled from its object action and hom functors. -/
private noncomputable def prelax :
    PrelaxFunctor
      (FiberedCategoryOver.{uD, vD, w₀, w₁} D)
      (FiberedCategoryOver.{uC, vC,
        max uC (max w₀ vD), max vC w₁} C) :=
  PrelaxFunctor.mkOfHomFunctors
    (fun X ↦ FiberedCategoryOver.pullback u X)
    (mapFunctor u)

/-- The identity comparison of the fixed-base pullback prelax core. -/
private noncomputable def mapIdOwner
    (X : FiberedCategoryOver.{uD, vD, w₀, w₁} D) :
    (prelax u).map (𝟙 X) ≅ 𝟙 ((prelax u).obj X) :=
  eqToIso (mapCanonical.id u X)

/-- The composition comparison of the fixed-base pullback prelax core. -/
private noncomputable def mapCompOwner
    {X Y Z : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    (prelax u).map (F ≫ G) ≅ (prelax u).map F ≫ (prelax u).map G :=
  eqToIso (mapCanonical.comp u F G)

/-- Fixed-base pullback carries associators through its composition comparisons. -/
private theorem map₂_associator
    {W X Y Z : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    (F : W ⟶ X) (G : X ⟶ Y) (H : Y ⟶ Z) :
    (prelax u).map₂ (α_ F G H).hom =
      (mapCompOwner u (F ≫ G) H).hom ≫
        (mapCompOwner u F G).hom ▷ (prelax u).map H ≫
          (α_ ((prelax u).map F) ((prelax u).map G) ((prelax u).map H)).hom ≫
            (prelax u).map F ◁ (mapCompOwner u G H).inv ≫
              (mapCompOwner u F (G ≫ H)).inv := sorry

/-- Fixed-base pullback carries left unitors through its identity and composition comparisons. -/
private theorem map₂_left_unitor
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D} (F : X ⟶ Y) :
    (prelax u).map₂ (λ_ F).hom =
      (mapCompOwner u (𝟙 X) F).hom ≫
        (mapIdOwner u X).hom ▷ (prelax u).map F ≫
          (λ_ ((prelax u).map F)).hom := sorry

/-- Fixed-base pullback carries right unitors through its identity and composition comparisons. -/
private theorem map₂_right_unitor
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D} (F : X ⟶ Y) :
    (prelax u).map₂ (ρ_ F).hom =
      (mapCompOwner u F (𝟙 Y)).hom ≫
        (prelax u).map F ◁ (mapIdOwner u Y).hom ≫
          (ρ_ ((prelax u).map F)).hom := sorry

end pseudofunctorConstruction

/-- Pullback along the fixed base functor `u` as a pseudofunctor on fibred categories. Its
object, `1`-cell, and `2`-cell actions are `pullback u`, `mapCanonical u`, and `map₂ u`. -/
noncomputable def pseudofunctor (u : C ⥤ D) :
    Pseudofunctor
      (FiberedCategoryOver.{uD, vD, w₀, w₁} D)
      (FiberedCategoryOver.{uC, vC,
        max uC (max w₀ vD), max vC w₁} C) where
  toPrelaxFunctor := pseudofunctorConstruction.prelax u
  mapId := pseudofunctorConstruction.mapIdOwner u
  mapComp := pseudofunctorConstruction.mapCompOwner u
  map₂_whisker_left := map₂.whiskerLeft u
  map₂_whisker_right := map₂.whiskerRight u
  map₂_associator := pseudofunctorConstruction.map₂_associator u
  map₂_left_unitor := pseudofunctorConstruction.map₂_left_unitor u
  map₂_right_unitor := pseudofunctorConstruction.map₂_right_unitor u

/-- The object action of the fixed-base pullback pseudofunctor is categorical pullback. -/
@[simp]
theorem pseudofunctor.obj (X : FiberedCategoryOver.{uD, vD, w₀, w₁} D) :
    (pseudofunctor u).obj X = FiberedCategoryOver.pullback u X := sorry

/-- The `1`-cell action of the fixed-base pullback pseudofunctor is `mapCanonical`. -/
@[simp]
theorem pseudofunctor.map
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D} (F : X ⟶ Y) :
    (pseudofunctor u).map F = mapCanonical u F := sorry

/-- The `2`-cell action of the fixed-base pullback pseudofunctor is `map₂`. -/
@[simp]
theorem pseudofunctor.map₂
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    (pseudofunctor u).map₂ eta = map₂ u eta := sorry

/-- The identity comparison of the fixed-base pullback pseudofunctor comes from
`mapCanonical.id`. -/
@[simp]
theorem pseudofunctor.mapId (X : FiberedCategoryOver.{uD, vD, w₀, w₁} D) :
    (pseudofunctor u).mapId X = eqToIso (mapCanonical.id u X) := sorry

/-- The composition comparison of the fixed-base pullback pseudofunctor comes from
`mapCanonical.comp`. -/
@[simp]
theorem pseudofunctor.mapComp
    {X Y Z : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    (pseudofunctor u).mapComp F G = eqToIso (mapCanonical.comp u F G) := sorry

/-- On each hom category, the fixed-base pullback pseudofunctor uses `mapFunctor`. -/
@[simp]
theorem pseudofunctor.mapFunctor
    (X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D) :
    (pseudofunctor u).mapFunctor X Y = mapFunctor u X Y := sorry

/-- The object action of the fixed-base pullback pseudofunctor's hom functor is
`mapCanonical`. -/
@[simp]
theorem pseudofunctor.mapFunctor.obj
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D} (F : X ⟶ Y) :
    ((pseudofunctor u).mapFunctor X Y).obj F = mapCanonical u F := sorry

/-- The morphism action of the fixed-base pullback pseudofunctor's hom functor is pullback on
`2`-cells. -/
@[simp]
theorem pseudofunctor.mapFunctor.map
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    ((pseudofunctor u).mapFunctor X Y).map eta =
      _root_.CategoryTheory.FiberedCategoryOver.Pullback.map₂ u eta := sorry

end FiberedCategoryOver.Pullback

end CategoryTheory
