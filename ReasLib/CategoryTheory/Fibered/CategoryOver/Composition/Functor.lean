/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalTransformation
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Strict
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Composition
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functorial composition of fibred-category projections

Postcomposition by a faithful fibred functor acts on fibred categories,
cartesian morphisms, and their `2`-morphisms. Faithfulness is precisely what
reflects strong cartesianness from the composite projection to its first
factor. Discrete fibrations provide the main canonical class of examples.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe uA uB uC vA vB vC

namespace CategoryTheory.FiberedCategoryOver.comp

open Bicategory
open scoped CategoryTheory.Bicategory

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]

namespace map

/-- The total functor of a fibred-category morphism over `B` preserves strongly
cartesian morphisms after both projections are postcomposed with a faithful
fibred functor `G : B ⥤ C`. -/
@[stacks 09WV "cartesian morphism of composite fibred categories"]
theorem preservesStronglyCartesian
    (G : B ⥤ C) [G.IsFibered] [G.Faithful]
    {X Y : FiberedCategoryOver.{uB, vB, uA, vA} B} (F : X ⟶ Y) :
    (BasedFunctor.ofFunctor
      (FiberedCategoryOver.toFunctor F) (comp.map_comm F G)).PreservesStronglyCartesian := sorry

end map

/-- Postcompose a morphism of fibred categories with a faithful fibred functor.
The total functor is unchanged. -/
@[stacks 09WV "morphism of composite fibred categories"]
def map (G : B ⥤ C) [G.IsFibered] [G.Faithful]
    {X Y : FiberedCategoryOver.{uB, vB, uA, vA} B} (F : X ⟶ Y) :
    X.comp G ⟶ Y.comp G :=
  FiberedCategoryOver.ofBasedFunctor
    (BasedFunctor.ofFunctor
      (FiberedCategoryOver.toFunctor F) (comp.map_comm F G))
    (map.preservesStronglyCartesian G F)

namespace map

/-- The total functor of `comp.map G F` is the total functor of `F`. -/
@[simp, stacks 09WV "composite fibred-category morphism projection"]
theorem toFunctor
    (G : B ⥤ C) [G.IsFibered] [G.Faithful]
    {X Y : FiberedCategoryOver.{uB, vB, uA, vA} B} (F : X ⟶ Y) :
    FiberedCategoryOver.toFunctor (map G F) =
      FiberedCategoryOver.toFunctor F := sorry

end map

namespace map₂

/-- The total natural transformation of a `2`-morphism over `B` is vertical
for the postcomposed projections to `C`. -/
@[stacks 09WV "composite fibred-category 2-morphism equation"]
theorem overId
    (G : B ⥤ C) [G.IsFibered] [G.Faithful]
    {X Y : FiberedCategoryOver.{uB, vB, uA, vA} B}
    {F H : X ⟶ Y} (eta : F ⟶ H) :
    eqToHom (FiberedCategoryOver.toBasedFunctor (map G F)).w.symm ≫
        Functor.whiskerRight (FiberedCategoryOver.toNatTrans eta) (Y.comp G).p ≫
          eqToHom (FiberedCategoryOver.toBasedFunctor (map G H)).w =
      𝟙 (X.comp G).p := sorry

end map₂

/-- Postcompose a `2`-morphism of fibred-category morphisms with a faithful
fibred functor. The total natural transformation is unchanged. -/
@[stacks 09WV "2-morphism of composite fibred categories"]
def map₂ (G : B ⥤ C) [G.IsFibered] [G.Faithful]
    {X Y : FiberedCategoryOver.{uB, vB, uA, vA} B}
    {F H : X ⟶ Y} (eta : F ⟶ H) : map G F ⟶ map G H :=
  FiberedCategoryOver.ofBasedNatTrans
    (BasedNatTrans.ofOverId
      (FiberedCategoryOver.toNatTrans (X := X) (Y := Y) eta)
      (map₂.overId G eta))

namespace map₂

/-- The total natural transformation of `comp.map₂ G eta` is that of `eta`. -/
@[simp, stacks 09WV "composite fibred-category 2-morphism projection"]
theorem toNatTrans
    (G : B ⥤ C) [G.IsFibered] [G.Faithful]
    {X Y : FiberedCategoryOver.{uB, vB, uA, vA} B}
    {F H : X ⟶ Y} (eta : F ⟶ H) :
    FiberedCategoryOver.toNatTrans (map₂ G eta) =
      FiberedCategoryOver.toNatTrans eta := sorry

end map₂

/-- Two postcomposed `2`-morphisms agree when all of their total-category
components agree. -/
theorem map₂.ext
    (G : B ⥤ C) [G.IsFibered] [G.Faithful]
    {X Y : FiberedCategoryOver.{uB, vB, uA, vA} B}
    {F H : X ⟶ Y} {eta theta : F ⟶ H}
    (h : ∀ x : X.total,
      (FiberedCategoryOver.toNatTrans (map₂ G eta)).app x =
        (FiberedCategoryOver.toNatTrans (map₂ G theta)).app x) :
    map₂ G eta = map₂ G theta := sorry

/-- Postcomposition sends identity morphisms to identity morphisms. -/
@[simp, stacks 09WV "postcomposition preserves identity morphisms"]
theorem map.id
    (G : B ⥤ C) [G.IsFibered] [G.Faithful]
    (X : FiberedCategoryOver.{uB, vB, uA, vA} B) :
    map G (𝟙 X) = 𝟙 (X.comp G) := sorry

/-- Postcomposition sends composites to composites. -/
@[simp, stacks 09WV "postcomposition preserves morphism composition"]
theorem map_comp
    (G : B ⥤ C) [G.IsFibered] [G.Faithful]
    {X Y Z : FiberedCategoryOver.{uB, vB, uA, vA} B}
    (F : X ⟶ Y) (H : Y ⟶ Z) :
    map G (F ≫ H) = map G F ≫ map G H := sorry

/-- Postcomposition sends identity `2`-morphisms to identity `2`-morphisms. -/
@[simp, stacks 09WV "postcomposition preserves identity 2-morphisms"]
theorem map₂.id
    (G : B ⥤ C) [G.IsFibered] [G.Faithful]
    {X Y : FiberedCategoryOver.{uB, vB, uA, vA} B} (F : X ⟶ Y) :
    map₂ G (𝟙 F) = 𝟙 (map G F) := sorry

/-- Postcomposition preserves vertical composition of `2`-morphisms. -/
@[simp, stacks 09WV "postcomposition preserves 2-morphism composition"]
theorem map₂_comp
    (G : B ⥤ C) [G.IsFibered] [G.Faithful]
    {X Y : FiberedCategoryOver.{uB, vB, uA, vA} B}
    {F H K : X ⟶ Y} (eta : F ⟶ H) (theta : H ⟶ K) :
    map₂ G (eta ≫ theta) = map₂ G eta ≫ map₂ G theta := sorry

/-- Postcomposition preserves left whiskering, up to the transports supplied
by its strict composition law. -/
theorem map₂.whiskerLeft
    (G : B ⥤ C) [G.IsFibered] [G.Faithful]
    {X Y Z : FiberedCategoryOver.{uB, vB, uA, vA} B}
    (F : X ⟶ Y) {H K : Y ⟶ Z} (eta : H ⟶ K) :
    map₂ G (F ◁ eta) =
      eqToHom (map_comp G F H) ≫ map G F ◁ map₂ G eta ≫
        eqToHom (map_comp G F K).symm := sorry

/-- Postcomposition preserves right whiskering, up to the transports supplied
by its strict composition law. -/
theorem map₂.whiskerRight
    (G : B ⥤ C) [G.IsFibered] [G.Faithful]
    {X Y Z : FiberedCategoryOver.{uB, vB, uA, vA} B}
    {F H : X ⟶ Y} (eta : F ⟶ H) (K : Y ⟶ Z) :
    map₂ G (eta ▷ K) =
      eqToHom (map_comp G F K) ≫ map₂ G eta ▷ map G K ≫
        eqToHom (map_comp G H K).symm := sorry

/-- The strict-pseudofunctor core for postcomposition by `G`. -/
private def core (G : B ⥤ C) [G.IsFibered] [G.Faithful] :
    StrictPseudofunctorPreCore
      (FiberedCategoryOver.{uB, vB, uA, vA} B)
      (FiberedCategoryOver.{uC, vC, uA, vA} C) where
  obj X := X.comp G
  map := map G
  map₂ := map₂ G
  map_id := map.id G
  map_comp := map_comp G
  map₂_id := map₂.id G
  map₂_comp := map₂_comp G
  map₂_whisker_left := map₂.whiskerLeft G
  map₂_whisker_right := map₂.whiskerRight G

/-- Postcomposition by a faithful fibred functor, as a strict pseudofunctor on
fibred categories. -/
@[stacks 09WV "postcomposition of fibred categories"]
def functor (G : B ⥤ C) [G.IsFibered] [G.Faithful] :
    StrictPseudofunctor
      (FiberedCategoryOver.{uB, vB, uA, vA} B)
      (FiberedCategoryOver.{uC, vC, uA, vA} C) :=
  StrictPseudofunctor.mk'' (core G)

namespace functor

/-- Postcomposition acts on objects by `FiberedCategoryOver.comp`. -/
@[simp, stacks 09WV "postcomposition functor object"]
theorem obj
    (G : B ⥤ C) [G.IsFibered] [G.Faithful]
    (X : FiberedCategoryOver.{uB, vB, uA, vA} B) :
    (functor G).obj X = X.comp G := sorry

/-- Postcomposition acts on morphisms by `comp.map`. -/
@[simp, stacks 09WV "postcomposition functor morphism"]
theorem map
    (G : B ⥤ C) [G.IsFibered] [G.Faithful]
    {X Y : FiberedCategoryOver.{uB, vB, uA, vA} B} (F : X ⟶ Y) :
    (functor G).map F = comp.map G F := sorry

/-- Postcomposition acts on `2`-morphisms by `comp.map₂`. -/
@[simp, stacks 09WV "postcomposition functor 2-morphism"]
theorem map₂
    (G : B ⥤ C) [G.IsFibered] [G.Faithful]
    {X Y : FiberedCategoryOver.{uB, vB, uA, vA} B}
    {F H : X ⟶ Y} (eta : F ⟶ H) :
    (functor G).map₂ eta = comp.map₂ G eta := sorry

end functor

/- The non-`Prop` payloads of `map`, `map₂`, and `functor` are the supplied
total functors and natural transformations. Any `sorryAx` is confined to
cartesian-preservation, verticality, and pseudofunctor coherence laws. -/

end CategoryTheory.FiberedCategoryOver.comp
