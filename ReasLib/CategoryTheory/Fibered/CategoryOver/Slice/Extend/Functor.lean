/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.Slice.Extend
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Composition.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functorial extension along a faithful fibration in groupoids

Extension along a faithful fibration in groupoids `G : B ⥤ C` is functorial on
morphisms and `2`-morphisms of fibred categories over `B`. The ambient action
is inherited from `FiberedCategoryOver.comp.functor`; this module only packages
its strict triangles over `FiberedCategoryOver.ofFunctor G`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe uB vB uC vC

namespace CategoryTheory.FiberedCategoryOver.Slice.Extend

open Bicategory
open scoped CategoryTheory.Bicategory

variable {B : Type uB} {C : Type uC}
variable [Category.{vB} B] [Category.{vC} C]

namespace map

/-- The postcomposed ambient morphism commutes with the canonical structural
maps to the fibred category associated to `G`. -/
theorem comm (G : B ⥤ C) [Functor.IsFibered.InGroupoids G] [G.Faithful]
    {X Y : FiberedCategoryOver.{uB, vB, uB, vB} B} (F : X ⟶ Y) :
    FiberedCategoryOver.comp.map G F ≫ hom G Y = hom G X := sorry

end map

/-- Extension on `1`-morphisms, packaged in the strict slice over the fibred
category associated to `G`. -/
def map (G : B ⥤ C) [Functor.IsFibered.InGroupoids G] [G.Faithful]
    {X Y : FiberedCategoryOver.{uB, vB, uB, vB} B} (F : X ⟶ Y) :
    obj G X ⟶ obj G Y :=
  StrictSlice.Hom.mk (FiberedCategoryOver.comp.map G F) (map.comm G F)

namespace map

/-- The ambient morphism underlying `map G F` is `comp.map G F`. -/
@[simp]
theorem hom (G : B ⥤ C) [Functor.IsFibered.InGroupoids G] [G.Faithful]
    {X Y : FiberedCategoryOver.{uB, vB, uB, vB} B} (F : X ⟶ Y) :
    StrictSlice.Hom.hom (map G F) = FiberedCategoryOver.comp.map G F := sorry

/-- The total functor underlying extension on a `1`-morphism is the original
total functor. -/
@[simp]
theorem toFunctor (G : B ⥤ C) [Functor.IsFibered.InGroupoids G] [G.Faithful]
    {X Y : FiberedCategoryOver.{uB, vB, uB, vB} B} (F : X ⟶ Y) :
    FiberedCategoryOver.toFunctor (StrictSlice.Hom.hom (map G F)) =
      FiberedCategoryOver.toFunctor F := sorry

end map

namespace map₂

/-- The postcomposed ambient `2`-morphism is compatible with the strict-slice
triangles determined by `map`. -/
theorem comm (G : B ⥤ C) [Functor.IsFibered.InGroupoids G] [G.Faithful]
    {X Y : FiberedCategoryOver.{uB, vB, uB, vB} B}
    {F H : X ⟶ Y} (eta : F ⟶ H) :
    FiberedCategoryOver.comp.map₂ G eta ▷ hom G Y ≫
        eqToHom (StrictSlice.Hom.comm (map G H)) =
      eqToHom (StrictSlice.Hom.comm (map G F)) := sorry

end map₂

/-- Extension on `2`-morphisms, packaged in the strict slice over the fibred
category associated to `G`. -/
def map₂ (G : B ⥤ C) [Functor.IsFibered.InGroupoids G] [G.Faithful]
    {X Y : FiberedCategoryOver.{uB, vB, uB, vB} B}
    {F H : X ⟶ Y} (eta : F ⟶ H) : map G F ⟶ map G H :=
  StrictSlice.Hom₂.mk (FiberedCategoryOver.comp.map₂ G eta) (map₂.comm G eta)

namespace map₂

/-- The ambient cell underlying `map₂ G eta` is `comp.map₂ G eta`. -/
@[simp]
theorem hom (G : B ⥤ C) [Functor.IsFibered.InGroupoids G] [G.Faithful]
    {X Y : FiberedCategoryOver.{uB, vB, uB, vB} B}
    {F H : X ⟶ Y} (eta : F ⟶ H) :
    StrictSlice.Hom₂.hom (map₂ G eta) =
      FiberedCategoryOver.comp.map₂ G eta := sorry

end map₂

/-- Two extension `2`-morphisms agree when all components of their ambient
total natural transformations agree. -/
theorem map₂.ext
    (G : B ⥤ C) [Functor.IsFibered.InGroupoids G] [G.Faithful]
    {X Y : FiberedCategoryOver.{uB, vB, uB, vB} B}
    {F H : X ⟶ Y} {eta theta : F ⟶ H}
    (h : ∀ x : X.total,
      (FiberedCategoryOver.toNatTrans
        (StrictSlice.Hom₂.hom (map₂ G eta))).app x =
      (FiberedCategoryOver.toNatTrans
        (StrictSlice.Hom₂.hom (map₂ G theta))).app x) :
    map₂ G eta = map₂ G theta := sorry

/-- Extension along `G` sends identity morphisms to identity morphisms. -/
@[simp]
theorem map.id (G : B ⥤ C) [Functor.IsFibered.InGroupoids G] [G.Faithful]
    (X : FiberedCategoryOver.{uB, vB, uB, vB} B) :
    map G (𝟙 X) = 𝟙 (obj G X) := sorry

/-- Extension along `G` sends composites to composites. -/
@[simp]
theorem map.comp (G : B ⥤ C) [Functor.IsFibered.InGroupoids G] [G.Faithful]
    {X Y Z : FiberedCategoryOver.{uB, vB, uB, vB} B}
    (F : X ⟶ Y) (H : Y ⟶ Z) :
    map G (F ≫ H) = map G F ≫ map G H := sorry

/-- Extension along `G` sends identity `2`-morphisms to identity
`2`-morphisms. -/
@[simp]
theorem map₂.id (G : B ⥤ C) [Functor.IsFibered.InGroupoids G] [G.Faithful]
    {X Y : FiberedCategoryOver.{uB, vB, uB, vB} B} (F : X ⟶ Y) :
    map₂ G (𝟙 F) = 𝟙 (map G F) := sorry

/-- Extension along `G` preserves vertical composition of `2`-morphisms. -/
@[simp]
theorem map₂.comp (G : B ⥤ C) [Functor.IsFibered.InGroupoids G] [G.Faithful]
    {X Y : FiberedCategoryOver.{uB, vB, uB, vB} B}
    {F H K : X ⟶ Y} (eta : F ⟶ H) (theta : H ⟶ K) :
    map₂ G (eta ≫ theta) = map₂ G eta ≫ map₂ G theta := sorry

/-- Extension along `G` preserves left whiskering with the transports
determined by its strict composition law. -/
theorem map₂.whiskerLeft (G : B ⥤ C)
    [Functor.IsFibered.InGroupoids G] [G.Faithful]
    {X Y Z : FiberedCategoryOver.{uB, vB, uB, vB} B}
    (F : X ⟶ Y) {H K : Y ⟶ Z} (eta : H ⟶ K) :
    map₂ G (F ◁ eta) =
      eqToHom (map.comp G F H) ≫ map G F ◁ map₂ G eta ≫
        eqToHom (map.comp G F K).symm := sorry

/-- Extension along `G` preserves right whiskering with the transports
determined by its strict composition law. -/
theorem map₂.whiskerRight (G : B ⥤ C)
    [Functor.IsFibered.InGroupoids G] [G.Faithful]
    {X Y Z : FiberedCategoryOver.{uB, vB, uB, vB} B}
    {F H : X ⟶ Y} (eta : F ⟶ H) (K : Y ⟶ Z) :
    map₂ G (eta ▷ K) =
      eqToHom (map.comp G F K) ≫ map₂ G eta ▷ map G K ≫
        eqToHom (map.comp G H K).symm := sorry

/-- The strict-pseudofunctor core of topology-independent extension along
`G`. -/
private def core (G : B ⥤ C) [Functor.IsFibered.InGroupoids G] [G.Faithful] :
    StrictPseudofunctorPreCore
      (FiberedCategoryOver.{uB, vB, uB, vB} B)
      (StrictSlice (FiberedCategoryOver.ofFunctor G)) where
  obj := obj G
  map := map G
  map₂ := map₂ G
  map_id := map.id G
  map_comp := map.comp G
  map₂_id := map₂.id G
  map₂_comp := map₂.comp G
  map₂_whisker_left := map₂.whiskerLeft G
  map₂_whisker_right := map₂.whiskerRight G

/-- Topology-independent extension along `G` from fibred categories over `B`
to the strict slice over the fibred category associated to `G`. -/
def functor (G : B ⥤ C) [Functor.IsFibered.InGroupoids G] [G.Faithful] :
    StrictPseudofunctor
      (FiberedCategoryOver.{uB, vB, uB, vB} B)
      (StrictSlice (FiberedCategoryOver.ofFunctor G)) :=
  StrictPseudofunctor.mk'' (core G)

namespace functor

/-- The extension strict pseudofunctor acts on objects by `Extend.obj`. -/
@[simp]
theorem obj (G : B ⥤ C) [Functor.IsFibered.InGroupoids G] [G.Faithful]
    (X : FiberedCategoryOver.{uB, vB, uB, vB} B) :
    (functor G).obj X = Extend.obj G X := sorry

/-- The extension strict pseudofunctor acts on morphisms by `Extend.map`. -/
@[simp]
theorem map (G : B ⥤ C) [Functor.IsFibered.InGroupoids G] [G.Faithful]
    {X Y : FiberedCategoryOver.{uB, vB, uB, vB} B} (F : X ⟶ Y) :
    (functor G).map F = Extend.map G F := sorry

/-- The extension strict pseudofunctor acts on `2`-morphisms by
`Extend.map₂`. -/
@[simp]
theorem map₂ (G : B ⥤ C) [Functor.IsFibered.InGroupoids G] [G.Faithful]
    {X Y : FiberedCategoryOver.{uB, vB, uB, vB} B}
    {F H : X ⟶ Y} (eta : F ⟶ H) :
    (functor G).map₂ eta = Extend.map₂ G eta := sorry

end functor

/- The non-`Prop` payloads below are inherited from `comp.map` and
`comp.map₂`; this layer only adds strict-slice packaging. Any `sorryAx` is
confined to triangle and pseudofunctor coherence laws. -/

end CategoryTheory.FiberedCategoryOver.Slice.Extend
