/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Reindex
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Cleavage
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Pseudofunctor

/-!
# Selected-cleavage reindexing comparisons

This module gives the objectwise comparison between the selected reindexing
functors induced by a morphism of fibred categories.  The choice-free owner is
`CartesianBasedFunctor.Reindex.mapIso`; the declarations here specialize it
along the named bundled choice boundary `FiberedCategoryOver.chosenCleavage`.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

open Bicategory Functor Opposite
open scoped CategoryTheory.Bicategory

namespace FiberedCategoryOver

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, uS, vS} C}

/-- The selected-cleavage comparison
`f⁎(F x) ≅ F(f⁎x)` for a morphism of fibred categories. -/
noncomputable def Reindex.mapIso (F : X ⟶ Y) {U V : C} (f : V ⟶ U)
    (x : X.p.Fiber U) :
    (Functor.Chosen.reindex Y.p f).obj ((fiberFunctor F U).obj x) ≅
      (fiberFunctor F V).obj ((Functor.Chosen.reindex X.p f).obj x) :=
  CartesianBasedFunctor.Reindex.mapIso
    (toCartesianBasedFunctor F) X.chosenCleavage Y.chosenCleavage f x

/-- The forward selected-cleavage comparison is a fiber morphism over the identity of the
reindexed base object. -/
theorem Reindex.mapIso.hom.isHomLift (F : X ⟶ Y) {U V : C}
    (f : V ⟶ U) (x : X.p.Fiber U) :
    Y.p.IsHomLift (𝟙 V) (Reindex.mapIso F f x).hom.1 := sorry

/-- The inverse selected-cleavage comparison is a fiber morphism over the identity of the
reindexed base object. -/
theorem Reindex.mapIso.inv.isHomLift (F : X ⟶ Y) {U V : C}
    (f : V ⟶ U) (x : X.p.Fiber U) :
    Y.p.IsHomLift (𝟙 V) (Reindex.mapIso F f x).inv.1 := sorry

/-- The forward selected-cleavage comparison is characterized by its composite with the image of
the selected source cartesian arrow. -/
theorem Reindex.mapIso.hom.fac (F : X ⟶ Y) {U V : C}
    (f : V ⟶ U) (x : X.p.Fiber U) :
    (Reindex.mapIso F f x).hom.1 ≫
        (toFunctor F).map (Functor.Chosen.cartesianHom X.p f x) =
      Functor.Chosen.cartesianHom Y.p f ((fiberFunctor F U).obj x) := sorry

/-- The inverse selected-cleavage comparison followed by the target cartesian arrow recovers the
image of the source cartesian arrow. -/
theorem Reindex.mapIso.inv.fac (F : X ⟶ Y) {U V : C}
    (f : V ⟶ U) (x : X.p.Fiber U) :
    (Reindex.mapIso F f x).inv.1 ≫
        Functor.Chosen.cartesianHom Y.p f ((fiberFunctor F U).obj x) =
      (toFunctor F).map (Functor.Chosen.cartesianHom X.p f x) := sorry

/-- The selected-cleavage reindexing comparison is natural in the source fiber object. -/
theorem Reindex.mapIso.hom.naturality (F : X ⟶ Y) {U V : C}
    (f : V ⟶ U) {x y : X.p.Fiber U} (α : x ⟶ y) :
    (Functor.Chosen.reindex Y.p f).map ((fiberFunctor F U).map α) ≫
        (Reindex.mapIso F f y).hom =
      (Reindex.mapIso F f x).hom ≫
        (fiberFunctor F V).map
          ((Functor.Chosen.reindex X.p f).map α) := sorry

/-- Naturality of the inverse selected-cleavage comparison. -/
theorem Reindex.mapIso.inv.naturality (F : X ⟶ Y) {U V : C}
    (f : V ⟶ U) {x y : X.p.Fiber U} (α : x ⟶ y) :
    (fiberFunctor F V).map ((Functor.Chosen.reindex X.p f).map α) ≫
        (Reindex.mapIso F f y).inv =
      (Reindex.mapIso F f x).inv ≫
        (Functor.Chosen.reindex Y.p f).map
          ((fiberFunctor F U).map α) := sorry

/-- Naturality of the forward comparison in the map presentation of the selected fiber
pseudofunctors. -/
theorem Reindex.mapIso.hom.mapNaturality (F : X ⟶ Y) {U V : C}
    (f : V ⟶ U) {x y : X.p.Fiber U} (α : x ⟶ y) :
    ((Functor.fiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
          ((fiberFunctor F U).map α) ≫
        (Reindex.mapIso F f y).hom =
      (Reindex.mapIso F f x).hom ≫
        (fiberFunctor F V).map
          (((Functor.fiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map α) := sorry

/-- Naturality of the inverse comparison in the map presentation of the selected fiber
pseudofunctors. -/
theorem Reindex.mapIso.inv.mapNaturality (F : X ⟶ Y) {U V : C}
    (f : V ⟶ U) {x y : X.p.Fiber U} (α : x ⟶ y) :
    (Reindex.mapIso F f x).inv ≫
        ((Functor.fiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
          ((fiberFunctor F U).map α) =
      (fiberFunctor F V).map
          (((Functor.fiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map α) ≫
        (Reindex.mapIso F f y).inv := sorry

end FiberedCategoryOver

end CategoryTheory
