/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Morphism.Reindex

/-!
# Composition coherence for selected reindexing comparisons

This module records compatibility of selected-cleavage comparison isomorphisms
with composition of morphisms of fibred categories and with specified
composition in the base category.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

open Bicategory Functor Opposite
open scoped CategoryTheory.Bicategory

namespace FiberedCategoryOver

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, uS, vS} C}

/-- The selected-cleavage comparison for a composite owner morphism is the composite of the
individual comparison isomorphisms. -/
theorem Reindex.mapIso.comp {Z : FiberedCategoryOver.{u, v, uS, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    Reindex.mapIso (F ≫ G) f x =
      Reindex.mapIso G f ((fiberFunctor F U).obj x) ≪≫
        (fiberFunctor G V).mapIso (Reindex.mapIso F f x) := sorry

/-- The forward comparison for a composite owner morphism is the composite of the two forward
comparison maps. -/
theorem Reindex.mapIso.comp.hom {Z : FiberedCategoryOver.{u, v, uS, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    (Reindex.mapIso (F ≫ G) f x).hom =
      (Reindex.mapIso G f ((fiberFunctor F U).obj x)).hom ≫
        (fiberFunctor G V).map (Reindex.mapIso F f x).hom := sorry

/-- The inverse comparison for a composite owner morphism is the reverse composite of the two
inverse comparison maps. -/
theorem Reindex.mapIso.comp.inv {Z : FiberedCategoryOver.{u, v, uS, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    (Reindex.mapIso (F ≫ G) f x).inv =
      (fiberFunctor G V).map (Reindex.mapIso F f x).inv ≫
        (Reindex.mapIso G f ((fiberFunctor F U).obj x)).inv := sorry

/-- Total-category readout of `Reindex.mapIso.comp.hom`. -/
theorem Reindex.mapIso.comp.totalHom
    {Z : FiberedCategoryOver.{u, v, uS, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    (Reindex.mapIso (F ≫ G) f x).hom.1 =
      (Reindex.mapIso G f ((fiberFunctor F U).obj x)).hom.1 ≫
        ((fiberFunctor G V).map (Reindex.mapIso F f x).hom).1 := sorry

/-- Total-category readout of `Reindex.mapIso.comp.inv`. -/
theorem Reindex.mapIso.comp.totalInv
    {Z : FiberedCategoryOver.{u, v, uS, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    (Reindex.mapIso (F ≫ G) f x).inv.1 =
      ((fiberFunctor G V).map (Reindex.mapIso F f x).inv).1 ≫
        (Reindex.mapIso G f ((fiberFunctor F U).obj x)).inv.1 := sorry

/-- The selected-cleavage comparison is compatible with a specified composite of base arrows. -/
theorem Reindex.mapIso.specifiedComp.hom (F : X ⟶ Y)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (gf : W ⟶ U)
    (hgf : g ≫ f = gf) (x : X.p.Fiber U) :
    (Functor.Chosen.Reindex.specifiedCompIsoApp Y.p f g gf hgf
          ((fiberFunctor F U).obj x)).hom ≫
        Functor.Chosen.reindexMap Y.p g (Reindex.mapIso F f x).hom ≫
        (Reindex.mapIso F g (Functor.Chosen.reindexObj X.p f x)).hom =
      (Reindex.mapIso F gf x).hom ≫
        (fiberFunctor F W).map
          (Functor.Chosen.Reindex.specifiedCompIsoApp X.p f g gf hgf x).hom := sorry

/-- Cancellation form of selected-cleavage composition coherence. -/
theorem Reindex.mapIso.specifiedComp.boundary (F : X ⟶ Y)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (gf : W ⟶ U)
    (hgf : g ≫ f = gf) (x : X.p.Fiber U) :
    (Functor.Chosen.Reindex.specifiedCompIsoApp Y.p f g gf hgf
          ((fiberFunctor F U).obj x)).hom ≫
        Functor.Chosen.reindexMap Y.p g (Reindex.mapIso F f x).hom =
      (Reindex.mapIso F gf x).hom ≫
        (fiberFunctor F W).map
          (Functor.Chosen.Reindex.specifiedCompIsoApp X.p f g gf hgf x).hom ≫
        (Reindex.mapIso F g (Functor.Chosen.reindexObj X.p f x)).inv := sorry

/-- Inverse form of selected-cleavage composition coherence. -/
theorem Reindex.mapIso.specifiedComp.inv (F : X ⟶ Y)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (gf : W ⟶ U)
    (hgf : g ≫ f = gf) (x : X.p.Fiber U) :
    (Reindex.mapIso F g (Functor.Chosen.reindexObj X.p f x)).inv ≫
        Functor.Chosen.reindexMap Y.p g (Reindex.mapIso F f x).inv ≫
        (Functor.Chosen.Reindex.specifiedCompIsoApp Y.p f g gf hgf
          ((fiberFunctor F U).obj x)).inv =
      (fiberFunctor F W).map
          (Functor.Chosen.Reindex.specifiedCompIsoApp X.p f g gf hgf x).inv ≫
        (Reindex.mapIso F gf x).inv := sorry

/-- The selected reindexing comparison is compatible with a specified composite as an equality
of fiber isomorphisms.

This packages `Reindex.mapIso.specifiedComp.hom` as an equality of the canonical selected-cleavage
comparison isomorphisms. -/
theorem Reindex.mapIso.specifiedComp.cocycle
    (F : X ⟶ Y) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V) {gf : W ⟶ U}
    (hgf : g ≫ f = gf) (x : X.p.Fiber U) :
    (Functor.Chosen.Reindex.specifiedCompIsoApp Y.p f g gf hgf
        ((fiberFunctor F U).obj x) ≪≫
      ((Functor.fiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.mapIso
        (Reindex.mapIso F f x) ≪≫
        Reindex.mapIso F g
          (f⁎[X.chosenCleavage] x)) =
      Reindex.mapIso F gf x ≪≫
        (fiberFunctor F W).mapIso
          (Functor.Chosen.Reindex.specifiedCompIsoApp X.p f g gf hgf x) := sorry

/-- The inverse comparison over a composite, the target composition comparison, and the
selected cartesian arrow over the second factor reduce to the image of the corresponding
source composite after the forward comparison over the first factor.

This is the total-category normalization of selected reindexing composition coherence. -/
theorem Reindex.mapIso.specifiedComp.invCartesian (F : X ⟶ Y)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (gf : W ⟶ U)
    (hgf : g ≫ f = gf) (x : X.p.Fiber U) :
    (Reindex.mapIso F gf x).inv.1 ≫
        (Functor.Chosen.Reindex.specifiedCompIsoApp Y.p f g gf hgf
          ((fiberFunctor F U).obj x)).hom.1 ≫
        Functor.Chosen.cartesianHom Y.p g
          (Functor.Chosen.reindexObj Y.p f ((fiberFunctor F U).obj x)) ≫
        (Reindex.mapIso F f x).hom.1 =
      (toFunctor F).map
        ((Functor.Chosen.Reindex.specifiedCompIsoApp X.p f g gf hgf x).hom.1 ≫
          Functor.Chosen.cartesianHom X.p g
            (Functor.Chosen.reindexObj X.p f x)) := sorry

end FiberedCategoryOver

end CategoryTheory
