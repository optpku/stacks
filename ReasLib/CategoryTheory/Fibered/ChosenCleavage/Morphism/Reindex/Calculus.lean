module

public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Morphism.Reindex

/-!
# Calculus for selected reindexing comparisons

These conjugation formulas expose the objectwise selected-cleavage comparison
in the two presentations used by downstream fiber calculations.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

open Bicategory Functor Opposite
open scoped CategoryTheory.Bicategory

namespace FiberedCategoryOver

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, uS, vS} C}

/-- Applying a morphism of fibred categories to a chosen-reindexed fiber morphism is the chosen
reindexing of its image conjugated by the two comparison isomorphisms. -/
theorem Reindex.mapIso.conjugation.fiber (F : X ⟶ Y) {U V : C}
    (f : V ⟶ U) {x y : X.p.Fiber U} (α : x ⟶ y) :
    (fiberFunctor F V).map ((Functor.Chosen.reindex X.p f).map α) =
      (Reindex.mapIso F f x).inv ≫
        (Functor.Chosen.reindex Y.p f).map ((fiberFunctor F U).map α) ≫
        (Reindex.mapIso F f y).hom := sorry

/-- Chosen reindexing of the image of a fiber morphism is the image of its chosen reindexing
conjugated by the forward comparison isomorphisms. -/
theorem Reindex.mapIso.conjugation.chosen (F : X ⟶ Y) {U V : C}
    (f : V ⟶ U) {x y : X.p.Fiber U} (α : x ⟶ y) :
    (Functor.Chosen.reindex Y.p f).map ((fiberFunctor F U).map α) =
      (Reindex.mapIso F f x).hom ≫
        (fiberFunctor F V).map ((Functor.Chosen.reindex X.p f).map α) ≫
        (Reindex.mapIso F f y).inv := sorry

/-- Total-category readout of `Reindex.mapIso.conjugation.fiber`. -/
theorem Reindex.mapIso.conjugation.totalFiber (F : X ⟶ Y) {U V : C}
    (f : V ⟶ U) {x y : X.p.Fiber U} (α : x ⟶ y) :
    ((fiberFunctor F V).map ((Functor.Chosen.reindex X.p f).map α)).1 =
      (Reindex.mapIso F f x).inv.1 ≫
        ((Functor.Chosen.reindex Y.p f).map ((fiberFunctor F U).map α)).1 ≫
        (Reindex.mapIso F f y).hom.1 := sorry

/-- Total-category readout of `Reindex.mapIso.conjugation.chosen`. -/
theorem Reindex.mapIso.conjugation.totalChosen (F : X ⟶ Y) {U V : C}
    (f : V ⟶ U) {x y : X.p.Fiber U} (α : x ⟶ y) :
    ((Functor.Chosen.reindex Y.p f).map ((fiberFunctor F U).map α)).1 =
      (Reindex.mapIso F f x).hom.1 ≫
        ((fiberFunctor F V).map ((Functor.Chosen.reindex X.p f).map α)).1 ≫
        (Reindex.mapIso F f y).inv.1 := sorry

/-- Map-presentation form of `Reindex.mapIso.conjugation.fiber`, for calculations phrased through
the selected fiber pseudofunctors. -/
theorem Reindex.mapIso.conjugation.pseudofunctorFiber (F : X ⟶ Y) {U V : C}
    (f : V ⟶ U) {x y : X.p.Fiber U} (α : x ⟶ y) :
    (fiberFunctor F V).map
        (((Functor.fiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map α) =
      (Reindex.mapIso F f x).inv ≫
        ((Functor.fiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
          ((fiberFunctor F U).map α) ≫
        (Reindex.mapIso F f y).hom := sorry

/-- Reverse conjugation form of `Reindex.mapIso.conjugation.pseudofunctorFiber`. -/
theorem Reindex.mapIso.conjugation.pseudofunctorChosen (F : X ⟶ Y) {U V : C}
    (f : V ⟶ U) {x y : X.p.Fiber U} (α : x ⟶ y) :
    ((Functor.fiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
        ((fiberFunctor F U).map α) =
      (Reindex.mapIso F f x).hom ≫
        (fiberFunctor F V).map
          (((Functor.fiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map α) ≫
        (Reindex.mapIso F f y).inv := sorry

end FiberedCategoryOver

end CategoryTheory
