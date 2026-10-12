/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Reindex.Chosen.Construction
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Reindex.Explicit.Equivalence
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.ChosenCleavage
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open Opposite
open scoped CategoricalPullback CategoryTheory.Bicategory

universe u v

namespace CategoryTheory

namespace FiberedCategoryOver.PseudoPullback.reindex.chosen

universe w vT

variable {C : Type u} [Category.{v} C]
variable {X Y S : FiberedCategoryOver.{u, v, w, vT} C}

/-- The first-projection comparison between selected actual reindexing in the
pseudo-pullback and selected componentwise reindexing in its fiber model. -/
@[stacks 0040 "first projection of selected pseudo-pullback reindexing"]
noncomputable def fstIso
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U) :
    (Functor.Chosen.reindex
        (BasedCategory.PseudoPullback
          (toBasedFunctor F) (toBasedFunctor G)).p f ⋙
      (BasedCategory.PseudoPullback.Fiber.comparison
        (toBasedFunctor F) (toBasedFunctor G) V)) ⋙
        π₁ (fiberFunctor F V) (fiberFunctor G V) ≅
    (BasedCategory.PseudoPullback.Fiber.comparison
        (toBasedFunctor F) (toBasedFunctor G) U ⋙
      functor F G f) ⋙
        π₁ (fiberFunctor F V) (fiberFunctor G V) :=
  BasedCategory.PseudoPullback.Fiber.reindex.fstIso
    (toCartesianBasedFunctor F) (toCartesianBasedFunctor G)
    (FiberedCategoryOver.PseudoPullback.chosenCleavage F G)
    X.chosenCleavage Y.chosenCleavage S.chosenCleavage f

/-- The second-projection comparison between selected actual reindexing in the
pseudo-pullback and selected componentwise reindexing in its fiber model. -/
@[stacks 0040 "second projection of selected pseudo-pullback reindexing"]
noncomputable def sndIso
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U) :
    (Functor.Chosen.reindex
        (BasedCategory.PseudoPullback
          (toBasedFunctor F) (toBasedFunctor G)).p f ⋙
      (BasedCategory.PseudoPullback.Fiber.comparison
        (toBasedFunctor F) (toBasedFunctor G) V)) ⋙
        π₂ (fiberFunctor F V) (fiberFunctor G V) ≅
    (BasedCategory.PseudoPullback.Fiber.comparison
        (toBasedFunctor F) (toBasedFunctor G) U ⋙
      functor F G f) ⋙
        π₂ (fiberFunctor F V) (fiberFunctor G V) :=
  BasedCategory.PseudoPullback.Fiber.reindex.sndIso
    (toCartesianBasedFunctor F) (toCartesianBasedFunctor G)
    (FiberedCategoryOver.PseudoPullback.chosenCleavage F G)
    X.chosenCleavage Y.chosenCleavage S.chosenCleavage f

/-- The selected-cleavage naturality isomorphism identifying reindexing in the actual
pseudo-pullback fiber with reindexing in its categorical-pullback model. -/
@[stacks 0040 "selected reindexing comparison for a pseudo-pullback fiber model"]
noncomputable def iso
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U) :
    Functor.Chosen.reindex
        (BasedCategory.PseudoPullback
          (toBasedFunctor F) (toBasedFunctor G)).p f ⋙
      (BasedCategory.PseudoPullback.Fiber.comparison
        (toBasedFunctor F) (toBasedFunctor G) V) ≅
    (BasedCategory.PseudoPullback.Fiber.comparison
        (toBasedFunctor F) (toBasedFunctor G) U) ⋙
      functor F G f :=
  BasedCategory.PseudoPullback.Fiber.reindex.iso
    (toCartesianBasedFunctor F) (toCartesianBasedFunctor G)
    (FiberedCategoryOver.PseudoPullback.chosenCleavage F G)
    X.chosenCleavage Y.chosenCleavage S.chosenCleavage f

/-- The selected actual-to-modeled reindexing comparison is the explicit comparison specialized
to the cleavages selected from the pseudo-pullback and its cospan. -/
theorem iso.eqExplicit
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U) :
    iso F G f =
      BasedCategory.PseudoPullback.Fiber.reindex.iso
        (toCartesianBasedFunctor F) (toCartesianBasedFunctor G)
        (FiberedCategoryOver.PseudoPullback.chosenCleavage F G)
        X.chosenCleavage Y.chosenCleavage S.chosenCleavage f := sorry

namespace iso

/-- The first component of the forward selected actual-to-modeled reindexing comparison. -/
@[simp]
theorem hom.fst
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U)
    (P : Functor.Fiber
      (BasedCategory.PseudoPullback
        (toBasedFunctor F) (toBasedFunctor G)).p U) :
    ((iso F G f).hom.app P).fst =
      (fstIso F G f).hom.app P := sorry

/-- The second component of the forward selected actual-to-modeled reindexing comparison. -/
@[simp]
theorem hom.snd
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U)
    (P : Functor.Fiber
      (BasedCategory.PseudoPullback
        (toBasedFunctor F) (toBasedFunctor G)).p U) :
    ((iso F G f).hom.app P).snd =
      (sndIso F G f).hom.app P := sorry

/-- The first component of the inverse selected actual-to-modeled reindexing comparison. -/
@[simp]
theorem inv.fst
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U)
    (P : Functor.Fiber
      (BasedCategory.PseudoPullback
        (toBasedFunctor F) (toBasedFunctor G)).p U) :
    ((iso F G f).inv.app P).fst =
      (fstIso F G f).inv.app P := sorry

/-- The second component of the inverse selected actual-to-modeled reindexing comparison. -/
@[simp]
theorem inv.snd
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U)
    (P : Functor.Fiber
      (BasedCategory.PseudoPullback
        (toBasedFunctor F) (toBasedFunctor G)).p U) :
    ((iso F G f).inv.app P).snd =
      (sndIso F G f).inv.app P := sorry

/-- Compatibility of the forward selected actual-to-modeled comparison with composition of base
arrows. -/
theorem mapComp.hom
    (F : X ⟶ S) (G : Y ⟶ S) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V)
    (P : Functor.Fiber
      (BasedCategory.PseudoPullback
        (toBasedFunctor F) (toBasedFunctor G)).p U) :
    (iso F G (g ≫ f)).hom.app P ≫
        (mapCompIso F G f g).hom.app
          ((BasedCategory.PseudoPullback.Fiber.comparison
          (toBasedFunctor F) (toBasedFunctor G) U).obj P) =
      (BasedCategory.PseudoPullback.Fiber.comparison
          (toBasedFunctor F) (toBasedFunctor G) W).map
          (Functor.Chosen.Reindex.compIsoApp
            (BasedCategory.PseudoPullback
              (toBasedFunctor F) (toBasedFunctor G)).p f g P).hom ≫
        (iso F G g).hom.app
          ((Functor.Chosen.reindex
            (BasedCategory.PseudoPullback
              (toBasedFunctor F) (toBasedFunctor G)).p f).obj P) ≫
        (functor F G g).map
          ((iso F G f).hom.app P) := sorry

/-- Compatibility of the inverse selected actual-to-modeled comparison with composition of base
arrows. -/
theorem mapComp.inv
    (F : X ⟶ S) (G : Y ⟶ S) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V)
    (P : Functor.Fiber
      (BasedCategory.PseudoPullback
        (toBasedFunctor F) (toBasedFunctor G)).p U) :
    (mapCompIso F G f g).inv.app
          ((BasedCategory.PseudoPullback.Fiber.comparison
          (toBasedFunctor F) (toBasedFunctor G) U).obj P) ≫
        (iso F G (g ≫ f)).inv.app P =
      (functor F G g).map
          ((iso F G f).inv.app P) ≫
        (iso F G g).inv.app
          ((Functor.Chosen.reindex
            (BasedCategory.PseudoPullback
              (toBasedFunctor F) (toBasedFunctor G)).p f).obj P) ≫
        (BasedCategory.PseudoPullback.Fiber.comparison
          (toBasedFunctor F) (toBasedFunctor G) W).map
          (Functor.Chosen.Reindex.compIsoApp
            (BasedCategory.PseudoPullback
              (toBasedFunctor F) (toBasedFunctor G)).p f g P).inv := sorry

/-- Compatibility of the forward selected actual-to-modeled comparison with identity
reindexing. -/
theorem mapId.hom
    (F : X ⟶ S) (G : Y ⟶ S) {U : C}
    (P : Functor.Fiber
      (BasedCategory.PseudoPullback
        (toBasedFunctor F) (toBasedFunctor G)).p U) :
    (BasedCategory.PseudoPullback.Fiber.comparison
          (toBasedFunctor F) (toBasedFunctor G) U).map
          (Functor.Chosen.Reindex.idIsoApp
            (BasedCategory.PseudoPullback
              (toBasedFunctor F) (toBasedFunctor G)).p U P).hom ≫
        (iso F G (𝟙 U)).hom.app P =
      (idIso F G U).hom.app
        ((BasedCategory.PseudoPullback.Fiber.comparison
          (toBasedFunctor F) (toBasedFunctor G) U).obj P) := sorry

/-- Compatibility of the inverse selected actual-to-modeled comparison with identity
reindexing. -/
theorem mapId.inv
    (F : X ⟶ S) (G : Y ⟶ S) {U : C}
    (P : Functor.Fiber
      (BasedCategory.PseudoPullback
        (toBasedFunctor F) (toBasedFunctor G)).p U) :
    (idIso F G U).inv.app
          ((BasedCategory.PseudoPullback.Fiber.comparison
          (toBasedFunctor F) (toBasedFunctor G) U).obj P) =
      (iso F G (𝟙 U)).inv.app P ≫
        (BasedCategory.PseudoPullback.Fiber.comparison
          (toBasedFunctor F) (toBasedFunctor G) U).map
          (Functor.Chosen.Reindex.idIsoApp
            (BasedCategory.PseudoPullback
              (toBasedFunctor F) (toBasedFunctor G)).p U P).inv := sorry

end iso

end FiberedCategoryOver.PseudoPullback.reindex.chosen

end CategoryTheory
