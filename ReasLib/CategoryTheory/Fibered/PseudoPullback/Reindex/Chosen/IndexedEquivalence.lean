/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Reindex.Chosen.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Reindex.Chosen.Equivalence
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Reindex.Explicit.IndexedEquivalence
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open Opposite
open scoped CategoricalPullback CategoryTheory.Bicategory

universe u v

namespace CategoryTheory

namespace FiberedCategoryOver.PseudoPullback.reindex.chosen.indexed

universe w vT

variable {C : Type u} [Category.{v} C]
variable {X Y S : FiberedCategoryOver.{u, v, w, vT} C}

/-- Identity coherence for the selected indexed equivalence between actual pseudo-pullback
fibers and their categorical-pullback models. -/
theorem functor.naturality.id
    (F : X ⟶ S) (G : Y ⟶ S) {U : C}
    (P : Functor.Fiber
      (BasedCategory.PseudoPullback
        (toBasedFunctor F) (toBasedFunctor G)).p U) :
    (BasedCategory.PseudoPullback.Fiber.comparison
          (toBasedFunctor F) (toBasedFunctor G) U).map
          (((Functor.fiberPseudofunctor
            (BasedCategory.PseudoPullback
              (toBasedFunctor F) (toBasedFunctor G)).p).mapIdOp U).inv.toNatTrans.app P) ≫
        (iso F G (𝟙 U)).hom.app P =
      ((FiberedCategoryOver.PseudoPullback.reindex.chosen.pseudofunctor F G).mapIdOp'
        ((𝟭 C).obj U) ((𝟭 C).map (𝟙 U))
        ((𝟭 C).map_id U)).inv.toNatTrans.app
          ((BasedCategory.PseudoPullback.Fiber.comparison
          (toBasedFunctor F) (toBasedFunctor G) U).obj P) := sorry

/-- Composition coherence for the selected indexed equivalence between actual pseudo-pullback
fibers and their categorical-pullback models. -/
theorem functor.naturality.comp
    (F : X ⟶ S) (G : Y ⟶ S) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V)
    (P : Functor.Fiber
      (BasedCategory.PseudoPullback
        (toBasedFunctor F) (toBasedFunctor G)).p U) :
    (iso F G (g ≫ f)).hom.app P ≫
        ((FiberedCategoryOver.PseudoPullback.reindex.chosen.pseudofunctor F G).mapCompOp'
          ((𝟭 C).map f) ((𝟭 C).map g) ((𝟭 C).map (g ≫ f))
          ((𝟭 C).map_comp g f).symm).hom.toNatTrans.app
            ((BasedCategory.PseudoPullback.Fiber.comparison
          (toBasedFunctor F) (toBasedFunctor G) U).obj P) =
      (BasedCategory.PseudoPullback.Fiber.comparison
          (toBasedFunctor F) (toBasedFunctor G) W).map
          (((Functor.fiberPseudofunctor
            (BasedCategory.PseudoPullback
              (toBasedFunctor F) (toBasedFunctor G)).p).mapCompOp f g).hom.toNatTrans.app P) ≫
        (iso F G g).hom.app
          (((Functor.fiberPseudofunctor
            (BasedCategory.PseudoPullback
              (toBasedFunctor F) (toBasedFunctor G)).p).map f.op.toLoc).toFunctor.obj P) ≫
        ((FiberedCategoryOver.PseudoPullback.reindex.chosen.pseudofunctor F G).map
          ((𝟭 C).map g).op.toLoc).toFunctor.map
            ((iso F G f).hom.app P) := sorry

/-- The selected equivalences from actual pseudo-pullback fibers to their categorical-pullback
models form a coherent indexed functor over `𝟭 C`. -/
@[stacks 0040 "selected indexed equivalence for pseudo-pullback fiber models"]
noncomputable def functor
    (F : X ⟶ S) (G : Y ⟶ S) :
    Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor (𝟭 C)
      (Functor.fiberPseudofunctor
        (BasedCategory.PseudoPullback
          (toBasedFunctor F) (toBasedFunctor G)).p)
      (FiberedCategoryOver.PseudoPullback.reindex.chosen.pseudofunctor F G) :=
  BasedCategory.PseudoPullback.Fiber.reindex.indexed.functor
    (toCartesianBasedFunctor F) (toCartesianBasedFunctor G)
    (FiberedCategoryOver.PseudoPullback.chosenCleavage F G)
    X.chosenCleavage Y.chosenCleavage S.chosenCleavage

/-- The selected actual-to-modeled indexed comparison is the explicit indexed comparison
specialized to the cleavages selected from the pseudo-pullback and its cospan. -/
theorem functor.eqExplicit (F : X ⟶ S) (G : Y ⟶ S) :
    functor F G =
      BasedCategory.PseudoPullback.Fiber.reindex.indexed.functor
        (toCartesianBasedFunctor F) (toCartesianBasedFunctor G)
        (FiberedCategoryOver.PseudoPullback.chosenCleavage F G)
        X.chosenCleavage Y.chosenCleavage S.chosenCleavage := sorry

/-- Components of the selected actual-to-modeled indexed functor are the canonical comparison
functors; each component is an equivalence. -/
@[simp]
theorem functor.app
    (F : X ⟶ S) (G : Y ⟶ S) (U : C) :
    (functor F G).app U =
      (BasedCategory.PseudoPullback.Fiber.comparison
        (toBasedFunctor F) (toBasedFunctor G) U) := sorry

/-- Naturality of the selected actual-to-modeled indexed functor is the selected reindexing
comparison. -/
@[simp]
theorem functor.naturality
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U) :
    (functor F G).naturality f =
      iso F G f := sorry

/-- Restricted-morphism transport through the selected actual-to-modeled indexed functor is
conjugation by the two selected reindexing comparisons. -/
@[simp]
theorem functor.mapHom
    (F : X ⟶ S) (G : Y ⟶ S)
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {P : Functor.Fiber
      (BasedCategory.PseudoPullback
        (toBasedFunctor F) (toBasedFunctor G)).p U₁}
    {Q : Functor.Fiber
      (BasedCategory.PseudoPullback
        (toBasedFunctor F) (toBasedFunctor G)).p U₂}
    (φ :
      (Functor.Chosen.reindex
        (BasedCategory.PseudoPullback
          (toBasedFunctor F) (toBasedFunctor G)).p f₁).obj P ⟶
      (Functor.Chosen.reindex
        (BasedCategory.PseudoPullback
          (toBasedFunctor F) (toBasedFunctor G)).p f₂).obj Q) :
    (functor F G).mapHom f₁ f₂ φ =
      (iso F G f₁).inv.app P ≫
        (BasedCategory.PseudoPullback.Fiber.comparison
          (toBasedFunctor F) (toBasedFunctor G) V).map φ ≫
        (iso F G f₂).hom.app Q := sorry

/-- The selected indexed comparison from actual pseudo-pullback fibers to their
categorical-pullback models is an equivalence on every fiber. This instance bridges the
selected `reindex.chosen.pseudofunctor` façade to the corresponding explicit-cleavage
instance. -/
instance functor.isFiberwiseEquivalence
    (F : X ⟶ S) (G : Y ⟶ S) :
    (functor F G).FiberwiseEquivalence := sorry

namespace fst

/-- Compatibility with selected reindexing of the componentwise identification between the
first projection of the modeled fiber equivalence and the actual first projection. -/
theorem naturality
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U)
    (P : Functor.Fiber
      (BasedCategory.PseudoPullback
        (toBasedFunctor F) (toBasedFunctor G)).p U) :
    (((functor F G).comp
          (FiberedCategoryOver.PseudoPullback.reindex.chosen.fst.indexedFunctor F G)).naturality f).hom.app P ≫
        ((Functor.fiberPseudofunctor X.p).map
          ((𝟭 C).map f).op.toLoc).toFunctor.map
            ((BasedCategory.PseudoPullback.Fiber.comparison.fstIso
              (toBasedFunctor F) (toBasedFunctor G) U).hom.app P) =
      (BasedCategory.PseudoPullback.Fiber.comparison.fstIso
          (toBasedFunctor F) (toBasedFunctor G) V).hom.app
            (((Functor.fiberPseudofunctor
              (BasedCategory.PseudoPullback
                (toBasedFunctor F) (toBasedFunctor G)).p).map
                  f.op.toLoc).toFunctor.obj P) ≫
        ((CartesianBasedFunctor.Indexed.chosen.functor
          (BasedCategory.PseudoPullback.cartesianFst
            (toCartesianBasedFunctor F)
            (toCartesianBasedFunctor G))).naturality f).hom.app P := sorry

/-- The selected first projection of the modeled fiber equivalence agrees, as an indexed
functor, with the actual first projection of the fibred pseudo-pullback. -/
@[stacks 0040 "first projection of the selected indexed pseudo-pullback equivalence"]
noncomputable def iso
    (F : X ⟶ S) (G : Y ⟶ S) :
    (functor F G).comp
      (FiberedCategoryOver.PseudoPullback.reindex.chosen.fst.indexedFunctor F G) ≅
      CartesianBasedFunctor.Indexed.chosen.functor
        (BasedCategory.PseudoPullback.cartesianFst
          (toCartesianBasedFunctor F)
          (toCartesianBasedFunctor G)) :=
  BasedCategory.PseudoPullback.Fiber.reindex.indexed.fst.iso
    (toCartesianBasedFunctor F) (toCartesianBasedFunctor G)
    (FiberedCategoryOver.PseudoPullback.chosenCleavage F G)
    X.chosenCleavage Y.chosenCleavage S.chosenCleavage

/-- Components of the selected indexed first-projection comparison are the canonical
first-projection identifications of the selected fiber equivalences. -/
@[simp]
theorem iso.app
    (F : X ⟶ S) (G : Y ⟶ S) (U : C) :
    Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.isoApp
        (iso F G) U =
      BasedCategory.PseudoPullback.Fiber.comparison.fstIso
        (toBasedFunctor F) (toBasedFunctor G) U := sorry

end fst

namespace snd

/-- Compatibility with selected reindexing of the componentwise identification between the
second projection of the modeled fiber equivalence and the actual second projection. -/
theorem naturality
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U)
    (P : Functor.Fiber
      (BasedCategory.PseudoPullback
        (toBasedFunctor F) (toBasedFunctor G)).p U) :
    (((functor F G).comp
          (FiberedCategoryOver.PseudoPullback.reindex.chosen.snd.indexedFunctor F G)).naturality f).hom.app P ≫
        ((Functor.fiberPseudofunctor Y.p).map
          ((𝟭 C).map f).op.toLoc).toFunctor.map
            ((BasedCategory.PseudoPullback.Fiber.comparison.sndIso
              (toBasedFunctor F) (toBasedFunctor G) U).hom.app P) =
      (BasedCategory.PseudoPullback.Fiber.comparison.sndIso
          (toBasedFunctor F) (toBasedFunctor G) V).hom.app
            (((Functor.fiberPseudofunctor
              (BasedCategory.PseudoPullback
                (toBasedFunctor F) (toBasedFunctor G)).p).map
                  f.op.toLoc).toFunctor.obj P) ≫
        ((CartesianBasedFunctor.Indexed.chosen.functor
          (BasedCategory.PseudoPullback.cartesianSnd
            (toCartesianBasedFunctor F)
            (toCartesianBasedFunctor G))).naturality f).hom.app P := sorry

/-- The selected second projection of the modeled fiber equivalence agrees, as an indexed
functor, with the actual second projection of the fibred pseudo-pullback. -/
@[stacks 0040 "second projection of the selected indexed pseudo-pullback equivalence"]
noncomputable def iso
    (F : X ⟶ S) (G : Y ⟶ S) :
    (functor F G).comp
      (FiberedCategoryOver.PseudoPullback.reindex.chosen.snd.indexedFunctor F G) ≅
      CartesianBasedFunctor.Indexed.chosen.functor
        (BasedCategory.PseudoPullback.cartesianSnd
          (toCartesianBasedFunctor F)
          (toCartesianBasedFunctor G)) :=
  BasedCategory.PseudoPullback.Fiber.reindex.indexed.snd.iso
    (toCartesianBasedFunctor F) (toCartesianBasedFunctor G)
    (FiberedCategoryOver.PseudoPullback.chosenCleavage F G)
    X.chosenCleavage Y.chosenCleavage S.chosenCleavage

/-- Components of the selected indexed second-projection comparison are the canonical
second-projection identifications of the selected fiber equivalences. -/
@[simp]
theorem iso.app
    (F : X ⟶ S) (G : Y ⟶ S) (U : C) :
    Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.isoApp
        (iso F G) U =
      BasedCategory.PseudoPullback.Fiber.comparison.sndIso
        (toBasedFunctor F) (toBasedFunctor G) U := sorry

end snd

end FiberedCategoryOver.PseudoPullback.reindex.chosen.indexed

end CategoryTheory
