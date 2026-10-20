/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.DescentData.FiberedCategoryOver.Action
public import ReasLib.CategoryTheory.Sites.Descent.IndexedFunctor.DescentData.PullFunctor

/-!
# Family pullback and descent-data actions of fibred-category morphisms

This module provides the comparison between descent-data transport by a fibred-category
morphism and pullback along a map of indexing families.
-/

@[expose] public section

universe t t' uC vC uS₁ vS₁

namespace CategoryTheory

open Functor Opposite
open scoped CategoryTheory.Bicategory

namespace FiberedCategoryOver.Descent

variable {C : Type uC} [Category.{vC} C]
variable {A B : FiberedCategoryOver.{uC, vC, uS₁, vS₁} C}
variable {ι : Type t} {S : C} {X : ι → C} (a : ∀ i, X i ⟶ S)

section PullFunctor

variable {ι' : Type t'} {S' : C} {X' : ι' → C}
variable (a' : ∀ j, X' j ⟶ S')
variable {α : ι' → ι} {p : S' ⟶ S}
variable {p' : ∀ j, X' j ⟶ X (α j)}
variable (w : ∀ j, p' j ≫ a (α j) = a' j ≫ p)

/-- The direct descent-data functor of a fibred-category morphism commutes with pullback to
another indexing family. -/
noncomputable def pullFunctorIso
    (F : A ⟶ B) :
    Pseudofunctor.DescentData.pullFunctor
          (Functor.fiberPseudofunctor A.p) w ⋙
        Descent.functor a' F ≅
      Descent.functor a F ⋙
        Pseudofunctor.DescentData.pullFunctor
          (Functor.fiberPseudofunctor B.p) w :=
  Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.PullFunctor.Comparison.iso
    (Indexed.functor F) a a' w

/-- Components of the direct family-pullback comparison are inverse selected reindexing
comparisons. -/
@[simp]
theorem pullFunctorIso.hom.component
    (F : A ⟶ B)
    (D : (Functor.fiberPseudofunctor A.p).DescentData a) (j : ι') :
    ((pullFunctorIso a a' w F).hom.app D).hom j =
      (Reindex.mapIso F (p' j) (D.obj (α j))).inv := sorry

/-- Total-category readout of a forward direct family-pullback comparison component. -/
@[simp]
theorem pullFunctorIso.hom.component.val
    (F : A ⟶ B)
    (D : (Functor.fiberPseudofunctor A.p).DescentData a) (j : ι') :
    (((pullFunctorIso a a' w F).hom.app D).hom j).1 =
      (Reindex.mapIso F (p' j) (D.obj (α j))).inv.1 := sorry

/-- Inverse components of the direct family-pullback comparison are forward selected
reindexing comparisons. -/
@[simp]
theorem pullFunctorIso.inv.component
    (F : A ⟶ B)
    (D : (Functor.fiberPseudofunctor A.p).DescentData a) (j : ι') :
    ((pullFunctorIso a a' w F).inv.app D).hom j =
      (Reindex.mapIso F (p' j) (D.obj (α j))).hom := sorry

/-- Total-category readout of an inverse direct family-pullback comparison component. -/
@[simp]
theorem pullFunctorIso.inv.component.val
    (F : A ⟶ B)
    (D : (Functor.fiberPseudofunctor A.p).DescentData a) (j : ι') :
    (((pullFunctorIso a a' w F).inv.app D).hom j).1 =
      (Reindex.mapIso F (p' j) (D.obj (α j))).hom.1 := sorry

/-- The direct family-pullback comparison is natural in `2`-morphisms of fibred-category
morphisms. -/
theorem pullFunctorIso.hom.naturality
    {F G : A ⟶ B} (τ : F ⟶ G)
    (D : (Functor.fiberPseudofunctor A.p).DescentData a) :
    (pullFunctorIso a a' w F).hom.app D ≫
        (Pseudofunctor.DescentData.pullFunctor
          (Functor.fiberPseudofunctor B.p) w).map
            ((cell a τ).app D) =
      (cell a' τ).app
          ((Pseudofunctor.DescentData.pullFunctor
            (Functor.fiberPseudofunctor A.p) w).obj D) ≫
        (pullFunctorIso a a' w G).hom.app D := sorry

/-- Inverse form of naturality of the direct family-pullback comparison in a fibred-category
`2`-morphism. -/
theorem pullFunctorIso.inv.naturality
    {F G : A ⟶ B} (τ : F ⟶ G)
    (D : (Functor.fiberPseudofunctor A.p).DescentData a) :
    (Pseudofunctor.DescentData.pullFunctor
          (Functor.fiberPseudofunctor B.p) w).map
            ((cell a τ).app D) ≫
        (pullFunctorIso a a' w G).inv.app D =
      (pullFunctorIso a a' w F).inv.app D ≫
        (cell a' τ).app
          ((Pseudofunctor.DescentData.pullFunctor
            (Functor.fiberPseudofunctor A.p) w).obj D) := sorry

/-- For a fibred-category morphism, the canonical-descent and family-pullback comparisons form
the canonical coherent square.  This direct component formula avoids exposing the underlying
indexed functor in applications. -/
theorem pullFunctorIso.hom.canonical
    (F : A ⟶ B) (x : A.p.Fiber S) :
    (pullFunctorIso a a' w F).hom.app
          (((Functor.fiberPseudofunctor A.p).toDescentData a).obj x) ≫
        (Pseudofunctor.DescentData.pullFunctor
          (Functor.fiberPseudofunctor B.p) w).map
            ((comparisonIso a F).hom.app x) ≫
        (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
          (Functor.fiberPseudofunctor B.p) w).hom.app
            ((fiberFunctor F S).obj x) =
      (Descent.functor a' F).map
          ((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
            (Functor.fiberPseudofunctor A.p) w).hom.app x) ≫
        (comparisonIso a' F).hom.app
          (((Functor.fiberPseudofunctor A.p).map
            p.op.toLoc).toFunctor.obj x) ≫
        ((Functor.fiberPseudofunctor B.p).toDescentData a').map
          (Reindex.mapIso F p x).inv := sorry

/-- Inverse component form of the coherent square relating canonical descent, family pullback,
and the descent-data functor of a fibred-category morphism. -/
theorem pullFunctorIso.inv.canonical
    (F : A ⟶ B) (x : A.p.Fiber S) :
    (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
          (Functor.fiberPseudofunctor B.p) w).inv.app
            ((fiberFunctor F S).obj x) ≫
        (Pseudofunctor.DescentData.pullFunctor
          (Functor.fiberPseudofunctor B.p) w).map
            ((comparisonIso a F).inv.app x) ≫
        (pullFunctorIso a a' w F).inv.app
          (((Functor.fiberPseudofunctor A.p).toDescentData a).obj x) =
      ((Functor.fiberPseudofunctor B.p).toDescentData a').map
          (Reindex.mapIso F p x).hom ≫
        (comparisonIso a' F).inv.app
          (((Functor.fiberPseudofunctor A.p).map
            p.op.toLoc).toFunctor.obj x) ≫
        (Descent.functor a' F).map
          ((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
            (Functor.fiberPseudofunctor A.p) w).inv.app x) := sorry

end PullFunctor

end FiberedCategoryOver.Descent

end CategoryTheory
