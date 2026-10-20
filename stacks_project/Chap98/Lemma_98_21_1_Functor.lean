/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Lifts

/-!
# Functoriality of outgoing lifts over an arbitrary base

The canonical functor on outgoing lift categories is defined for a morphism of
categories fibred in groupoids, a commutative base square and a connecting fibre arrow.
-/

open CategoryTheory CategoryTheory.Functor
open FiberedCategoryOver.Groupoids (fiberFunctor)
open scoped Bicategory

universe u v

#check (CategoryTheory.FiberedCategoryOver.Groupoids.liftFunctor :
  ∀
    {C : Type u} [Category.{v} C] {X Y : FiberedCategoryOver.Groupoids C} (F : X ⟶ Y) {U U' V V' : C}
    (i : U ⟶ U') (j : V ⟶ V') (r : V ⟶ U) (r' : V' ⟶ U') (sq : CommSq j r r' i)
    {x : X.p.Fiber U} {y : Y.p.Fiber V}
    (φ : Chosen.reindexObj Y.p r ((fiberFunctor F U).obj x) ⟶ y),
    UnderLift X.p i x ⥤ UnderLift Y.p j y)
