/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.IndexedFunctor.FiberedCategoryOver.Action

/-!
# Fiberwise equivalence properties of direct indexed actions

This module transfers full faithfulness and equivalence hypotheses on the
fiber functors of a fibred-category morphism to its direct indexed action.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

open Functor Opposite
open scoped CategoryTheory.Bicategory

namespace FiberedCategoryOver

variable {C : Type uC} [Category.{vC} C]
variable {X : FiberedCategoryOver.{uC, vC, uS, vS} C}
variable {Y : FiberedCategoryOver.{uC, vC, uS, vS} C}

/-- Fiberwise full faithfulness of a fibred-category morphism supplies the corresponding
property of its selected indexed functor. -/
theorem Indexed.functor.fiberwiseFullyFaithful
    (F : X ⟶ Y)
    (h : ∀ U : C, Nonempty (fiberFunctor F U).FullyFaithful) :
    (Indexed.functor F).FiberwiseFullyFaithful := sorry

/-- Equivalences on all fibers make the direct indexed fiber action a fiberwise
equivalence. -/
theorem Indexed.functor.fiberwiseEquivalence
    (F : X ⟶ Y)
    (h : ∀ U : C, (fiberFunctor F U).IsEquivalence) :
    (Indexed.functor F).FiberwiseEquivalence := sorry

/-- Boundary form: a fibred-category morphism whose underlying based functor is an equivalence
over the base induces a fiberwise equivalence of selected fiber pseudofunctors. -/
instance Indexed.functor.fiberwiseEquivalence.ofBasedEquivalence
    (F : X ⟶ Y) [(toBasedFunctor F).IsEquivalence] :
    (Indexed.functor F).FiberwiseEquivalence := sorry

/-- The forward morphism of a bicategorical equivalence of fibred categories induces a
fiberwise equivalence of selected fiber pseudofunctors. -/
instance Indexed.functor.fiberwiseEquivalence.ofEquivalence
    (e : X ≌ Y) :
    (Indexed.functor e.hom).FiberwiseEquivalence := sorry

end FiberedCategoryOver

end CategoryTheory
