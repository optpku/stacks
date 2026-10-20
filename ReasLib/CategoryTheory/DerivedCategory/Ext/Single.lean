/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ordinary Ext and the derived single-object functor

Mathlib's `CategoryTheory.Abelian.Ext` owns ordinary Ext and its additive equivalence with
shifted morphisms between degree-zero single objects.  This leaf adds the two composition
formulas needed by downstream derived-category calculations without aliasing that canonical API.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Preadditive
open scoped DerivedExt

universe w' w v u

noncomputable section

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasExt.{w} C] [HasDerivedCategory.{w'} C]

/-- The ordinary Ext equivalence intertwines postcomposition by a degree-zero morphism with
postcomposition by its image under the derived single-object functor. -/
@[simp, stacks 06XQ "ordinary Ext postcomposition in the derived category"]
theorem homAddEquiv_comp_mk₀ {X Y Y' : C} {n : ℕ} (e : Ext X Y n) (f : Y ⟶ Y') :
    homAddEquiv (e.comp (mk₀ f) (add_zero n)) =
      homAddEquiv e ≫ ((DerivedCategory.singleFunctor C 0).map f)⟦(n : ℤ)⟧' := sorry

/-- The ordinary Ext equivalence intertwines precomposition by a degree-zero morphism with
precomposition by its image under the derived single-object functor. -/
@[simp, stacks 06XQ "ordinary Ext precomposition in the derived category"]
theorem homAddEquiv_mk₀_comp {X X' Y : C} {n : ℕ} (f : X' ⟶ X) (e : Ext X Y n) :
    homAddEquiv ((mk₀ f).comp e (zero_add n)) =
      (DerivedCategory.singleFunctor C 0).map f ≫ homAddEquiv e := sorry

end CategoryTheory.Abelian.Ext

end
