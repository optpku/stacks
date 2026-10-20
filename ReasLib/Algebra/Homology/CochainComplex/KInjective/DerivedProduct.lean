/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Limit
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Products

@[expose] public section

/-!
# Derived Products of K-Injective Complexes

This leaf owns the K-injective specialization of derived-product preservation.
The general representative-model fan and exact-product APIs remain in
`ReasLib.CategoryTheory.DerivedCategory.Limit.Products`, so consumers only
import this file when their product model specifically uses K-injectivity.
-/

open CategoryTheory CategoryTheory.Limits

universe wD v u uJ

namespace CategoryTheory.DerivedCategory.Product

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{wD} C]

/-- Localization to the derived category preserves a product of K-injective cochain
complexes. -/
@[stacks 0BK6, stacks 07D9 "termwise K-injective product model"]
instance q_preservesProduct_of_kInjective {J : Type uJ}
    (I : J → CochainComplex C ℤ) [HasProduct I] [∀ j, (I j).IsKInjective] :
    PreservesLimit (Discrete.functor I) DerivedCategory.Q := sorry

end CategoryTheory.DerivedCategory.Product
