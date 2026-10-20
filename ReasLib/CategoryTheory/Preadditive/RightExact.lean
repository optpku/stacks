/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Additivity of Right Exact Functors

This leaf provides the canonical typeclass bridge from preservation of finite
colimits to additivity.  It removes the need for downstream files to rebuild
binary-biproduct and additive instances locally.
-/

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D]

/-- A functor preserving finite colimits between preadditive categories with
zero objects and binary coproducts is additive. -/
@[stacks 0794]
instance (priority := 90) additive_of_preservesFiniteColimits
    [HasZeroObject C] [HasBinaryCoproducts C] [HasZeroObject D]
    (F : C ⥤ D) [PreservesFiniteColimits F] : F.Additive := sorry

end CategoryTheory.Functor
