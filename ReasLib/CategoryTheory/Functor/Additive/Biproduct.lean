/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Additive Functors and Binary Biproduct Comparisons

This module characterizes additivity by either of the canonical comparison
morphisms for binary biproducts.  The target is only required to have binary
biproducts: a zero object in the target is not part of the criterion.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open Limits ZeroObject

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasBinaryBiproducts D]
variable (F : C ⥤ D)

/-- A functor is additive exactly when all coproduct-oriented binary biproduct
comparison morphisms are isomorphisms. -/
theorem additive_iff_biprodComparison'_isIso :
    F.Additive ↔ ∀ X Y : C, IsIso (F.biprodComparison' X Y) := sorry

/-- A functor is additive exactly when all product-oriented binary biproduct
comparison morphisms are isomorphisms. -/
theorem additive_iff_biprodComparison_isIso :
    F.Additive ↔ ∀ X Y : C, IsIso (F.biprodComparison X Y) := sorry

/-- Lemma 12.7.1: additivity and invertibility of either canonical binary
biproduct comparison are equivalent. -/
@[stacks 0DLP]
theorem additive_tfae_biprodComparison_isIso :
    List.TFAE [F.Additive,
      ∀ X Y : C, IsIso (F.biprodComparison' X Y),
      ∀ X Y : C, IsIso (F.biprodComparison X Y)] := sorry

end CategoryTheory.Functor
