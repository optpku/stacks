/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Symmetric
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoricalPullback

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable (F : A ⥤ C) (G : B ⥤ C)

/- Remark 4.31.5: the functor sending a symmetric quintuple `(A, B, C, a, b)` to
`(A, B, a ≫ b⁻¹)` is an equivalence with the ordinary `2`-fibre-product category. The reusable
comparison is `CategoricalPullback.Symmetric.comparison`. -/
@[stacks 06RL]
#check (CategoricalPullback.Symmetric.equivalence F G :
  (F.prod G) ⊡ (Functor.diag C) ≌ F ⊡ G)

@[stacks 06RL]
#check (CategoryTheory.Limits.CategoricalPullback.Symmetric.comparison.isEquivalence F G :
  (CategoryTheory.Limits.CategoricalPullback.Symmetric.comparison F G).IsEquivalence)
