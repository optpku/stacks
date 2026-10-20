/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Countable
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe w v u

/- Lemma 57.17.2 -/
@[stacks 0G0V]
#check
  (CategoryTheory.countableCategory_boundedDerived :
    ∀ (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
      [CountableCategory (Skeleton A)],
      CountableCategory (Skeleton (DerivedCategory.Bounded A)))
