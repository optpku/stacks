/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.InverseSystem.TailDecomposition
import StacksCheckRecall

/-!
# Lemma 12.31.5

Compatibility entry point for tail decompositions of essentially constant sequential inverse
systems. The reusable API is owned by ReasLib.CategoryTheory.InverseSystem.TailDecomposition.
-/

@[expose] public section

open CategoryTheory

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [IsIdempotentComplete A]
variable (F : SequentialInverseSystem A)

namespace CategoryTheory

/- Lemma 12.31.5: an essentially constant sequential inverse system admits an explicit limit
tail decomposition with eventually zero complementary transitions. -/
@[stacks 070C]
#check (SequentialInverseSystem.TailDecomposition.HasLimit.iff_essentiallyConstant F :
  IsCofiltered.IsEssentiallyConstant F ↔
    SequentialInverseSystem.TailDecomposition.HasLimit F)

#check (SequentialInverseSystem.TailDecomposition.HasLimit F : Prop)
#check (SequentialInverseSystem.TailDecomposition.HasLimit.iff_split F :
  EssentiallyConstant.Split.Eventual.HasLimit F ↔
    SequentialInverseSystem.TailDecomposition.HasLimit F)

end CategoryTheory
