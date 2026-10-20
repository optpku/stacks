/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap87.Lemma_87_14_4_Completion
public import stacks_project.Chap88.Definition_88_21_1_Formal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.FiniteType
import StacksCheckRecall

/-!
# Locally of finite type morphisms of completions

If a morphism of algebraic spaces is locally of finite type, then the induced
morphism of formal completions along a closed subset is locally of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 88.23.1: If `f : X' ⟶ X` is locally of finite type, then the induced
morphism `completionAlong.map f T` of completions along a closed subset `T` of
`Points X` is locally of finite type. -/
@[stacks 0AQ9] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyOfFiniteType_completionAlongMap :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
      [AlgebraicSpace.LocallyOfFiniteType f] (T : Closeds (Points X)),
      FormalAlgebraicSpace.LocallyOfFiniteType (completionAlong.map f T))

end AlgebraicGeometry.AlgebraicSpace
