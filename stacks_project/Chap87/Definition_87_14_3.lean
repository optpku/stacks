/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/- Definition 87.14.3: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `T ⊆ Points X` be a closed subset. The formal algebraic space of Lemma 87.14.2
is called the completion of `X` along `T`, and is `completionAlong X T`. -/
@[stacks 0AMC] #check (AlgebraicGeometry.AlgebraicSpace.completionAlong :
  {S : Scheme.{u}} → (X : AlgebraicSpace S) →
    Closeds (AlgebraicGeometry.AlgebraicSpace.Points X) → (Over S)ᵒᵖ ⥤ Type u)
