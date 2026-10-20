/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe.Existence
import StacksCheckRecall

/-!
# Existence of residual gerbes under quasi-compact inertia

If `X` is an algebraic stack whose inertia morphism `I_X ⟶ X` is
quasi-compact, then a residual gerbe of `X` exists at every point of `|X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.31.1: Let `X` be an algebraic stack such that `I_X ⟶ X` is
quasi-compact. Then the residual gerbe of `X` at `x` exists for every
`x ∈ |X|`. -/
@[stacks 06RD] #check
  (AlgebraicGeometry.AlgebraicStack.instHasResidualGerbe_of_quasiCompactInertia :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] (x : Points X),
      HasResidualGerbe X x)

#check
  (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.exists_at_of_quasiCompactInertia :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] (x : Points X),
      ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (ι : Z ⟶ X),
        IsResidualGerbe ι x)

end AlgebraicGeometry.AlgebraicStack
