/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe.ResidualGerbe
import StacksCheckRecall

/-!
# Existence of residual gerbes of gerbe algebraic stacks

If `X` is a gerbe algebraic stack, then a residual gerbe of `X` exists at every
point of `|X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.28.15: Let `X` be an algebraic stack. If `X` is a gerbe then for
every `x ∈ |X|` the residual gerbe of `X` at `x` exists. -/
@[stacks 06RA] #check
  (AlgebraicGeometry.AlgebraicStack.instHasResidualGerbe_of_isGerbe :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] [IsGerbe X]
      (x : Points X), HasResidualGerbe X x)

#check (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.exists_at_of_isGerbe :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] [IsGerbe X]
    (x : Points X), ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (ι : Z ⟶ X),
      IsResidualGerbe ι x)

end AlgebraicGeometry.AlgebraicStack
