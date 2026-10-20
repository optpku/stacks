/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe.QuasiDM
import StacksCheckRecall

/-!
# Existence of residual gerbes of quasi-DM algebraic stacks

If `X` is a quasi-DM algebraic stack, then a residual gerbe of `X` exists at
every point of `|X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

/- Lemma 101.31.2: Let `X` be a quasi-DM algebraic stack. Then the residual
gerbe of `X` at `x` exists for every `x ∈ |X|`. -/
@[stacks 06UI] #check
  (AlgebraicGeometry.AlgebraicStack.instHasResidualGerbe_of_isQuasiDM :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      [AlgebraicStack.IsQuasiDM X] (x : AlgebraicStack.Points X),
      AlgebraicStack.HasResidualGerbe X x)

#check (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.exists_at_of_isQuasiDM :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [AlgebraicStack.IsQuasiDM X] (x : AlgebraicStack.Points X),
    ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (ι : Z ⟶ X),
      AlgebraicStack.IsResidualGerbe ι x)
