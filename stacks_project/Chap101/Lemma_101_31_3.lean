/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Example_100_11_9_ResidualGerbe

/-!
# Existence of residual gerbes of locally Noetherian algebraic stacks

If `X` is a locally Noetherian algebraic stack, then a residual gerbe of `X`
exists at every point of `|X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsResidualGerbe

/-- Lemma 101.31.3: Let `X` be a locally Noetherian algebraic stack. Then the
residual gerbe of `X` at `x` exists for every `x ∈ |X|`. -/
@[stacks 0H22]
theorem exists_at {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsLocallyNoetherian X] (x : Points X) :
    ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (ι : Z ⟶ X),
      IsResidualGerbe ι x :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsResidualGerbe
