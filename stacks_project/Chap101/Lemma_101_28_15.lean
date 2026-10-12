/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Definition_100_11_8_ResidualGerbe
public import stacks_project.Chap100.Example_100_11_9_ResidualGerbe
public import stacks_project.Chap101.Definition_101_28_1_Gerbe

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

/-- Lemma 101.28.15: Let `X` be an algebraic stack. If `X` is a gerbe then for
every `x ∈ |X|` the residual gerbe of `X` at `x` exists. -/
@[stacks 06RA, instance]
instance instHasResidualGerbe_of_isGerbe {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] [IsGerbe X] (x : Points X) :
    HasResidualGerbe X x :=
  sorry

namespace IsResidualGerbe

/-- If `X` is a gerbe algebraic stack, then there is a residual gerbe of `X` at
every point `x ∈ |X|`. -/
theorem exists_at_of_isGerbe {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsGerbe X] (x : Points X) :
    ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (ι : Z ⟶ X),
      IsResidualGerbe ι x :=
  sorry

end IsResidualGerbe

end AlgebraicGeometry.AlgebraicStack
