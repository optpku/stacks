module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe.Noetherian
import StacksCheckRecall

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

/- Lemma 101.31.3: Let `X` be a locally Noetherian algebraic stack. Then the
residual gerbe of `X` at `x` exists for every `x ∈ |X|`. -/
@[stacks 0H22] #check
  (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.exists_at :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      [AlgebraicStack.IsLocallyNoetherian X] (x : AlgebraicStack.Points X),
    ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (ι : Z ⟶ X),
      AlgebraicStack.IsResidualGerbe ι x)
