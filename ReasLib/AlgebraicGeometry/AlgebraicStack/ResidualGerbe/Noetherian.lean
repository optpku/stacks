module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe

/-!
# Residual gerbes of locally Noetherian algebraic stacks

Every point of a locally Noetherian algebraic stack has a residual gerbe.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Every point of a locally Noetherian algebraic stack has a residual gerbe. -/
instance instHasResidualGerbe_of_isLocallyNoetherian {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] [IsLocallyNoetherian X] (x : Points X) :
    HasResidualGerbe X x :=
  sorry

namespace IsResidualGerbe

/-- At every point of a locally Noetherian algebraic stack, there is an algebraic
stack with a residual-gerbe morphism to it. -/
@[stacks 0H22]
theorem exists_at {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsLocallyNoetherian X] (x : Points X) :
    ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (ι : Z ⟶ X),
      IsResidualGerbe ι x :=
  ⟨residualGerbe X x, instAlgebraicStack_residualGerbe X x,
    residualGerbeι X x, instIsResidualGerbe_residualGerbeι X x⟩

end IsResidualGerbe

end AlgebraicGeometry.AlgebraicStack
