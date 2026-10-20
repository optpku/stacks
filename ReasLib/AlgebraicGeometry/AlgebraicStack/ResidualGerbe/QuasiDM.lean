/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Object

/-!
# Residual gerbes of quasi-DM algebraic stacks

Every point of a quasi-DM algebraic stack has a residual gerbe.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Every point of a quasi-DM algebraic stack has a residual gerbe. -/
@[stacks 06UI, instance]
instance instHasResidualGerbe_of_isQuasiDM {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] [IsQuasiDM X] (x : Points X) :
    HasResidualGerbe X x :=
  sorry

namespace IsResidualGerbe

/-- At every point of a quasi-DM algebraic stack, there is an algebraic stack
with a residual-gerbe morphism to it. -/
theorem exists_at_of_isQuasiDM {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsQuasiDM X] (x : Points X) :
    ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (ι : Z ⟶ X),
      IsResidualGerbe ι x :=
  sorry

end IsResidualGerbe

end AlgebraicGeometry.AlgebraicStack
