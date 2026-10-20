module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Transfer
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Monomorphism

/-!
# Separation axioms of residual gerbes

DM, quasi-DM, separatedness, and quasi-separatedness pass from an algebraic
stack to any existing residual gerbe.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A residual gerbe of a DM algebraic stack is DM. -/
theorem IsDM.of_residualGerbe {S : Scheme.{u}} {X Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] (ι : Z ⟶ X) (x : Points X)
    [IsResidualGerbe ι x] [IsDM X] : IsDM Z :=
  sorry

/-- A residual gerbe of a quasi-DM algebraic stack is quasi-DM. -/
theorem IsQuasiDM.of_residualGerbe {S : Scheme.{u}} {X Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] (ι : Z ⟶ X) (x : Points X)
    [IsResidualGerbe ι x] [IsQuasiDM X] : IsQuasiDM Z :=
  sorry

/-- A residual gerbe of a separated algebraic stack is separated. -/
theorem IsSeparated.of_residualGerbe {S : Scheme.{u}} {X Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] (ι : Z ⟶ X) (x : Points X)
    [IsResidualGerbe ι x] [IsSeparated X] : IsSeparated Z :=
  sorry

/-- A residual gerbe of an absolutely quasi-separated algebraic stack is
absolutely quasi-separated. -/
theorem IsQuasiSeparated.of_residualGerbe {S : Scheme.{u}}
    {X Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Z]
    (ι : Z ⟶ X) (x : Points X) [IsResidualGerbe ι x]
    [IsQuasiSeparated X] : IsQuasiSeparated Z :=
  sorry

end AlgebraicGeometry.AlgebraicStack
