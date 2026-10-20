module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.ResidualGerbe
import StacksCheckRecall

/-!
# Separation axioms of residual gerbes

If an algebraic stack has a residual gerbe at a point, then DM, quasi-DM,
separated, and quasi-separated pass from the stack to the residual gerbe.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.4.16 (1): if `X` is DM and `ι : Z ⟶ X` is a residual gerbe of
`X` at `x`, then `Z` is DM. -/
@[stacks 06MZ] #check (AlgebraicGeometry.AlgebraicStack.IsDM.of_residualGerbe :
  ∀ {S : Scheme.{u}} {X Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] (ι : Z ⟶ X) (x : Points X)
    [IsResidualGerbe ι x] [IsDM X], IsDM Z)

/- Lemma 101.4.16 (2): if `X` is quasi-DM and `ι : Z ⟶ X` is a residual gerbe
of `X` at `x`, then `Z` is quasi-DM. -/
@[stacks 06MZ] #check (AlgebraicGeometry.AlgebraicStack.IsQuasiDM.of_residualGerbe :
  ∀ {S : Scheme.{u}} {X Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] (ι : Z ⟶ X) (x : Points X)
    [IsResidualGerbe ι x] [IsQuasiDM X], IsQuasiDM Z)

/- Lemma 101.4.16 (3): if `X` is separated and `ι : Z ⟶ X` is a residual gerbe
of `X` at `x`, then `Z` is separated. -/
@[stacks 06MZ] #check (AlgebraicGeometry.AlgebraicStack.IsSeparated.of_residualGerbe :
  ∀ {S : Scheme.{u}} {X Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] (ι : Z ⟶ X) (x : Points X)
    [IsResidualGerbe ι x] [IsSeparated X], IsSeparated Z)

/- Lemma 101.4.16 (4): if `X` is quasi-separated and `ι : Z ⟶ X` is a residual
gerbe of `X` at `x`, then `Z` is quasi-separated. Absolute quasi-separatedness
is quasi-separatedness over `Spec ℤ` after Construction A, as in
Definition 101.4.2 (8). -/
@[stacks 06MZ] #check (AlgebraicGeometry.AlgebraicStack.IsQuasiSeparated.of_residualGerbe :
  ∀ {S : Scheme.{u}} {X Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] (ι : Z ⟶ X) (x : Points X)
    [IsResidualGerbe ι x] [IsQuasiSeparated X], IsQuasiSeparated Z)

end AlgebraicGeometry.AlgebraicStack
