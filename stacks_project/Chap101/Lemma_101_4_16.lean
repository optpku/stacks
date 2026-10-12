/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Example_100_11_9_ResidualGerbe
public import stacks_project.Chap101.Definition_101_4_2_Separation

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

/-- Lemma 101.4.16 (1): if `X` is DM and `ι : Z ⟶ X` is a residual gerbe of
`X` at `x`, then `Z` is DM. -/
@[stacks 06MZ]
theorem IsDM.of_residualGerbe {S : Scheme.{u}} {X Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] (ι : Z ⟶ X) {x : Points X}
    [IsResidualGerbe ι x] [IsDM X] : IsDM Z :=
  sorry

/-- Lemma 101.4.16 (2): if `X` is quasi-DM and `ι : Z ⟶ X` is a residual gerbe
of `X` at `x`, then `Z` is quasi-DM. -/
@[stacks 06MZ]
theorem IsQuasiDM.of_residualGerbe {S : Scheme.{u}} {X Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] (ι : Z ⟶ X) {x : Points X}
    [IsResidualGerbe ι x] [IsQuasiDM X] : IsQuasiDM Z :=
  sorry

/-- Lemma 101.4.16 (3): if `X` is separated and `ι : Z ⟶ X` is a residual gerbe
of `X` at `x`, then `Z` is separated. -/
@[stacks 06MZ]
theorem IsSeparated.of_residualGerbe {S : Scheme.{u}} {X Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] (ι : Z ⟶ X) {x : Points X}
    [IsResidualGerbe ι x] [IsSeparated X] : IsSeparated Z :=
  sorry

/-- Lemma 101.4.16 (4): if `X` is quasi-separated and `ι : Z ⟶ X` is a residual
gerbe of `X` at `x`, then `Z` is quasi-separated. Absolute quasi-separatedness
is quasi-separatedness over `Spec ℤ` after Construction A, as in
Definition 101.4.2 (8). -/
@[stacks 06MZ]
theorem IsQuasiSeparated.of_residualGerbe {S : Scheme.{u}}
    {X Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Z]
    (ι : Z ⟶ X) {x : Points X} [IsResidualGerbe ι x]
    [IsQuasiSeparatedOver (viewedOver (specULiftZIsTerminal.from S) X)] :
    IsQuasiSeparatedOver (viewedOver (specULiftZIsTerminal.from S) Z) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
