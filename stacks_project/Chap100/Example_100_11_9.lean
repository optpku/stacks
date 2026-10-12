/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Example_100_11_9_ResidualGerbe

/-!
# Residual gerbes of schemes and algebraic spaces

The residue-field monomorphism of a scheme is a residual gerbe. For an
algebraic space the residual gerbe at a point always exists, and is the
residual space of Decent Spaces, Section 68.13.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Example 100.11.9 (1): Let `X` be a scheme and let `x ∈ X` be a point. Then
the monomorphism `x ⟶ X` is the residual gerbe of `X` at `x`, identifying `x`
with the scheme `Spec (X.residueField x)`. -/
@[stacks 0H21]
instance isResidualGerbe_residueFieldι {S : Scheme.{u}} {U : Over S}
    (u : U.left) : IsResidualGerbe (residueFieldι u) (residueFieldPoint u) :=
  sorry

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.AlgebraicSpace.IsResidualSpace

/-- Example 100.11.9 (2): If `X` is an algebraic space and `x ∈ |X|`, then the
residual gerbe at `x` (which is called the residual space) always exists. -/
@[stacks 0H21]
theorem exists_residualSpace {S : Scheme.{u}} (X : AlgebraicSpace S)
    (x : Points X) : ∃ (Z : AlgebraicSpace S) (ι : Z ⟶ X), IsResidualSpace ι x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsResidualSpace
