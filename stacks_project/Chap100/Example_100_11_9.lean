module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe
import StacksCheckRecall

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

/- Example 100.11.9 (1): The canonical residue-field inclusion of a scheme
point is its residual gerbe. -/
@[stacks 0H21] #check
  (AlgebraicGeometry.AlgebraicStack.isResidualGerbe_residueFieldι :
    ∀ {S : Scheme.{u}} {U : Over S} (u : U.left),
      AlgebraicGeometry.AlgebraicStack.IsResidualGerbe
        (AlgebraicGeometry.AlgebraicStack.residueFieldι u)
        (AlgebraicGeometry.AlgebraicStack.residueFieldPoint u))

/- Example 100.11.9 (2): Every point of an algebraic space has a residual space. -/
@[stacks 0H21] #check
  (AlgebraicGeometry.AlgebraicSpace.IsResidualSpace.exists_at :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      (x : AlgebraicGeometry.AlgebraicSpace.Points X),
      ∃ (Z : AlgebraicSpace S) (ι : Z ⟶ X),
        AlgebraicGeometry.AlgebraicSpace.IsResidualSpace ι x)
