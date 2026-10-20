module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FormalBranches.Multiplicity

import StacksCheckRecall

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped Bicategory

universe u

/- Definition 107.4.1. For an algebraic stack locally of finite type over a
locally Noetherian scheme, formal branches through a finite type field-valued
point are the irreducible components of any marked versal ring, identified
across choices by residue-point-compatible power-series comparisons. -/
@[stacks 0DRA] #check (AlgebraicGeometry.AlgebraicStack.FormalBranches :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicGeometry.AlgebraicStack.IsLocallyOfFiniteType X]
    (x0 : AlgebraicGeometry.AlgebraicStack.FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom],
    Type (u + 1))

#check (AlgebraicGeometry.AlgebraicStack.FormalBranches.spec :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicGeometry.AlgebraicStack.IsLocallyOfFiniteType X]
    (x0 : AlgebraicGeometry.AlgebraicStack.FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom],
    ∀ (ξ : GroupoidsOver.FormalObject X) [GroupoidsOver.FormalObject.IsVersal ξ]
      (mξ : AlgebraicGeometry.AlgebraicStack.StageOneMarking x0 ξ),
      Function.Surjective (AlgebraicGeometry.AlgebraicStack.FormalBranches.mk x0 ξ mξ) ∧
        ∀ Z W, AlgebraicGeometry.AlgebraicStack.FormalBranches.mk x0 ξ mξ Z =
          AlgebraicGeometry.AlgebraicStack.FormalBranches.mk x0 ξ mξ W ↔ Z = W)

