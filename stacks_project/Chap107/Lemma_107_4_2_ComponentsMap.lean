module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FormalBranches.Components

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped Bicategory

universe u

/-! # The map from formal branches to irreducible components -/

#check (AlgebraicGeometry.AlgebraicStack.FormalBranches.toComponent :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicGeometry.AlgebraicStack.IsLocallyOfFiniteType X]
    (x0 : AlgebraicGeometry.AlgebraicStack.FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom],
    ∀ {τ : TopologicalSpace (AlgebraicGeometry.AlgebraicStack.Points X)},
    AlgebraicGeometry.AlgebraicStack.IsPointsTopology X τ →
      AlgebraicGeometry.AlgebraicStack.FormalBranches x0 →
        @irreducibleComponents (AlgebraicGeometry.AlgebraicStack.Points X) τ)
