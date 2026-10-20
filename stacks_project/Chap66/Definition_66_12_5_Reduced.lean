module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Structure

/-! The reduced induced algebraic space structure on a closed subset. -/

open AlgebraicGeometry TopologicalSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspaceStructure.reduced :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} → (Z : Closeds (AlgebraicSpace.Points X)) →
    AlgebraicSpace.ClosedSubspaceStructure Z)
