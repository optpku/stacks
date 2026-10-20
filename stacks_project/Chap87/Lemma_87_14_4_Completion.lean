module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong

/-! Completion of an algebraic space along a closed subset. -/

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong :
  {S : Scheme.{u}} → (X : AlgebraicSpace S) →
    Closeds (AlgebraicGeometry.AlgebraicSpace.Points X) → (Over S)ᵒᵖ ⥤ Type u)
