module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.ClosedImmersion

open CategoryTheory AlgebraicGeometry

universe u

/- Closed immersions of lifted groupoid fibrations are represented by closed
immersions of algebraic spaces. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.ClosedImmersion :
  ∀ {S : Scheme.{u}}
    {X Y : CategoryTheory.FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1}
      (Over S)},
    (X ⟶ Y) → Prop)
