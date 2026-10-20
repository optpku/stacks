module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.OpenImmersion

open CategoryTheory AlgebraicGeometry

universe u

@[expose] public section

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

/-- An open immersion of lifted groupoid fibrations is representable by algebraic
spaces, with every representing morphism an open immersion. -/
abbrev OpenImmersion {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.AlgebraicSpace.CohStack.OpenImmersion f

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

/- Open immersions in the lifted bicategory of groupoid fibrations over `Over S`. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.OpenImmersion :
  ∀ {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)},
    (X ⟶ Y) → Prop)
