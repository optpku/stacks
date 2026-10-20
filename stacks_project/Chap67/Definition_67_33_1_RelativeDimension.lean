module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 67.33.1: the pointwise relative dimension
predicate for morphisms of algebraic spaces, including infinite values. -/
#check (AlgebraicGeometry.AlgebraicSpace.RelativeDimensionEqAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
    (X ⟶ Y) → ℕ∞ → AlgebraicSpace.Points X → Prop)
