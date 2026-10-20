module

public import ReasLib.AlgebraicGeometry.FreeDimensionalAlgebra

universe u

/- 97.13.0.2: The presheaf of distinguished finite free algebra groupoids on schemes. -/
#check
  (@AlgebraicGeometry.FA : ∀ (d : ℕ) [NeZero d],
    CategoryTheory.Functor (AlgebraicGeometry.Scheme.{u})ᵒᵖ CategoryTheory.Grpd.{u, u})
