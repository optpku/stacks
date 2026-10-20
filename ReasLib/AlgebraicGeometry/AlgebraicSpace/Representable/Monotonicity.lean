module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Property

/-!
# Monotonicity of transferred morphism properties of algebraic spaces

Pointwise implication between morphism properties of algebraic spaces is
preserved by transfer to morphisms of presheaves representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace relativeAlgebraicSpaces

/-- Pointwise implication between morphism properties of algebraic spaces over
`S` induces pointwise implication between their transferred properties on
morphisms of presheaves on `(Over S)ᵒᵖ`. -/
theorem monotone {S : Scheme.{u}}
    {P P' : MorphismProperty (AlgebraicSpace S)} (h : P ≤ P') :
    relativeAlgebraicSpaces P ≤ relativeAlgebraicSpaces P' :=
  sorry

end relativeAlgebraicSpaces

end AlgebraicGeometry.AlgebraicSpace
