module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Cancellation for unramified morphisms

Unramifiedness of a composite morphism of algebraic spaces descends to its left
factor, without a hypothesis on the right factor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Unramified

/-- If a composite morphism of algebraic spaces is unramified, then its first
factor is unramified. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Unramified (f ≫ g)] : Unramified f := sorry

end Unramified

/-- Unramified morphisms of algebraic spaces cancel against arbitrary
postcomposition. -/
instance unramified_hasOfPostcompProperty {S : Scheme.{u}} :
    MorphismProperty.HasOfPostcompProperty
      (@Unramified S : MorphismProperty (AlgebraicSpace S)) ⊤ := sorry

end AlgebraicGeometry.AlgebraicSpace
