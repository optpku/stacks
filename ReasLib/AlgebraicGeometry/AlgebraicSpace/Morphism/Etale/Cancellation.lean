module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale

/-!
# Cancellation of étale morphisms of algebraic spaces

If a composite morphism of algebraic spaces is étale and the second factor is étale,
then the first factor is étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale

/-- If a composite morphism of algebraic spaces is étale and the second factor is étale,
then the first factor is étale. -/
theorem of_comp {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {Z : AlgebraicSpace S} (g : Y ⟶ Z) [Etale (f ≫ g)] [Etale g] : Etale f := sorry

/-- Étale morphisms of algebraic spaces cancel against an étale postcomposition. -/
instance instHasOfPostcompProperty {S : Scheme.{u}} :
    HasOfPostcompProperty (@Etale S : MorphismProperty (AlgebraicSpace S)) (@Etale S) :=
  sorry

/-- If `g : X ⟶ Z` and `h : Y ⟶ Z` are étale and `f ≫ h = g`, then `f` is étale. -/
theorem of_comp_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (g : X ⟶ Z) (h : Y ⟶ Z)
    (f : X ⟶ Y) [Etale g] [Etale h] (hfg : f ≫ h = g) : Etale f := sorry

end AlgebraicGeometry.AlgebraicSpace.Etale
