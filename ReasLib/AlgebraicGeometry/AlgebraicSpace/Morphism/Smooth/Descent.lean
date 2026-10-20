module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Descent of smooth morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Smooth

/-- In a commutative triangle `f ≫ q = p` of algebraic spaces over `S`,
smoothness descends from `p` to `q` along a surjective smooth morphism `f`. -/
theorem of_comp_eq_of_surjective {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    [Surjective f] [Smooth f] [Smooth p] (hcomm : f ≫ q = p) :
    Smooth q := sorry

/-- Smoothness of morphisms of algebraic spaces descends under precomposition by
surjective smooth morphisms. -/
instance hasOfPrecompSurjective {S : Scheme.{u}} :
    MorphismProperty.HasOfPrecompProperty
      (@Smooth S : MorphismProperty (AlgebraicSpace S))
      ((@Surjective S ⊓ @Smooth S) : MorphismProperty (AlgebraicSpace S)) where
  of_precomp {X Y Z} f g hf hfg :=
    @of_comp_eq_of_surjective S X Y Z f (f ≫ g) g hf.1 hf.2 hfg rfl

end AlgebraicGeometry.AlgebraicSpace.Smooth
