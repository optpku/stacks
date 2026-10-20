module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Descent of étale morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale

/-- In a commutative triangle `f ≫ q = p` of algebraic spaces over `S`,
étaleness descends from `p` to `q` along a surjective étale morphism `f`. -/
theorem of_comp_eq_of_surjective {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    [Surjective f] [Etale f] [Etale p] (hcomm : f ≫ q = p) :
    Etale q := sorry

/-- Étaleness of morphisms of algebraic spaces descends under precomposition by
surjective étale morphisms. -/
instance hasOfPrecompSurjective {S : Scheme.{u}} :
    MorphismProperty.HasOfPrecompProperty
      (@Etale S : MorphismProperty (AlgebraicSpace S))
      ((@Surjective S ⊓ @Etale S) : MorphismProperty (AlgebraicSpace S)) where
  of_precomp {X Y Z} f g hf hfg :=
    @of_comp_eq_of_surjective S X Y Z f (f ≫ g) g hf.1 hf.2 hfg rfl

end AlgebraicGeometry.AlgebraicSpace.Etale
