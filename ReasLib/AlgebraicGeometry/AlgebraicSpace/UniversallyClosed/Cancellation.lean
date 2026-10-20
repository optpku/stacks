module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Cancellation of universal closedness

If a composite morphism of algebraic spaces is universally closed and the second
factor is separated, then the first factor is universally closed.
If instead the first factor is surjective, then the second factor is universally
closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace UniversallyClosed

/-- If a composite morphism of algebraic spaces is universally closed and the
second factor is separated, then the first factor is universally closed. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [UniversallyClosed (f ≫ g)] [Separated g] : UniversallyClosed f := sorry

/-- If a composite morphism of algebraic spaces is universally closed and the
first factor is surjective, then the second factor is universally closed. -/
@[stacks 08AJ]
theorem of_comp_surjective {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ B) [UniversallyClosed (f ≫ g)] [Surjective f] :
    UniversallyClosed g :=
  sorry

end UniversallyClosed

/-- Universally closed morphisms of algebraic spaces cancel against a separated
postcomposition. -/
instance universallyClosed_hasOfPostcompProperty {S : Scheme.{u}} :
    MorphismProperty.HasOfPostcompProperty
      (@UniversallyClosed S : MorphismProperty (AlgebraicSpace S))
      (@Separated S) where
  of_postcomp {X Y Z} f g hg hfg :=
    @UniversallyClosed.of_comp S X Y Z f g hfg hg

/-- Universally closed morphisms of algebraic spaces cancel against a surjective
precomposition. -/
instance universallyClosed_hasOfPrecompProperty {S : Scheme.{u}} :
    MorphismProperty.HasOfPrecompProperty
      (@UniversallyClosed S : MorphismProperty (AlgebraicSpace S))
      (@Surjective S) where
  of_precomp {X Y Z} f g hf hfg :=
    @UniversallyClosed.of_comp_surjective S X Y Z f g hfg hf

end AlgebraicGeometry.AlgebraicSpace
