module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.Cancellation

/-!
# Cancellation laws for properness

If a composite morphism of algebraic spaces is proper and the second factor is
separated, then the first factor is proper.
A separated finite type second factor is proper if the composite is universally
closed and the first factor is surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Proper

/-- If a composite morphism of algebraic spaces is proper and the second factor
is separated, then the first factor is proper. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Proper (f ≫ g)] [Separated g] : Proper f := sorry

/-- A separated finite type morphism of algebraic spaces is proper if its
precomposition with a surjective morphism is universally closed. -/
@[stacks 08AJ]
theorem of_comp_surjective {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ B) [UniversallyClosed (f ≫ g)] [Surjective f]
    [Separated g] [FiniteType g] : Proper g :=
  sorry

end Proper

/-- Proper morphisms of algebraic spaces cancel against a separated
postcomposition. -/
instance proper_hasOfPostcompProperty {S : Scheme.{u}} :
    MorphismProperty.HasOfPostcompProperty
      (@Proper S : MorphismProperty (AlgebraicSpace S))
      (@Separated S) where
  of_postcomp {X Y Z} f g hg hfg :=
    @Proper.of_comp S X Y Z f g hfg hg

end AlgebraicGeometry.AlgebraicSpace
