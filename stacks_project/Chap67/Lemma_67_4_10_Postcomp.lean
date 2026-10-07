module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Cancellation of separation axioms along postcomposition

If a composite morphism of algebraic spaces is separated, locally separated, or
quasi-separated, then so is the first factor. No hypothesis is imposed on the
second factor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Separated

/-- If a composite morphism of algebraic spaces is separated, then so is the first
factor. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Separated (f ≫ g)] : Separated f := sorry

end Separated

namespace LocallySeparated

/-- If a composite morphism of algebraic spaces is locally separated, then so is the
first factor. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallySeparated (f ≫ g)] : LocallySeparated f := sorry

end LocallySeparated

namespace QuasiSeparated

/-- If a composite morphism of algebraic spaces is quasi-separated, then so is the
first factor. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiSeparated (f ≫ g)] : QuasiSeparated f := sorry

end QuasiSeparated

/-- Separated morphisms of algebraic spaces cancel against an arbitrary postcomposition. -/
instance separated_hasOfPostcompProperty {S : Scheme.{u}} :
    MorphismProperty.HasOfPostcompProperty
      (@Separated S : MorphismProperty (AlgebraicSpace S)) ⊤ := sorry

/-- Locally separated morphisms of algebraic spaces cancel against an arbitrary
postcomposition. -/
instance locallySeparated_hasOfPostcompProperty {S : Scheme.{u}} :
    MorphismProperty.HasOfPostcompProperty
      (@LocallySeparated S : MorphismProperty (AlgebraicSpace S)) ⊤ := sorry

/-- Quasi-separated morphisms of algebraic spaces cancel against an arbitrary
postcomposition. -/
instance quasiSeparated_hasOfPostcompProperty {S : Scheme.{u}} :
    MorphismProperty.HasOfPostcompProperty
      (@QuasiSeparated S : MorphismProperty (AlgebraicSpace S)) ⊤ := sorry

end AlgebraicGeometry.AlgebraicSpace
