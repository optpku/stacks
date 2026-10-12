/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Cancellation for separation properties

Separatedness, local separatedness, and quasi-separatedness of a composite
morphism of algebraic spaces descend to its first factor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Separated

/-- If a composite morphism of algebraic spaces is separated, then so is the first factor. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Separated (f ≫ g)] : Separated f := sorry

end Separated

namespace LocallySeparated

/-- If a composite morphism of algebraic spaces is locally separated, then so is the first factor. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallySeparated (f ≫ g)] : LocallySeparated f := sorry

end LocallySeparated

namespace QuasiSeparated

/-- If a composite morphism of algebraic spaces is quasi-separated, then so is the first factor. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiSeparated (f ≫ g)] : QuasiSeparated f := sorry

end QuasiSeparated

/-- Separated morphisms of algebraic spaces cancel against an arbitrary postcomposition. -/
instance separated_hasOfPostcompProperty {S : Scheme.{u}} :
    MorphismProperty.HasOfPostcompProperty
      (@Separated S : MorphismProperty (AlgebraicSpace S)) ⊤ := sorry

/-- Locally separated morphisms of algebraic spaces cancel against an arbitrary postcomposition. -/
instance locallySeparated_hasOfPostcompProperty {S : Scheme.{u}} :
    MorphismProperty.HasOfPostcompProperty
      (@LocallySeparated S : MorphismProperty (AlgebraicSpace S)) ⊤ := sorry

/-- Quasi-separated morphisms of algebraic spaces cancel against an arbitrary postcomposition. -/
instance quasiSeparated_hasOfPostcompProperty {S : Scheme.{u}} :
    MorphismProperty.HasOfPostcompProperty
      (@QuasiSeparated S : MorphismProperty (AlgebraicSpace S)) ⊤ := sorry

end AlgebraicGeometry.AlgebraicSpace
