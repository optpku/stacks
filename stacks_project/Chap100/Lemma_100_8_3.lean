module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import stacks_project.Chap100.Definition_100_8_1_Mono

/-!
# Composition of monomorphisms of algebraic stacks

The composition of monomorphisms of algebraic stacks is a monomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace Mono

/-- Lemma 100.8.3: compositions of monomorphisms of algebraic stacks are
monomorphisms. -/
@[stacks 04ZY]
instance instIsStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Mono S : MorphismProperty (GroupoidsOver S)) := sorry

/-- The composition of monomorphisms of groupoid fibrations is a
monomorphism. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g] : Mono (f ≫ g) := sorry

end Mono

end AlgebraicGeometry.Groupoids.Hom
