module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Perfect

/-!
# Composition of perfect morphisms of algebraic spaces

Perfect morphisms of algebraic spaces are stable under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry
namespace AlgebraicSpace
namespace Perfect

/-- A composition of perfect morphisms of algebraic spaces is perfect. -/
@[stacks 06C1]
theorem comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Perfect f] [Perfect g] :
    Perfect (f ≫ g) := sorry

/-- The composition of perfect morphisms of algebraic spaces is canonically perfect. -/
instance instComp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Perfect f] [Perfect g] :
    Perfect (f ≫ g) := Perfect.comp f g

/-- Perfect morphisms of algebraic spaces are stable under composition. -/
instance instIsStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Perfect S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end Perfect
end AlgebraicSpace
end AlgebraicGeometry
