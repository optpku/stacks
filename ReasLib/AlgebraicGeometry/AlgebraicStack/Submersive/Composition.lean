module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Submersive

/-!
# Composition of submersive morphisms of algebraic stacks

The composition of a pair of submersive morphisms of algebraic stacks is
submersive, and the composition of a pair of universally submersive morphisms
of algebraic stacks is universally submersive.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Submersive

/-- The composition of a pair of submersive morphisms of algebraic stacks is
submersive. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Submersive f] [Submersive g] :
    Submersive (f ≫ g) :=
  sorry

end Submersive

namespace UniversallySubmersive

/-- The composition of a pair of universally submersive morphisms of algebraic
stacks is universally submersive. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallySubmersive f] [UniversallySubmersive g] :
    UniversallySubmersive (f ≫ g) :=
  sorry

end UniversallySubmersive

end AlgebraicGeometry.AlgebraicStack
