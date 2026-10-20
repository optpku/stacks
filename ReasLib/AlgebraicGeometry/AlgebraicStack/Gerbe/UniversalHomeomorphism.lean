module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism

/-!
# Gerbes are universal homeomorphisms

A morphism of algebraic stacks that makes the source a gerbe over the target
is a universal homeomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace UniversalHomeomorphism

/-- A gerbe morphism of algebraic stacks is a universal homeomorphism. -/
instance of_gerbe {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f] :
    UniversalHomeomorphism f :=
  sorry

end UniversalHomeomorphism

/-- A gerbe morphism of algebraic stacks induces a homeomorphism on underlying
point spaces. -/
theorem pointsIsHomeomorph_of_gerbe {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f] :
    pointsIsHomeomorph f :=
  AlgebraicGeometry.AlgebraicStack.pointsIsHomeomorph_of_universalHomeomorphism f

end AlgebraicGeometry.AlgebraicStack
