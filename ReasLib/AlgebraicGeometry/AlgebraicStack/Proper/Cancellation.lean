module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyClosed.Cancellation

/-!
# Cancellation of properness

Properness of a composite of morphisms of algebraic stacks cancels through a
separated second factor. If a composite is universally closed and its first
factor is surjective, then a separated finite type second factor is proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Proper

/-- If a composite morphism of algebraic stacks is proper and the second factor
is separated, then the first factor is proper. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [Proper (f ≫ g)] [Separated g] : Proper f :=
  sorry

/-- If a composite morphism of algebraic stacks is universally closed and the
first factor is surjective, then a separated finite type second factor is proper. -/
@[stacks 0CQK]
theorem of_comp_surjective {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallyClosed (f ≫ g)] [Surjective f]
    [Separated g] [FiniteType g] : Proper g :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Proper
