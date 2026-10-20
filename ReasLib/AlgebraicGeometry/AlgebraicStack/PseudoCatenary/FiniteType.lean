module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType.Scheme
public import ReasLib.AlgebraicGeometry.AlgebraicStack.PseudoCatenary

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The source scheme of a smooth morphism to an algebraic stack locally of finite
type over a universally catenary scheme is universally catenary. -/
theorem universallyCatenary_of_smooth {S : Scheme.{u}}
    [AlgebraicGeometry.UniversallyCatenary S] {X : GroupoidsOver S}
    [AlgebraicStack X] [LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    {U : Over S} (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p] :
    AlgebraicGeometry.UniversallyCatenary U.left :=
  sorry

/-- An algebraic stack locally of finite type over a universally catenary scheme is
pseudo-catenary. -/
instance instIsPseudoCatenary_of_locallyOfFiniteType {S : Scheme.{u}}
    [AlgebraicGeometry.UniversallyCatenary S] (X : GroupoidsOver S)
    [AlgebraicStack X]
    [LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)] :
    IsPseudoCatenary X :=
  sorry

/-- The source of a locally of finite type morphism to a pseudo-catenary algebraic
stack is pseudo-catenary. -/
@[stacks 0DRW]
theorem IsPseudoCatenary.of_locallyOfFiniteType {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [IsPseudoCatenary X] (f : Y ⟶ X) [LocallyOfFiniteType f] :
    IsPseudoCatenary Y :=
  sorry

end AlgebraicGeometry.AlgebraicStack
