module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.PseudoCatenary.FiniteType
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Example 107.5.15: if an algebraic stack `X` is locally of finite type over a
universally catenary locally Noetherian scheme `S`, and `U ⟶ X` is a smooth
surjective morphism from a scheme, then the composite `U ⟶ S` is locally of
finite type, hence `U` is universally catenary, and therefore `X` is
pseudo-catenary. -/
@[stacks 0DRV] #check
  (AlgebraicGeometry.AlgebraicStack.instIsPseudoCatenary_of_locallyOfFiniteType :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (X : GroupoidsOver S)
      [AlgebraicStack X]
      [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)],
      AlgebraicStack.IsPseudoCatenary X)

#check
  (AlgebraicGeometry.AlgebraicStack.locallyOfFiniteType_hom_of_smooth :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
      {U : Over S} (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p],
      LocallyOfFiniteType U.hom)

#check
  (AlgebraicGeometry.AlgebraicStack.universallyCatenary_of_smooth :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {X : GroupoidsOver S}
      [AlgebraicStack X]
      [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
      {U : Over S} (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p],
      UniversallyCatenary U.left)
