module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.AutomorphismGroup.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia.BaseChange
import StacksCheckRecall

/-!
# Base change of stabilizer-preserving morphisms

On a cartesian square of algebraic stacks, inducing an isomorphism of
automorphism groups is stable under base change, both at a point and for
the global inertia comparison.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

open AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.AlgebraicStack.automorphismGroup
open AlgebraicGeometry.AlgebraicStack.Inertia

/- Lemma 101.45.5 (1): pointwise stabilizer preservation is stable under
cartesian base change. -/
@[stacks 0DUB] #check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.IsIsoAt.of_isBilimit :
    ∀ {S : Scheme.{u}} {X Y Y' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y']
    {f : X ⟶ Y} {g : Y' ⟶ Y} (c : PseudoPullbackCone f g)
    [AlgebraicStack c.pt] (hc : c.IsBilimit) (x' : |c.pt|)
    (hx : IsIsoAt f (Points.map c.fst x')),
    IsIsoAt c.snd x')

/- Lemma 101.45.5 (2): equivalence of the canonical inertia comparison is
stable under cartesian base change. -/
@[stacks 0DUB] #check (AlgebraicGeometry.AlgebraicStack.Inertia.comparison_isEquivalence_of_isBilimit :
    ∀ {S : Scheme.{u}}
    {X Y Y' : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Y'] {f : X ⟶ Y} {g : Y' ⟶ Y}
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    (hf : (CategoryTheory.FiberedCategoryOver.Groupoids.toBasedFunctor (comparison f)).IsEquivalence),
    (CategoryTheory.FiberedCategoryOver.Groupoids.toBasedFunctor (comparison c.snd)).IsEquivalence)
