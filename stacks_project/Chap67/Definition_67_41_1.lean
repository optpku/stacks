module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion
import StacksCheckRecall

@[expose]
public section

open CategoryTheory

universe u

/- Definition 67.41.1 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
satisfies the uniqueness part of the valuative criterion if every solid valuative square
with `A` a valuation ring and `K` its field of fractions has at most one dotted lift
`Spec(A) ⟶ X`. -/
@[stacks 03IX] #check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Uniqueness :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → Prop)

/- Definition 67.41.1 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
satisfies the existence part of the valuative criterion if every solid valuative square
admits a field extension `K'/K`, a valuation ring `A' ⊂ K'` dominating `A`, and a morphism
`Spec(A') ⟶ X` making the extended diagram commute. -/
@[stacks 03IX] #check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Existence :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → Prop)

/- Definition 67.41.1 (3): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
satisfies the valuative criterion if it satisfies both the uniqueness and existence parts. -/
@[stacks 03IX] #check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → Prop)
