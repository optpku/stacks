module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.DVR

/-!
# DVR uniqueness for morphisms of algebraic stacks

A morphism of algebraic stacks satisfies uniqueness on discrete valuation rings
when every DVR valuative 2-square has a thin dotted-arrow category with at most
one isomorphism class.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.DVR.Uniqueness :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y], (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.DVR.Uniqueness.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    ValuativeCriterion.DVR.Uniqueness (𝟙 X))

#check (AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.DVR.Uniqueness.of_uniqueness :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [ValuativeCriterion.Uniqueness f], ValuativeCriterion.DVR.Uniqueness f)

#check (AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.DVR.Uniqueness.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    ValuativeCriterion.DVR.Uniqueness f ↔
      (∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R →
          Quiver.IsThin (DottedArrow sq.toCone)) ∧
        ∀ (sq : ValuativeCommSq f), IsDiscreteValuationRing sq.R →
          ∀ (A A' : DottedArrow sq.toCone), Nonempty (A ≅ A'))

#check (AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.DVR.Uniqueness.isThin_dottedArrow :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    [ValuativeCriterion.DVR.Uniqueness f]
    (sq : ValuativeCommSq f) (hR : IsDiscreteValuationRing sq.R),
    Quiver.IsThin (DottedArrow sq.toCone))

#check (AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.DVR.Uniqueness.nonempty_iso :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    [ValuativeCriterion.DVR.Uniqueness f]
    (sq : ValuativeCommSq f) (hR : IsDiscreteValuationRing sq.R)
    (A A' : DottedArrow sq.toCone), Nonempty (A ≅ A'))

end AlgebraicGeometry.AlgebraicStack
