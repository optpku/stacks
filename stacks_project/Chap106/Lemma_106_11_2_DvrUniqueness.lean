module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import stacks_project.Chap101.Lemma_101_39_8_Uniqueness

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

/-- A morphism of algebraic stacks satisfies the uniqueness part of the DVR
valuative criterion when, for every valuative 2-commutative square whose ring
is a discrete valuation ring, the category of dotted arrows is either empty or
a setoid with exactly one isomorphism class. -/
@[mk_iff]
class ValuativeCriterion.DVR.Uniqueness {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- Hom-spaces in the dotted-arrow category of a DVR valuative square are
  subsingleton. -/
  isThin :
    ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R →
      Quiver.IsThin (DottedArrow sq.toCone)
  /-- Any two dotted arrows of a DVR valuative square are isomorphic. -/
  uniqueIsoClass :
    ∀ (sq : ValuativeCommSq f), IsDiscreteValuationRing sq.R →
      ∀ (A A' : DottedArrow sq.toCone), Nonempty (A ≅ A')

namespace ValuativeCriterion.DVR.Uniqueness

/-- The identity morphism of an algebraic stack satisfies DVR uniqueness. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    Uniqueness (𝟙 X) :=
  sorry

/-- Uniqueness for all valuation rings implies uniqueness for discrete valuation
rings. -/
instance of_uniqueness {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [ValuativeCriterion.Uniqueness f] : Uniqueness f :=
  sorry

/-- A morphism satisfies DVR uniqueness if and only if every DVR valuative square
has a thin dotted-arrow category with at most one isomorphism class. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Uniqueness f ↔
      (∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R →
          Quiver.IsThin (DottedArrow sq.toCone)) ∧
        ∀ (sq : ValuativeCommSq f), IsDiscreteValuationRing sq.R →
          ∀ (A A' : DottedArrow sq.toCone), Nonempty (A ≅ A') :=
  sorry

/-- The dotted-arrow category of a DVR valuative square is thin. -/
theorem isThin_dottedArrow {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [Uniqueness f]
    (sq : ValuativeCommSq f) (hR : IsDiscreteValuationRing sq.R) :
    Quiver.IsThin (DottedArrow sq.toCone) :=
  sorry

/-- Any two dotted arrows of a DVR valuative square are isomorphic. -/
theorem nonempty_iso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [Uniqueness f]
    (sq : ValuativeCommSq f) (hR : IsDiscreteValuationRing sq.R)
    (A A' : DottedArrow sq.toCone) :
    Nonempty (A ≅ A') :=
  sorry

end ValuativeCriterion.DVR.Uniqueness

end AlgebraicGeometry.AlgebraicStack
