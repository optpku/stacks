module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion

/-!
# DVR uniqueness for morphisms of algebraic spaces

A morphism of algebraic spaces satisfies the uniqueness part of the DVR
valuative criterion when every valuative square whose ring is a discrete
valuation ring has at most one lift.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces satisfies the uniqueness part of the DVR
valuative criterion if every valuative commutative square whose ring is a
discrete valuation ring has at most one lift. -/
@[mk_iff]
class ValuativeCriterion.DVR.Uniqueness {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- Every DVR valuative square has at most one dotted lift. -/
  subsingleton_liftStruct :
    ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R → Subsingleton sq.commSq.LiftStruct

namespace ValuativeCriterion.DVR.Uniqueness

/-- The identity morphism of an algebraic space satisfies DVR uniqueness. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Uniqueness (𝟙 X) := sorry

/-- Uniqueness for all valuation rings implies uniqueness for discrete valuation rings. -/
instance of_uniqueness {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [ValuativeCriterion.Uniqueness f] : Uniqueness f := sorry

/-- A morphism satisfies DVR uniqueness if and only if every DVR valuative square
has at most one lift. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Uniqueness f ↔
      ∀ sq : ValuativeCommSq f,
        IsDiscreteValuationRing sq.R → Subsingleton sq.commSq.LiftStruct :=
  sorry

end ValuativeCriterion.DVR.Uniqueness

end AlgebraicGeometry.AlgebraicSpace
