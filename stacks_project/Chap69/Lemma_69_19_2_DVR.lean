module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion
public import stacks_project.Chap69.Lemma_69_19_1_DVR

/-!
# DVR valuative criterion for morphisms of algebraic spaces

A morphism of algebraic spaces satisfies the existence part of the DVR
valuative criterion when every valuative square whose ring is a discrete
valuation ring has a lift, and the DVR valuative criterion when every such
square has a unique lift.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces satisfies the existence part of the DVR
valuative criterion if every valuative commutative square whose ring is a
discrete valuation ring has a lift. -/
@[mk_iff]
class ValuativeCriterion.DVR.Existence {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- Every DVR valuative square has a dotted lift. -/
  nonempty_liftStruct :
    ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R → Nonempty sq.commSq.LiftStruct

namespace ValuativeCriterion.DVR.Existence

/-- The identity morphism of an algebraic space satisfies DVR existence. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Existence (𝟙 X) := sorry

/-- A morphism satisfies DVR existence if and only if every DVR valuative square
has a lift. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Existence f ↔
      ∀ sq : ValuativeCommSq f,
        IsDiscreteValuationRing sq.R → Nonempty sq.commSq.LiftStruct :=
  sorry

end ValuativeCriterion.DVR.Existence

/-- A morphism of algebraic spaces satisfies the DVR valuative criterion if
every valuative commutative square whose ring is a discrete valuation ring has
a unique lift. -/
@[mk_iff]
class ValuativeCriterion.DVR {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop
    extends ValuativeCriterion.DVR.Uniqueness f, ValuativeCriterion.DVR.Existence f

namespace ValuativeCriterion.DVR

/-- The identity morphism of an algebraic space satisfies the DVR valuative
criterion. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    ValuativeCriterion.DVR (𝟙 X) :=
  sorry

/-- A morphism satisfies the DVR valuative criterion if and only if it satisfies
both the uniqueness and existence parts. -/
theorem iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ValuativeCriterion.DVR f ↔ Uniqueness f ∧ Existence f :=
  sorry

/-- A morphism satisfying the DVR valuative criterion has a unique dotted lift
on every DVR valuative square. -/
theorem unique_liftStruct {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [ValuativeCriterion.DVR f] (sq : ValuativeCommSq f)
    (hR : IsDiscreteValuationRing sq.R) :
    Nonempty (Unique sq.commSq.LiftStruct) :=
  sorry

end ValuativeCriterion.DVR

end AlgebraicGeometry.AlgebraicSpace
