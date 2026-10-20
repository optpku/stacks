/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion

/-!
# DVR valuative criterion for morphisms of algebraic spaces

A morphism of algebraic spaces satisfies the uniqueness part of the DVR
valuative criterion when every valuative square whose ring is a discrete
valuation ring has at most one lift, the existence part when every such square
has a lift, and the DVR valuative criterion when every such square has a unique lift.
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
