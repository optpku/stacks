/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion
public import stacks_project.Chap69.Lemma_69_19_1_DVR
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR

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

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Existence :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Existence.id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S},
    AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Existence (𝟙 X))

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Existence.spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Existence f ↔
      ∀ sq : AlgebraicGeometry.AlgebraicSpace.ValuativeCommSq f,
        IsDiscreteValuationRing sq.R → Nonempty sq.commSq.LiftStruct)

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S},
    AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR (𝟙 X))

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR f ↔
      AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Uniqueness f ∧
        AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Existence f)

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.unique_liftStruct :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR f]
    (sq : AlgebraicGeometry.AlgebraicSpace.ValuativeCommSq f)
    (hR : IsDiscreteValuationRing sq.R), Nonempty (Unique sq.commSq.LiftStruct))
