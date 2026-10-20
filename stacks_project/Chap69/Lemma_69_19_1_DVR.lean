/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR

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

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Uniqueness :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Uniqueness.id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S},
    AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Uniqueness (𝟙 X))

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Uniqueness.of_uniqueness :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Uniqueness f],
    AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Uniqueness f)

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Uniqueness.spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Uniqueness f ↔
      ∀ sq : AlgebraicGeometry.AlgebraicSpace.ValuativeCommSq f,
        IsDiscreteValuationRing sq.R → Subsingleton sq.commSq.LiftStruct)
