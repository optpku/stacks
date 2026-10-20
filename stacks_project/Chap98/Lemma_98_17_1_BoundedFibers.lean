/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.BoundedFiniteTypeFibers

/-!
# Bounded finite-type field fibres

The uniform bound on isomorphism classes and arrows in finite-type field fibres.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver
open scoped Cardinal

universe u

#check (AlgebraicGeometry.GroupoidsOver.HasBoundedFiniteTypeFibers :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S), Prop)

#check (AlgebraicGeometry.GroupoidsOver.HasBoundedFiniteTypeFibers.slice :
  ∀ {S : Scheme.{u}} (U : Over S),
    HasBoundedFiniteTypeFibers (GroupoidsOver.slice U))

#check (AlgebraicGeometry.GroupoidsOver.HasBoundedFiniteTypeFibers.spec :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [HasBoundedFiniteTypeFibers X],
    ∃ T : Over S,
      ∀ {k : Type u} [Field k] (kToS : Spec (CommRingCat.of k) ⟶ S)
        [LocallyOfFiniteType kToS],
        #(Quotient (isIsomorphicSetoid (X.p.Fiber (Over.mk kToS)))) ≤
            Cardinal.lift.{u + 1} T.left.size ∧
          #(Arrow (X.p.Fiber (Over.mk kToS))) ≤
            Cardinal.lift.{u + 1} T.left.size)

#check (AlgebraicGeometry.GroupoidsOver.HasBoundedFiniteTypeFibers.iff :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    HasBoundedFiniteTypeFibers X ↔
      ∃ T : Over S,
        ∀ {k : Type u} [Field k] (kToS : Spec (CommRingCat.of k) ⟶ S)
          [LocallyOfFiniteType kToS],
          #(Quotient (isIsomorphicSetoid (X.p.Fiber (Over.mk kToS)))) ≤
              Cardinal.lift.{u + 1} T.left.size ∧
            #(Arrow (X.p.Fiber (Over.mk kToS))) ≤
              Cardinal.lift.{u + 1} T.left.size)
