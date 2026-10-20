/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SerreCondition

/-!
# Serre conditions on algebraic spaces

The Serre-condition predicate and its specification and comparison statements.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.satisfiesSerreConditionS :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (k : ℕ), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.satisfiesSerreConditionS_def :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (k : ℕ),
    satisfiesSerreConditionS X k ↔
      hasEtaleLocal
        (fun U : Scheme.{u} ↦
          AlgebraicGeometry.IsLocallyNoetherian U ∧ Scheme.satisfiesSerreConditionS U k)
        X)

#check (AlgebraicGeometry.AlgebraicSpace.satisfiesSerreConditionS_iff_forallEtale :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (k : ℕ),
    satisfiesSerreConditionS X k ↔
      forallEtale
        (fun U : Scheme.{u} ↦
          AlgebraicGeometry.IsLocallyNoetherian U ∧ Scheme.satisfiesSerreConditionS U k)
        X)

#check (AlgebraicGeometry.AlgebraicSpace.satisfiesSerreConditionS_ofOver :
  ∀ {S : Scheme.{u}} (T : Over S) [AlgebraicGeometry.IsLocallyNoetherian T.left] (k : ℕ),
    satisfiesSerreConditionS (ofOver T) k ↔ T.left.satisfiesSerreConditionS k)

end AlgebraicGeometry.AlgebraicSpace
