/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocal
public import ReasLib.AlgebraicGeometry.Scheme.SerreCondition.Etale

/-!
# Serre conditions on algebraic spaces

An algebraic space satisfies `(S_k)` when it has the étale-local scheme property of
being locally Noetherian and satisfying `(S_k)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space satisfies `(S_k)` when it has the étale-local type-property of
being locally Noetherian and satisfying the scheme-theoretic Serre condition
`(S_k)`. -/
def satisfiesSerreConditionS {S : Scheme.{u}} (X : AlgebraicSpace S) (k : ℕ) : Prop :=
  hasEtaleLocal
    (fun U : Scheme.{u} ↦
      AlgebraicGeometry.IsLocallyNoetherian U ∧ Scheme.satisfiesSerreConditionS U k)
    X

/-- `satisfiesSerreConditionS X k` is the étale-local type-property of being locally
Noetherian and satisfying the scheme-theoretic condition `(S_k)`. -/
theorem satisfiesSerreConditionS_def {S : Scheme.{u}} (X : AlgebraicSpace S)
    (k : ℕ) :
    satisfiesSerreConditionS X k ↔
      hasEtaleLocal
        (fun U : Scheme.{u} ↦
          AlgebraicGeometry.IsLocallyNoetherian U ∧ Scheme.satisfiesSerreConditionS U k)
        X :=
  Iff.rfl

/-- An algebraic space satisfies `(S_k)` if and only if every étale morphism from a
scheme to it has locally Noetherian source satisfying `(S_k)`. -/
theorem satisfiesSerreConditionS_iff_forallEtale {S : Scheme.{u}}
    (X : AlgebraicSpace S) (k : ℕ) :
    satisfiesSerreConditionS X k ↔
      forallEtale
        (fun U : Scheme.{u} ↦
          AlgebraicGeometry.IsLocallyNoetherian U ∧ Scheme.satisfiesSerreConditionS U k)
        X :=
  existsSurjectiveEtale_iff_forallEtale
    (fun U : Scheme.{u} ↦
      AlgebraicGeometry.IsLocallyNoetherian U ∧ Scheme.satisfiesSerreConditionS U k) X

/-- A locally Noetherian scheme over `S`, viewed as an algebraic space, satisfies
`(S_k)` if and only if the scheme itself satisfies `(S_k)`. -/
theorem satisfiesSerreConditionS_ofOver {S : Scheme.{u}} (T : Over S)
    [AlgebraicGeometry.IsLocallyNoetherian T.left] (k : ℕ) :
    satisfiesSerreConditionS (ofOver T) k ↔ T.left.satisfiesSerreConditionS k :=
  by
    simpa only [satisfiesSerreConditionS, hasEtaleLocal, and_iff_right
      (show AlgebraicGeometry.IsLocallyNoetherian T.left from inferInstance)] using
      existsSurjectiveEtale_ofOver
        (fun U : Scheme.{u} ↦
          AlgebraicGeometry.IsLocallyNoetherian U ∧ Scheme.satisfiesSerreConditionS U k) T

end AlgebraicGeometry.AlgebraicSpace
