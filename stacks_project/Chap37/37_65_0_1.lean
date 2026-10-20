/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Normalization.IntegralClosurePullback
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory Limits

universe u

/- 37.65.0.1: if `B` is the integral closure of a Dedekind domain `A` in a finite
extension of `FractionRing A`, then the normalization of the pullback of
`X ⟶ Spec(A)` to `Spec(B)` maps to the displayed commutative pullback diagram. -/
@[stacks 09IK] #check
  (AlgebraicGeometry.Scheme.Normalization.integralClosurePullback_condition :
    ∀ (A L : Type u) [CommRing A] [IsDedekindDomain A] [Field L]
      [Algebra A L] [Algebra (FractionRing A) L]
      [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L]
      (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A)) [Flat f]
      [Scheme.Hom.FiniteType f],
    let B := integralClosure A L
    -- Local instance justification (search instability): the nonseparable finite-extension theorem supplies the canonical Dedekind structure needed for normalization prerequisites.
    letI : IsDedekindDomain B :=
      FractionRing.IntegralClosure.isDedekind_of_finite_extension
    let g : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A B))
    let X_B := pullback f g
    X_B.normalizationTo ≫ (pullback.fst f g ≫ f) =
      X_B.normalizationTo ≫ (pullback.snd f g ≫ g))
