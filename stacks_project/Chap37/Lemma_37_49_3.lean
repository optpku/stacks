/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiAffine.Integral
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.49.3 (1): the source of an integral morphism to a quasi-affine scheme is
quasi-affine. -/
@[stacks 0EJY] #check
  (AlgebraicGeometry.Scheme.IsQuasiAffine.of_isIntegralHom :
    ∀ {U X : AlgebraicGeometry.Scheme.{u}}
      (f : U ⟶ X) [X.IsQuasiAffine] [AlgebraicGeometry.IsIntegralHom f],
      U.IsQuasiAffine)

/- Lemma 37.49.3 (2): for an integral morphism `f : U ⟶ X` to a quasi-affine scheme,
the square formed by `f`, `U.toSpecΓ`, `X.toSpecΓ`, and `Spec.map f.appTop` is cartesian. -/
@[stacks 0EJY] #check
  (AlgebraicGeometry.Scheme.isPullback_toSpecΓ_of_isIntegralHom :
    ∀ {U X : AlgebraicGeometry.Scheme.{u}}
      (f : U ⟶ X) [X.IsQuasiAffine] [AlgebraicGeometry.IsIntegralHom f],
      IsPullback f U.toSpecΓ X.toSpecΓ (AlgebraicGeometry.Spec.map f.appTop))
