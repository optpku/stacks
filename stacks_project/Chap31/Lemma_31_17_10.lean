/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm.QuasiAffine.Descent
import StacksCheckRecall

/-!
# Lemma 31.17.10

Descent of quasi-affineness along standard classes of finite surjections.

@stack 0BD5
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 31.17.10: the target of a finite locally free surjection from a quasi-affine scheme is
quasi-affine. -/
@[stacks 0BD5]
#check (AlgebraicGeometry.Scheme.IsQuasiAffine.target_of_isFiniteLocallyFree_surjective :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (π : X ⟶ Y)
      [AlgebraicGeometry.IsFiniteLocallyFree π] [AlgebraicGeometry.Surjective π]
      (hX : X.IsQuasiAffine),
    Y.IsQuasiAffine)

/- The integral-normal branch: the target of a finite surjection from a quasi-affine scheme is
quasi-affine when the target is integral and normal. -/
#check (AlgebraicGeometry.Scheme.IsQuasiAffine.target_of_isFinite_surjective_isIntegral_isNormal :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (π : X ⟶ Y)
      [AlgebraicGeometry.IsFinite π] [AlgebraicGeometry.Surjective π]
      [AlgebraicGeometry.IsIntegral Y]
      (hYnormal : Y.isNormal) (hX : X.IsQuasiAffine),
    Y.IsQuasiAffine)
