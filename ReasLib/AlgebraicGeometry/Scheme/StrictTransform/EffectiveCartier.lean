/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.StrictTransform

/-!
# Strict transforms and effective Cartier divisors

For a module without nonzero local sections supported on an effective Cartier divisor,
multiplying a blowup center by that divisor does not change the strict transform.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- If a quasicoherent module has no nonzero local sections supported on the inverse image of
an effective Cartier divisor, multiplying a blowup center by that divisor does not change the
module's strict transform. -/
theorem strictTransformModule_mul_eq_of_noSectionsSupportedOn
    {S S' X : Scheme.{u}} (I D : S.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (b : S' ⟶ S) [IsBlowup b I]
    (f : X ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (hsections : ∀ (U : X.Opens) (s : ℱ.val.obj (op U)),
      SheafOfModules.localSectionSupport s ⊆
        {x : U | (x : X) ∈ ((D.comap f).support : Set X)} → s = 0) :
    strictTransformModule b (I.comap b) f ℱ =
      strictTransformModule b ((I * D).comap b) f ℱ := sorry

end AlgebraicGeometry.Scheme.Modules
