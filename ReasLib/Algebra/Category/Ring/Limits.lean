/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Limits

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace RingCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ CommRingCat.{u})
variable [UnivLE.{v, u}]

/-- The limit of the underlying ring diagram of commutative rings is commutative,
with the ring operations of the chosen ring limit. -/
noncomputable instance limitOfCommCommRing :
    CommRing (limit (F ⋙ forget₂ CommRingCat RingCat) : RingCat.{u}) where
  toRing := inferInstance
  mul_comm :=
    let e := (limit.isoLimitCone
      ⟨RingCat.limitCone (F ⋙ forget₂ CommRingCat RingCat),
        RingCat.limitConeIsLimit (F ⋙ forget₂ CommRingCat RingCat)⟩).ringCatIsoToRingEquiv
    (@Function.Injective.commMagma _ _ inferInstance
      (CommRingCat.limitCommRing F).toCommMagma e e.injective e.map_mul).mul_comm

/-- Multiplication in the ring limit of a commutative-ring diagram commutes. -/
noncomputable instance limitOfComm_commutative :
    Fact (∀ a b : (limit (F ⋙ forget₂ CommRingCat RingCat) : RingCat.{u}), a * b = b * a) :=
  ⟨(limitOfCommCommRing F).mul_comm⟩

end RingCat
