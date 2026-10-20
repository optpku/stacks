/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

@[expose] public section

universe u

namespace RatFunc

variable {k : Type u} [Field k]

/-- The canonical ring homomorphism from the localization away from a nonzero polynomial
to the rational function field. -/
noncomputable def fromAway {f : Polynomial k} (hf : f ≠ 0) :
    Localization.Away f →+* RatFunc k :=
  IsLocalization.Away.lift f
    (isUnit_iff_ne_zero.mpr fun h ↦
      hf ((RatFunc.algebraMap_injective k)
        (h.trans (map_zero (algebraMap (Polynomial k) (RatFunc k))).symm)) :
      IsUnit (algebraMap (Polynomial k) (RatFunc k) f))

end RatFunc
