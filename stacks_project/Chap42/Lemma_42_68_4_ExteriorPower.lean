/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.FiniteLength.Determinant.ExteriorPower

@[expose] public section

noncomputable section

universe u v

namespace Module.FiniteLengthDeterminant

variable (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
variable [AddCommGroup M] [Module R M]

/- The promoted comparison has its original complete public type through this compatibility
module. -/
#check (Module.FiniteLengthDeterminant.toExteriorPower R M :
  (hM : IsFiniteLength R M) →
  (hAnn : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R)) →
  (hl :
    letI : Module (IsLocalRing.ResidueField R) M := hAnn.module
    length R M hM = Module.finrank (IsLocalRing.ResidueField R) M) →
  letI : Module (IsLocalRing.ResidueField R) M := hAnn.module
  Module.FiniteLengthDeterminant R M hM →ₗ[IsLocalRing.ResidueField R]
    ⋀[IsLocalRing.ResidueField R]^(Module.finrank (IsLocalRing.ResidueField R) M) M)

end Module.FiniteLengthDeterminant
