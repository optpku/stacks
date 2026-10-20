/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.FiniteLength.Determinant.Functoriality

/-!
# Functoriality of finite-length determinant lines

Compatibility bridge for determinant-line functoriality under module equivalences.
-/

@[expose] public section

noncomputable section

universe u v

namespace Module.FiniteLengthDeterminant

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M N P : Type v}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/- The reusable determinant equivalence has the expected source-facing type. -/
#check (mapEquiv :
  (hM : IsFiniteLength R M) → (hN : IsFiniteLength R N) → (M ≃ₗ[R] N) →
    Module.FiniteLengthDeterminant R M hM ≃ₗ[IsLocalRing.ResidueField R]
      Module.FiniteLengthDeterminant R N hN)

end Module.FiniteLengthDeterminant
