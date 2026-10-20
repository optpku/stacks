module

public import ReasLib.Algebra.Module.FiniteLength.Determinant

/-!
# Determinant space of a finite-length module

Compatibility bridge for the reusable determinant-space presentation.
-/

@[expose] public section

noncomputable section

universe u v

namespace Module.FiniteLengthDeterminant

variable (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
variable [AddCommGroup M] [Module R M]

/- The quotient-class constructor has the expected source-facing type. -/
#check (symbol R M :
  ∀ hM : IsFiniteLength R M,
    Symbol R M hM → Module.FiniteLengthDeterminant R M hM)

end Module.FiniteLengthDeterminant
