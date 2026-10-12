/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.FiniteLength.Determinant.Exact.Naturality

@[expose] public section

universe u v

namespace Module.FiniteLengthDeterminant

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Multiplication by a unit on a finite-length module acts on its determinant line by the
corresponding residue unit raised to the module's length. -/
theorem mapEquiv_smulOfUnit (hM : IsFiniteLength R M) (u : Rˣ) :
    mapEquiv hM hM (LinearEquiv.smulOfUnit u) =
      LinearEquiv.smulOfUnit
        ((Units.map (IsLocalRing.residue R).toMonoidHom u) ^ length R M hM) := sorry

end Module.FiniteLengthDeterminant
