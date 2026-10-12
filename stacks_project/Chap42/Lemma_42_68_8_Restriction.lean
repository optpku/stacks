/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.FiniteLength.Determinant.Restriction

open CategoryTheory

universe u u' v

variable {R' : Type u'} {R : Type u} [CommRing R'] [CommRing R]
variable [IsLocalRing R'] [IsLocalRing R]

/- A typed compatibility check for the determinant-line equivalence under restriction of
scalars. -/
#check
  (Module.FiniteLengthDeterminant.Restriction.equiv :
    ∀ (f : R' →+* R) [IsLocalHom f]
      (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
      (M : ModuleCat.{v} R) (hM : IsFiniteLength R M),
      Module.FiniteLengthDeterminant R M hM ≃ₛₗ[
        (Module.FiniteLengthDeterminant.Restriction.residueEquiv f hκ).symm.toRingHom]
        Module.FiniteLengthDeterminant R' ((ModuleCat.restrictScalars f).obj M)
          (Module.FiniteLengthDeterminant.Restriction.isFiniteLength f hκ M hM))
