/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Zero.Acyclic
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Determinant.Swap
public import ReasLib.Algebra.Module.End.FiniteLength

/-!
# Determinants of Two-Periodic Complexes with One Zero Differential

This file computes the determinant of an acyclic finite-length two-periodic endomorphism complex
when one differential is zero and the other is an isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The periodic determinant of the complex with differentials `(φ, 0)` is the finite-length
determinant of the isomorphism `φ`. -/
theorem determinant_swap_ofZero {M : ModuleCat.{v} R} (hM : IsFiniteLength R M)
    (φ : M ⟶ M) [IsIso φ] :
    (determinant (swap (ofZero φ)) hM
        ((swap_acyclic_iff (ofZero φ)).2 (ofZero_acyclic_of_isIso φ)) :
      IsLocalRing.ResidueField R) =
      Module.End.finiteLengthDeterminant φ.hom hM := sorry

/-- The periodic determinant of the complex with differentials `(0, ψ)` is the inverse of the
finite-length determinant of the isomorphism `ψ`. -/
theorem determinant_ofZero {M : ModuleCat.{v} R} (hM : IsFiniteLength R M)
    (ψ : M ⟶ M) [IsIso ψ] :
    (determinant (ofZero ψ) hM (ofZero_acyclic_of_isIso ψ) :
      IsLocalRing.ResidueField R) =
      (Module.End.finiteLengthDeterminant ψ.hom hM)⁻¹ := sorry

end CategoryTheory.TwoPeriodicEndomorphism
