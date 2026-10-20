/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Zero.Determinant
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {R : Type u} [CommRing R] [IsLocalRing R]

/- Lemma 42.68.17 (1): the periodic determinant of `(M, φ, 0)` is the
finite-length determinant of the isomorphism `φ`. -/
@[stacks 02PN] #check
  (CategoryTheory.TwoPeriodicEndomorphism.determinant_swap_ofZero :
    ∀ {M : ModuleCat.{v} R} (hM : IsFiniteLength R M)
        (φ : M ⟶ M) [IsIso φ],
      (TwoPeriodicEndomorphism.determinant
          (TwoPeriodicEndomorphism.swap (TwoPeriodicEndomorphism.ofZero φ)) hM
          ((TwoPeriodicEndomorphism.swap_acyclic_iff (TwoPeriodicEndomorphism.ofZero φ)).2
            (TwoPeriodicEndomorphism.ofZero_acyclic_of_isIso φ)) :
        IsLocalRing.ResidueField R) =
        Module.End.finiteLengthDeterminant φ.hom hM)

/- Lemma 42.68.17 (2): the periodic determinant of `(M, 0, ψ)` is the inverse
of the finite-length determinant of the isomorphism `ψ`. -/
@[stacks 02PN] #check
  (CategoryTheory.TwoPeriodicEndomorphism.determinant_ofZero :
    ∀ {M : ModuleCat.{v} R} (hM : IsFiniteLength R M)
        (ψ : M ⟶ M) [IsIso ψ],
      (TwoPeriodicEndomorphism.determinant (TwoPeriodicEndomorphism.ofZero ψ) hM
          (TwoPeriodicEndomorphism.ofZero_acyclic_of_isIso ψ) :
        IsLocalRing.ResidueField R) =
        (Module.End.finiteLengthDeterminant ψ.hom hM)⁻¹)
