/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Spectrum.Prime.Topology
import StacksCheckRecall
import ReasLib.RingTheory.Polynomial.Int.Spectrum

open Polynomial PrimeSpectrum

#check (IntPolynomial.IrreduciblePrincipalIdealForm : Ideal ℤ[X] → Prop)

#check (IntPolynomial.IrreduciblePairIdealForm : Ideal ℤ[X] → Prop)

#check (IntPolynomial.IrreduciblePrincipalIdealForm.isPrime :
  ∀ {I : Ideal ℤ[X]}, IntPolynomial.IrreduciblePrincipalIdealForm I → I.IsPrime)

#check (IntPolynomial.IrreduciblePairIdealForm.isMaximal :
  ∀ {I : Ideal ℤ[X]}, IntPolynomial.IrreduciblePairIdealForm I → I.IsMaximal)

#check (IntPolynomial.IrreduciblePairIdealForm.isPrime :
  ∀ {I : Ideal ℤ[X]}, IntPolynomial.IrreduciblePairIdealForm I → I.IsPrime)

#check (IntPolynomial.isPrime_iff :
  ∀ I : Ideal ℤ[X],
    I.IsPrime ↔
      I = ⊥ ∨
        IntPolynomial.IrreduciblePrincipalIdealForm I ∨
        IntPolynomial.IrreduciblePairIdealForm I)

/- Exercise 111.6.31 -/
@[stacks 02DK] #check (IntPolynomial.eq_bot_or_principal_or_pair :
  ∀ p : PrimeSpectrum ℤ[X],
    p.asIdeal = ⊥ ∨
      IntPolynomial.IrreduciblePrincipalIdealForm p.asIdeal ∨
      IntPolynomial.IrreduciblePairIdealForm p.asIdeal)

#check (PrimeSpectrum.le_iff_specializes :
  ∀ x y : PrimeSpectrum ℤ[X], x ≤ y ↔ x ⤳ y)

#check (PrimeSpectrum.isClosed_singleton_iff_isMaximal :
  ∀ x : PrimeSpectrum ℤ[X],
    IsClosed ({x} : Set (PrimeSpectrum ℤ[X])) ↔ x.asIdeal.IsMaximal)

#check (PrimeSpectrum.isClosed_iff_zeroLocus :
  ∀ Z : Set (PrimeSpectrum ℤ[X]),
    IsClosed Z ↔ ∃ s : Set ℤ[X], Z = zeroLocus s)

#check (PrimeSpectrum.mem_zeroLocus :
  ∀ x : PrimeSpectrum ℤ[X], ∀ s : Set ℤ[X],
    x ∈ zeroLocus s ↔ s ⊆ x.asIdeal)

#check (AlgebraicGeometry.AffineSpace.SpecIso (Fin 1) (CommRingCat.of ℤ) :
  AlgebraicGeometry.AffineSpace (Fin 1) (AlgebraicGeometry.Spec (CommRingCat.of ℤ)) ≅
    AlgebraicGeometry.Spec (CommRingCat.of (MvPolynomial (Fin 1) ℤ)))

#check (MvPolynomial.uniqueAlgEquiv ℤ (Fin 1) :
  MvPolynomial (Fin 1) ℤ ≃ₐ[ℤ] ℤ[X])
