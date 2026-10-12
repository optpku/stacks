/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Restricting primes of an algebra tensor product

This file names the two canonical contractions from the spectrum of `A ⊗[R] B` to the spectra
of its factors. The definitions are symmetric and keep the tensor-inclusion implementation out of
downstream statements.
-/

open scoped TensorProduct

universe u v w

namespace Algebra.TensorProduct

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [CommSemiring A] [CommSemiring B]
variable [Algebra R A] [Algebra R B]

/-- Restrict a prime of `A ⊗[R] B` to the left tensor factor. -/
@[stacks 00RJ "left prime restriction"]
def restrictLeft (q : PrimeSpectrum (A ⊗[R] B)) : PrimeSpectrum A :=
  PrimeSpectrum.comap
    (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B) q

/-- Restrict a prime of `A ⊗[R] B` to the right tensor factor. -/
@[stacks 00RJ "right prime restriction"]
def restrictRight (q : PrimeSpectrum (A ⊗[R] B)) : PrimeSpectrum B :=
  PrimeSpectrum.comap
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom q

/-- The ideal of `restrictLeft q` is the contraction along the left tensor inclusion. -/
@[simp]
theorem restrictLeft_asIdeal (q : PrimeSpectrum (A ⊗[R] B)) :
    (restrictLeft q).asIdeal =
      Ideal.comap
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B) q.asIdeal := sorry

/-- The ideal of `restrictRight q` is the contraction along the right tensor inclusion. -/
@[simp]
theorem restrictRight_asIdeal (q : PrimeSpectrum (A ⊗[R] B)) :
    (restrictRight q).asIdeal =
      Ideal.comap
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom q.asIdeal := sorry

end Algebra.TensorProduct
