/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Smooth.AtPrime
public import ReasLib.RingTheory.Smooth.Locus.BaseChange

@[expose] public section

/-!
# Smoothness at Primes under Field Extension

This leaf owns the pointwise smoothness comparison for a finite-type algebra
after tensoring with a field extension.  It exposes both the Stacks-facing
principal-open predicate and mathlib's canonical local predicate.
@stack 02UQ
-/

open scoped TensorProduct

universe u v w

namespace Algebra

variable {k : Type u} {K : Type v} {S : Type w}
variable [Field k] [Field K] [CommRing S]
variable [Algebra k K] [Algebra k S] [Algebra.FiniteType k S]

namespace SmoothAtPrime

/-- Lemma 10.137.18, tag `02UQ`: smoothness on a principal-open neighbourhood
of a prime is preserved and reflected by tensoring a finite-type algebra with
a field extension. -/
@[stacks 02UQ "smoothness at a prime under field extension"]
theorem iff_tensorProduct_fieldExtension
    (qK : PrimeSpectrum (K ⊗[k] S)) :
    let q := PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom qK
    SmoothAtPrime k S q ↔ SmoothAtPrime K (K ⊗[k] S) qK := sorry

end SmoothAtPrime

namespace IsSmoothAt

/-- The canonical local-predicate form of
`SmoothAtPrime.iff_tensorProduct_fieldExtension`. -/
theorem iff_tensorProduct_fieldExtension
    (qK : PrimeSpectrum (K ⊗[k] S)) :
    let q := PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom qK
    IsSmoothAt k q.asIdeal ↔ IsSmoothAt K qK.asIdeal := sorry

end IsSmoothAt

end Algebra
