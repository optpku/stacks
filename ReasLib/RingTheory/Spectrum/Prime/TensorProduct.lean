module

public import ReasLib.RingTheory.Spectrum.Prime.Irreducible
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Irreducibility of Tensor-Product Spectra

This leaf owns the separably-closed tensor-product criterion in ring language.
The geometric proof may use the affine scheme API, but the reusable interface
only exposes prime spectra and minimal primes.

@stack 00I7
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace PrimeSpectrum

variable {k R S : Type u}
variable [Field k] [IsSepClosed k]
variable [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

/-- Over a separably closed field, tensoring with an irreducible affine algebra
preserves irreducibility of prime spectra. -/
@[stacks 00I7 "tensor-product irreducibility"]
theorem irreducible_tensorProduct
    (hR : IrreducibleSpace (PrimeSpectrum R))
    (hS : IrreducibleSpace (PrimeSpectrum S)) :
    IrreducibleSpace (PrimeSpectrum (R ⊗[k] S)) := sorry

/-- Over a separably closed field, two rings with one minimal prime have a
tensor product with one minimal prime. -/
@[stacks 00I7 "tensor-product minimal prime"]
theorem unique_minimalPrime_tensorProduct
    (hR : ∃! p : Ideal R, p ∈ minimalPrimes R)
    (hS : ∃! p : Ideal S, p ∈ minimalPrimes S) :
    ∃! p : Ideal (R ⊗[k] S), p ∈ minimalPrimes (R ⊗[k] S) := sorry

end PrimeSpectrum
