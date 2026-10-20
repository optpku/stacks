module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.KrullDimension.Relative.Transport

@[expose] public section

/-!
# Base change of relative-dimension loci

This leaf owns the comparison of bounded relative-dimension loci with their
arbitrary tensor-product base changes.  The base-changed tensor product is
viewed through mathlib's canonical left `R'`-algebra, so consumers need no
additional tensor-product instance setup.

@stack 00QI
-/

noncomputable section

open scoped TensorProduct

universe u v w

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

/-- Under arbitrary base change, relative dimension at an upstairs prime equals relative
dimension at its contraction along the canonical right tensor inclusion. -/
@[stacks 00QI "pointwise relative dimension under base change"]
theorem RelativeDimensionAt.comap_includeRight_eq_baseChange
    [Algebra.FiniteType R S] (q' : PrimeSpectrum (R' ⊗[R] S)) :
    relativeDimensionAt R S
        (PrimeSpectrum.comap
          (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom q') =
      relativeDimensionAt R' (R' ⊗[R] S) q' := sorry

namespace RelativeDimensionAtLELocus

/-- Membership in a bounded relative-dimension locus is preserved and reflected by arbitrary
base change along the canonical right tensor inclusion. -/
@[stacks 00QI "pointwise bounded-locus membership under base change"]
theorem comap_includeRight_mem_iff_baseChange
    [Algebra.FiniteType R S] (n : ℕ) (q' : PrimeSpectrum (R' ⊗[R] S)) :
    PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom q' ∈
      relativeDimensionAtLELocus R S n ↔
      q' ∈ relativeDimensionAtLELocus R' (R' ⊗[R] S) n := sorry

/-- Lemma 10.125.7, tag 00QI: for a finite-type `R`-algebra `S`, the inverse image of the
bounded relative-dimension locus along the canonical map `Spec (R' ⊗[R] S) → Spec S` is the
corresponding locus of the base-changed `R'`-algebra. -/
@[stacks 00QI "base change of the bounded relative-dimension locus"]
theorem preimage_includeRight_eq_baseChange
    [Algebra.FiniteType R S] (n : ℕ) :
    (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom) ⁻¹'
        relativeDimensionAtLELocus R S n =
      relativeDimensionAtLELocus R' (R' ⊗[R] S) n := sorry

end RelativeDimensionAtLELocus
