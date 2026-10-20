module

public import ReasLib.RingTheory.QuasiFinite.FiniteType
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Quasi-finiteness under base change

This leaf records the pointwise and global base-change criteria behind the
standard stability theorem for quasi-finite ring maps.

@stack 00PP
@stack 00PN
-/

universe u v w x

open TensorProduct
open Algebra.TensorProduct

namespace Algebra.QuasiFiniteAt

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {A : Type w} [CommRing A] [Algebra R A]

/-- A point of a tensor-product base change is quasi-finite exactly when its
image in the original target is. -/
@[stacks 00PP "(1), pointwise base-change criterion"]
theorem baseChange_iff [Algebra.FiniteType R S]
    (q : PrimeSpectrum (A ⊗[R] S)) :
    Algebra.QuasiFiniteAt A q.asIdeal ↔
      Algebra.QuasiFiniteAt R
        (PrimeSpectrum.comap
          (Algebra.TensorProduct.includeRight : S →ₐ[R] (A ⊗[R] S)).toRingHom q).asIdeal := sorry

/-- The quasi-finite locus after tensor-product base change is the inverse
image of the original quasi-finite locus. -/
@[stacks 00PP "(1), quasi-finite locus under base change"]
theorem locus_baseChange [Algebra.FiniteType R S] :
    {q : PrimeSpectrum (A ⊗[R] S) | Algebra.QuasiFiniteAt A q.asIdeal} =
      PrimeSpectrum.comap
          (Algebra.TensorProduct.includeRight : S →ₐ[R] (A ⊗[R] S)).toRingHom ⁻¹'
        {q : PrimeSpectrum S | Algebra.QuasiFiniteAt R q.asIdeal} := sorry

end Algebra.QuasiFiniteAt

namespace Algebra.QuasiFinite

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {A : Type w} [CommRing A] [Algebra R A]

/-- Quasi-finiteness descends and ascends along a base change whose map on
prime spectra is surjective. -/
@[stacks 00PP "(2), descent along a spectrally surjective base change"]
theorem iff_baseChange_of_comap_surjective [Algebra.FiniteType R S]
    (h_comap : Function.Surjective (PrimeSpectrum.comap (algebraMap R A))) :
    Algebra.QuasiFinite R S ↔ Algebra.QuasiFinite A (A ⊗[R] S) := sorry

end Algebra.QuasiFinite

namespace Algebra.FiniteType.QuasiFinite

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {A : Type w} [CommRing A] [Algebra R A]

/-- Base change preserves the quasi-finite predicate, including both finite
type and finite fibers. -/
@[stacks 00PP "(3), stability under arbitrary base change"]
theorem baseChange (h : Algebra.FiniteType.QuasiFinite R S) :
    Algebra.FiniteType.QuasiFinite A (A ⊗[R] S) := sorry

end Algebra.FiniteType.QuasiFinite

namespace Algebra.FiniteType

variable {R : Type u} {S : Type v} {R' : Type w} {S' : Type x}
variable [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
variable [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S']
variable [IsScalarTower R S S'] [IsScalarTower R R' S']

/-- Quasi-finiteness at a prime passes through a tensor-product base change and
then through a surjective target map.  The conclusion retains the finite-type
component of the quasi-finite predicate. -/
@[stacks 00PN "surjective tensor-base-change criterion"]
theorem quasiFiniteAt_baseChange_of_surjective [Algebra.FiniteType R S]
    (h_surjective : Function.Surjective
      (productLeftAlgHom (Algebra.ofId R' S') (IsScalarTower.toAlgHom R S S') :
        R' ⊗[R] S →ₐ[R'] S'))
    (q' : Ideal S') [q'.IsPrime]
    [Algebra.QuasiFiniteAt R (q'.comap (algebraMap S S'))] :
    Algebra.FiniteType R' S' ∧ Algebra.QuasiFiniteAt R' q' := sorry

end Algebra.FiniteType
