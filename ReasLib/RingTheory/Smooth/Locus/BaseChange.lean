/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.TensorProduct.Flat
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra

@[expose] public section

/-!
# Flat Base Change of Smooth Loci

This leaf owns the inverse-image description of the smooth locus after a flat
tensor-product base change.  The right tensor algebra is selected through the
shared scoped owner, avoiding a competing global tensor-product instance.
-/

open scoped TensorProduct
open scoped Algebra.TensorProduct.Right

universe u v w

namespace Algebra

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R'] [FinitePresentation R S] [Module.Flat R R']

/-- Membership in the smooth locus is preserved and reflected at every prime
after a flat tensor-product base change. -/
theorem mem_smoothLocus_baseChange_iff
    (q' : PrimeSpectrum (R' ⊗[R] S)) :
    PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom q' ∈
        smoothLocus R S ↔
      q' ∈ smoothLocus R' (R' ⊗[R] S) := sorry

/-- Lemma 10.137.17, tag `00TG`: under a flat tensor-product base change, the
smooth locus is exactly the inverse image of the original smooth locus. -/
@[stacks 00TG "flat base change of smooth loci"]
theorem smoothLocus_preimage_includeRight_eq_baseChange :
    PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom ⁻¹'
        smoothLocus R S =
      smoothLocus R' (R' ⊗[R] S) := sorry

end Algebra
