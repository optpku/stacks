/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CohenMacaulay.Fiber.FieldExtension
public import ReasLib.RingTheory.CohenMacaulay.Fiber.Locus
public import ReasLib.RingTheory.RingHom.Fiber.BaseChange

@[expose] public section

/-!
# Base Change of Cohen--Macaulay Fiber Loci

@stack 00RK

This leaf records the pointwise and setwise base-change invariance of the
Cohen--Macaulay locus of residue-field fibers.
-/

open scoped TensorProduct

universe u v w

namespace PrimeSpectrum

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R'] [Algebra.FiniteType R S]

/-- Membership in the Cohen--Macaulay fiber locus is preserved and reflected by
arbitrary tensor-product base change. -/
@[stacks 00RK "Cohen-Macaulay fiber locus and base change"]
theorem mem_cohenMacaulayFiberLocus_baseChange_iff
    (q' : PrimeSpectrum (R' ⊗[R] S)) :
    PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom q' ∈
        cohenMacaulayFiberLocus R S ↔
      q' ∈ cohenMacaulayFiberLocus R' (R' ⊗[R] S) := sorry

/-- The Cohen--Macaulay fiber locus pulls back exactly along arbitrary
tensor-product base change. -/
@[stacks 00RK "Cohen-Macaulay fiber locus and base change"]
theorem cohenMacaulayFiberLocus_preimage_includeRight_eq_baseChange :
    PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom ⁻¹'
        cohenMacaulayFiberLocus R S =
      cohenMacaulayFiberLocus R' (R' ⊗[R] S) := sorry

end PrimeSpectrum
