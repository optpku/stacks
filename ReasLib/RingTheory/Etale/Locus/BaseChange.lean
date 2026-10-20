/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Flat base change of etale loci

This leaf owns the pointwise and set-theoretic forms of the flat base-change
description of `Algebra.etaleLocus`.  The tensor-product inclusion is written
explicitly so that consumers do not have to reconstruct the intended algebra
homomorphism from a coercion or a local instance.
-/

open scoped TensorProduct

universe u v w

namespace Algebra

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']
variable [FinitePresentation R S] [Module.Flat R R']

/-- Membership in the etale locus is preserved and reflected at every prime
under a flat tensor-product base change. -/
@[stacks 00U2 "pointwise flat base change of etale loci"]
theorem mem_etaleLocus_baseChange_iff
    (q' : PrimeSpectrum (R' ⊗[R] S)) :
    PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom q' ∈
        etaleLocus R S ↔
      q' ∈ etaleLocus R' (R' ⊗[R] S) := sorry

/-- Lemma 10.143.3 (00U2), clause (5): the etale locus after a flat
tensor-product base change is the inverse image of the original etale locus. -/
@[stacks 00U2 "flat base change of etale loci"]
theorem etaleLocus_preimage_includeRight_eq_baseChange :
    PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom ⁻¹'
        etaleLocus R S =
      etaleLocus R' (R' ⊗[R] S) := sorry

end Algebra
