/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Unramified.LocalStructure
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.152.2
@stack 00UX

The standard-étale-surjection theorem owns the local unramified input.  This chapter file keeps
the source-facing product decomposition, including the selected primes and both lying-over
conditions, as a single thin bridge.
-/

open scoped TensorProduct
open Algebra.TensorProduct

universe u v

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]

/-- Lemma 10.152.2: if `q` lies over `p` and `R → S` is unramified at `q`, then after an
étale base change `R → R'` the tensor product `R' ⊗[R] S` splits as `A × B`, with
`R' → A` surjective and the extended prime of `A` lying over both selected primes. -/
@[stacks 00UX]
theorem exists_etale_baseChange_prod_of_isUnramifiedAt
    (p : Ideal R) (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra.IsUnramifiedAt R q] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p)
      (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R' A)
      (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R' B)
      (e : R' ⊗[R] S ≃ₐ[R'] A × B),
      let pA : Ideal A := Ideal.map (algebraMap R' A) p'
      let πA : S →+* A :=
        (((RingHom.fst A B).comp e.toRingHom).comp
          (includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom)
      Function.Surjective (algebraMap R' A) ∧
        pA.IsPrime ∧
        pA.LiesOver p' ∧
        Ideal.comap πA pA = q := sorry

end

@[stacks 00UX "standard-étale local owner"]
#check @Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn

@[stacks 00UX "tensor-product right inclusion"]
#check @Algebra.TensorProduct.includeRight

@[stacks 00UX "source-facing product decomposition"]
#check @exists_etale_baseChange_prod_of_isUnramifiedAt

end
