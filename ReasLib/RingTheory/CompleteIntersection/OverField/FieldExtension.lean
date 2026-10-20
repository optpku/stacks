/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.OverField
public import ReasLib.RingTheory.CompleteIntersection.OverField.AtPrime

@[expose] public section

/-!
# Complete Intersections over Field Extensions

This leaf owns preservation and reflection of the field-relative local
complete-intersection condition under tensor-product base change.

@stack 00SI
@stack 00SJ
-/

open scoped TensorProduct

universe u v w

namespace IsLocalCompleteIntersection

variable {k : Type u} {K : Type v} {S : Type w}
variable [Field k] [Field K] [CommRing S]
variable [Algebra k K] [Algebra k S]

/-- Lemma 10.135.11, tag `00SJ`: a finite-type algebra is a local complete
intersection exactly when its scalar extension along a field extension is. -/
@[stacks 00SJ "local complete intersections under field extension"]
theorem iff_tensorProduct_fieldExtension [Algebra.FiniteType k S] :
    IsLocalCompleteIntersection k S ↔
      IsLocalCompleteIntersection K (K ⊗[k] S) := sorry

/-- Tensor-product base change along a field extension preserves the canonical
local complete-intersection instance. -/
@[stacks 00SJ "local complete-intersection tensor-product instance"]
instance instTensorProduct [IsLocalCompleteIntersection k S] :
    IsLocalCompleteIntersection K (K ⊗[k] S) := sorry

end IsLocalCompleteIntersection

namespace Algebra.IsCompleteIntersectionOver

variable {k : Type u} {K : Type v} {S : Type w}
variable [Field k] [Field K] [CommRing S]
variable [Algebra k K] [Algebra k S] [Algebra.FiniteType k S]

/-- Lemma 10.135.10: at corresponding primes after a field extension, the source and target local
rings are simultaneously complete intersections over their respective ground fields. -/
@[stacks 00SI "complete intersections at corresponding primes under field extension"]
theorem atPrime_iff_tensorProduct_fieldExtension
    (qK : PrimeSpectrum (K ⊗[k] S)) :
    let q := PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom qK
    IsCompleteIntersectionOver k (Localization.AtPrime q.asIdeal) ↔
      IsCompleteIntersectionOver K (Localization.AtPrime qK.asIdeal) := sorry

end Algebra.IsCompleteIntersectionOver
