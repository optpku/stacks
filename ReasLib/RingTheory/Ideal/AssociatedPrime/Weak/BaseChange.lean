/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.DirectSum
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.Localization
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Weakly associated primes under field base change

The canonical owner for a field extension is the `R ⊗[k] K`-module
`(R ⊗[k] K) ⊗[R] M`.  The source-facing `M ⊗[k] K` presentation is a bridge
and is intentionally kept out of this core leaf.  This avoids choosing a
noncanonical scalar-action instance on the textbook tensor presentation.
-/

open scoped TensorProduct

universe u v w

namespace weaklyAssociatedPrimes

namespace BaseChange

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {R : Type w} [CommRing R] [Algebra k R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Contracting a weakly associated prime of `(R ⊗[k] K) ⊗[R] M` to `R` gives a weakly
associated prime of `M`. -/
@[stacks 0CUB]
theorem under_mem
    (q : Ideal (R ⊗[k] K))
    (hq : q ∈ weaklyAssociatedPrimes (R ⊗[k] K)
      ((R ⊗[k] K) ⊗[R] M)) :
    q.under R ∈ weaklyAssociatedPrimes R M := sorry

end BaseChange

end weaklyAssociatedPrimes
