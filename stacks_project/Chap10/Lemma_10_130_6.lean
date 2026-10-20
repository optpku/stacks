/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Fiber.FieldExtension
import StacksCheckRecall

@[expose] public section

/-! @stack 00RJ -/

/-!
# Cohen--Macaulay Field-Extension Recall

The source statement is the local self-module Cohen--Macaulay comparison for a prime of the base
algebra and a prime of the tensor product lying over it.
-/

universe u v w

open Algebra.TensorProduct
open scoped TensorProduct

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {S : Type w} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/- Lemma 10.130.6, tag 00RJ: for a finite-type `k`-algebra `S` and field extension `K / k`,
Cohen--Macaulayness at `q : Spec S` is equivalent to Cohen--Macaulayness at a prime
`qK : Spec(K ⊗[k] S)` lying over `q`. -/
@[stacks 00RJ "Cohen-Macaulay local rings under field extension"]
#check @Module.CohenMacaulay.FieldExtension.FiniteType.localizationAtPrime_iff_of_liesOver

end
