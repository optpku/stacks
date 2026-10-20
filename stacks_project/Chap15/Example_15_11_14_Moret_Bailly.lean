/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.PadicTensorSquare
import StacksCheckRecall

/-!
# Example 15.11.14 (Moret-Bailly)

The explicit tensor-square datum and its consequences are owned by `ReasLib`; this file is the
labeled chapter recall.

@stack 0FWU
-/

@[expose] public section

/- Example 15.11.14 (Moret-Bailly) (1): the tensor coproduct of the two henselian p-adic pairs is not
henselian. -/
@[stacks 0FWU "(1), tensor coproduct of henselian pairs need not be henselian"]
#check @padicInteger_tensor_self_not_henselianRing

/- Example 15.11.14 (Moret-Bailly) (2): for odd primes, the tensor square has the explicit nontrivial
idempotent from Moret-Bailly's construction. -/
@[stacks 0FWU "(2), explicit nontrivial idempotent"]
#check @padicInteger_tensor_self_exists_nontrivial_idempotent_of_two_lt

#check @padicInteger_tensor_self_moretBaillyIdempotent
#check @padicInteger_tensor_self_moretBaillyIdempotent_isIdempotent
#check @padicInteger_tensor_self_pIdeal_eq_span
