/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.TensorPresentation
import StacksCheckRecall

@[expose] public section

/-!
# Tensor presentation of Kähler differentials

@stack 00RW

Mathlib's canonical Kähler differential is already the cotangent module of the multiplication
kernel. The ReasLib companion records the explicit tensor representative used by the source.
-/

/- Lemma 10.131.13: if `J` is the kernel of `S ⊗[R] S → S`, then `Ω[S⁄R]` is canonically
`J / J²`, and `a • db` is represented by `a ⊗ b - ab ⊗ 1`. -/
@[stacks 00RW "cotangent presentation"]
#check @KaehlerDifferential

@[stacks 00RW "explicit tensor representative"]
#check @KaehlerDifferential.smul_D_apply

#check @KaehlerDifferential.ideal
#check @KaehlerDifferential.D_apply
#check @KaehlerDifferential.tensor_sub_mul_tmul_one_mem_ideal
