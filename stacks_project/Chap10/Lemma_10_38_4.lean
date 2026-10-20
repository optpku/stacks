/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.ReesAlgebra.Integral
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.38.4

This chapter entry recalls the reusable ideal-extension theorem.
@stack 00H5
-/

/- Lemma 10.38.4 (Tag 00H5): every element of an extended ideal is integral
over the source ideal along an integral ring homomorphism. -/
@[stacks 00H5]
#check @RingHom.isIntegralOverIdeal_of_mem_map
