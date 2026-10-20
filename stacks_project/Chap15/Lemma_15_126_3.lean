/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RegularLocalRing.Parameters.Perturbation
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.126.3

@stack 0BWU

The source entry recalls the positive-tail specialization.  The same leaf also
exposes the dimension-one-compatible core without changing the tagged source
assumptions.
-/

/- Lemma 15.126.3: complete the distinguished element by parameters in a prescribed power. -/
@[stacks 0BWU "Lemma 15.126.3, completion to parameters in a maximal-ideal power"]
#check @IsLocalRing.IsSystemOfParameters.exists_cons_mem_maximalIdeal_pow_of_pos

#check @IsLocalRing.IsSystemOfParameters.exists_cons_mem_maximalIdeal_pow
