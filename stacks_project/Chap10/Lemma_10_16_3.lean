/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Module.End.CayleyHamilton

@[expose] public section

/-!
# Lemma 10.16.3

The source-oriented coefficient bridge is owned by
`ReasLib.Algebra.Module.End.CayleyHamilton`; the stronger Mathlib theorem is
recalled alongside it.

@stack 05G7
-/

@[stacks 05G7 "canonical finite-module Cayley-Hamilton theorem"]
#check @LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero

@[stacks 05G7 "source-order ideal-power coefficient bridge"]
#check @LinearMap.exists_monic_coeff_pow_of_range
