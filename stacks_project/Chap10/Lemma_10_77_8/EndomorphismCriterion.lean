/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.QuotientByIdeal.Endomorphism
import StacksCheckRecall

/-!
# Lemma 10.77.8 endomorphism criteria

The reusable owners are in `LinearMap`: arbitrary submodules belong to `Quotient.Endomorphism`,
while ideal multiples belong to `QuotientByIdeal.Endomorphism`. This chapter leaf only records the
recall surface and keeps no parallel proof implementation.
-/

@[expose] public section

/- Lemma 10.77.8 (0H7M): endomorphisms detected on a submodule quotient. -/
@[stacks 0H7M] #check @LinearMap.bijective_of_id_on_submodule_quotient
@[stacks 0H7M] #check @LinearMap.eq_on_of_id_on_quotient
@[stacks 0H7M] #check @LinearMap.eq_on_smul_top_of_mul_eq_bot
@[stacks 0H7M] #check @LinearMap.eq_on_smul_top_of_inf_eq_bot
