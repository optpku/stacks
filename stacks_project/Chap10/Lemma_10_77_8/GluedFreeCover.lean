/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Projective
public import ReasLib.LinearAlgebra.Quotient.Pair
public import ReasLib.LinearAlgebra.QuotientByIdeal.Endomorphism
import StacksCheckRecall

/-!
# Free-cover gluing support for Lemma 10.77.8

The source proof combines the generic paired-quotient range description with an endomorphism
criterion. This file is only a tagged recall surface.

@stack 0H7M
-/

@[expose] public section

@[stacks 0H7M "compatible quotient pair"]
#check @Submodule.Quotient.mem_range_pairMap_iff

@[stacks 0H7M "paired quotient equivalence"]
#check @Submodule.Quotient.compatiblePairsEquiv

@[stacks 0H7M "identity on ideal multiples"]
#check @LinearMap.eq_on_smul_top_of_inf_eq_bot

@[stacks 0H7M "endomorphism criterion"]
#check @LinearMap.bijective_of_id_on_submodule_quotient

@[stacks 0H7M "split free cover gives projectivity"]
#check @Module.Projective.of_split
