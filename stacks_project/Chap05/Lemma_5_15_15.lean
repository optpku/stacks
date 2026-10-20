/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.IrreducibleCloseds.FiniteLocallyClosed
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.15.15

Finite locally closed trace API is owned by
`ReasLib.Topology.IrreducibleCloseds.FiniteLocallyClosed`.
-/

/- Lemma 5.15.15 (1): dense traces contain open dense subtraces. -/
@[stacks 005K "open-dense trace criterion"]
#check @IsIrreducible.exists_open_dense_iff_dense_preimage_of_isFiniteUnionOfLocallyClosed

/- Lemma 5.15.15 (2): generic-point membership detects a dense finite locally closed trace. -/
@[stacks 005K "generic-point membership criterion"]
#check @IsGenericPoint.dense_preimage_iff_mem_of_isFiniteUnionOfLocallyClosed

/- Lemma 5.15.15 (2): source form with an explicit irreducibility hypothesis. -/
@[stacks 005K "generic-point membership criterion"]
#check @IsIrreducible.dense_preimage_iff_mem_of_isGenericPoint_of_isFiniteUnionOfLocallyClosed
