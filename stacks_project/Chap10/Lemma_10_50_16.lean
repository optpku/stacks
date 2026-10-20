/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Valuation.UnitHom.ValuationSubring
import StacksCheckRecall

/-!
# Valuations from homomorphisms on units

@stack 00IG
-/

@[expose] public section

@[stacks 00IG "bundle the source unit homomorphism"]
#check @AddValuation.UnitHom.of

@[stacks 00IG "(1), induced valuation subring"]
#check @AddValuation.UnitHom.valuationSubring

@[stacks 00IG "(1), carrier description"]
#check @AddValuation.UnitHom.mem_valuationSubring_iff_eq_zero_or_nonneg

@[stacks 00IG "(2), exact value group"]
#check @AddValuation.UnitHom.exists_unit_value_eq

@[stacks 00IG "(3), maximal ideal"]
#check @AddValuation.UnitHom.mem_maximalIdeal_iff_eq_zero_or_pos

@[stacks 00IG "(4), unit group"]
#check @AddValuation.UnitHom.mem_unitGroup_iff_toAdd_eq_zero

@[stacks 00IG "(4), canonical kernel description"]
#check @AddValuation.UnitHom.mem_unitGroup_iff

@[stacks 00IG "(4), unit group as a kernel"]
#check @AddValuation.UnitHom.unitGroup_eq_ker
