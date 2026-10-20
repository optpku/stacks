/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.BaseChange
import StacksCheckRecall

/-!
# Base change for the extended alternating Cech complex

@stack 0G6I
-/

@[expose] public section

/- Lemma 15.29.3: for a ring map `R → S`, the extended alternating Cech complex of
`S ⊗[R] M` for the image family is the scalar extension of the source complex. -/
@[stacks 0G6I "Lemma 15.29.3"]
#check @LocalizedModule.Away.Cech.Alternating.BaseChange.extendedIso

#check @LocalizedModule.Away.Cech.Alternating.BaseChange.ringExtendedIso
#check @LocalizedModule.Away.Cech.Alternating.BaseChange.tensorReassociationIso
#check @LocalizedModule.Away.Cech.Alternating.BaseChange.familyLinearEquiv
