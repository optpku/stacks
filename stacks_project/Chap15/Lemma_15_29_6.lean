/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Koszul
import StacksCheckRecall

/-!
# The extended Cech complex as a powered Koszul colimit

@stack 0913
-/

@[expose] public section

/- Lemma 15.29.6: the ring-valued extended alternating Cech complex is the colimit of the powered
Koszul cochain system. -/
@[stacks 0913 "Lemma 15.29.6"]
#check @LocalizedModule.Away.Cech.Koszul.extendedIso

#check @LocalizedModule.Away.Cech.Koszul.stage
#check @LocalizedModule.Away.Cech.Koszul.step
#check @LocalizedModule.Away.Cech.Koszul.system
#check @LocalizedModule.Away.Cech.Koszul.cocone
#check @LocalizedModule.Away.Cech.Koszul.colimitComparison
