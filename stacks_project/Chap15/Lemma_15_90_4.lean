/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.KoszulCechBaseChange
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.90.4 (091M)

@stack 091M
-/

/- Lemma 15.90.4 (1), Stacks `091M`: flat base change for the Koszul complex. -/
@[stacks 091M "Lemma 15.90.4 (1), flat base change for a Koszul complex"]
#check @KoszulComplex.baseChangeUnit_quasiIso_of_quotientMap_bijective

/- Lemma 15.90.4 (2), Stacks `091M`: flat base change for the extended alternating Cech
complex. -/
@[stacks 091M "Lemma 15.90.4 (2), flat base change for an extended alternating Cech complex"]
#check @LocalizedModule.Away.Cech.Alternating.extended_baseChangeUnit_quasiIso_of_quotientMap_bijective
