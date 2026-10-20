/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.FormallyEtale
import StacksCheckRecall

/-!
# Formal etaleness of henselizations

Lemma 15.45.2 states that the henselization map, the strict-henselization map over a
henselization, and the composite strict-henselization map are formally etale and formally smooth
for the corresponding maximal-ideal-adic topologies. The generic strict-henselization owners below
specialize to both strict maps.

@stack 07QN
-/

@[expose] public section

@[stacks 07QN "Lemma 15.45.2 (1)"]
#check @IsHenselizationOf.formallyEtale

@[stacks 07QN "Lemma 15.45.2 (2)"]
#check @IsStrictHenselizationOf.formallyEtale

@[stacks 07QN "Lemma 15.45.2 (3)"]
#check @IsStrictHenselizationOf.formallyEtale

@[stacks 07QN "Lemma 15.45.2 (4)"]
#check @IsHenselizationOf.formallySmoothForMaximalIdeal

@[stacks 07QN "Lemma 15.45.2 (5)"]
#check @IsStrictHenselizationOf.formallySmoothForMaximalIdeal

@[stacks 07QN "Lemma 15.45.2 (6)"]
#check @IsStrictHenselizationOf.formallySmoothForMaximalIdeal
