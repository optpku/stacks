/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Tame
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.115.8

The repository path retains the legacy numbering.  The current Stacks entry is Lemma 15.116.8,
tag `0EXX`.  The canonical tame normal-closure and common-overfield owners live in
`DVR.Field.IsTamelyRamified`; this file is a thin source-facing recall.

@stack 0EXX
-/

/- Lemma 15.115.8 (canonical normal-closure bridge). -/
@[stacks 0EXX "Lemma 15.115.8: tame normal closure"]
#check @DVR.Field.IsTamelyRamified.normalClosure

/- Lemma 15.115.8 (1): finite Galois tame overfield. -/
@[stacks 0EXX "Lemma 15.115.8 (1): finite Galois tame overfield"]
#check @DVR.Field.IsTamelyRamified.existsGaloisExtension

/- Lemma 15.115.8 (2): common finite separable tame overfield. -/
@[stacks 0EXX "Lemma 15.115.8 (2): common finite separable tame overfield"]
#check @DVR.Field.IsTamelyRamified.existsCommonExtension
