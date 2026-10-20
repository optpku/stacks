/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Jacobson.ZariskiPair.FlatIntegral
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.10.3

The Zariski-pair bijectivity theorem is owned by ReasLib.

@stack 0ELZ
-/

/- Lemma 15.10.3: a flat integral finitely presented algebra over a Zariski pair is determined by
its reduction modulo the distinguished ideal. -/
@[stacks 0ELZ "Lemma 15.10.3"]
#check @Algebra.bijective_algebraMap_of_zariskiPair
