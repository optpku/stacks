/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Galois.KrullTopology.Tower
import StacksCheckRecall

@[expose] public section

/- Lemma 9.22.5 (Tag 0BMM): the inclusion and restriction maps in a Galois tower form a short
exact sequence of profinite topological groups. -/
@[stacks 0BMM]
#check FieldExtension.galoisTowerIsShortExact
