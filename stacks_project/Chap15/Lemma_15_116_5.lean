/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.RamificationElimination
import StacksCheckRecall

/-!
# Lemma 15.116.5

The reusable square and its existence theorem live in ReasLib.  This source-facing file is a
tagged recall block; its path retains the repository's legacy chapter numbering.

@stack 09ET
-/

@[expose] public section

/- Lemma 15.116.5: the chosen commutative square records its DVRs, fraction fields, residue-field
closures along the induced residue maps, and the three descent implications. -/
@[stacks 09ET "ramification-elimination square data"]
#check @DVR.RamificationElimination.Square

/- Lemma 15.116.5: every extension of DVRs admits such a ramification-elimination square
in the common universe of its input rings and fraction fields. -/
@[stacks 09ET "Lemma 15.116.5: ramification-elimination square"]
#check @DVR.RamificationElimination.exists_square
