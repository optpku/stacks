/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Compactness.LocallyCompact
import StacksCheckRecall

@[expose] public section

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]

/- Lemma 5.13.2: for a Hausdorff space, local quasi-compactness is equivalent
to every point having a quasi-compact neighborhood. -/
@[stacks 08ZR]
#check locallyCompactSpace_iff_weaklyLocallyCompactSpace (X := X)
