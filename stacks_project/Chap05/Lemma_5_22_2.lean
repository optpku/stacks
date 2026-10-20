/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Category.Profinite.AsLimit
public import ReasLib.Topology.Category.Profinite.Recognition
import StacksCheckRecall

@[expose] public section

/- Lemma 5.22.2: a space is profinite exactly under the canonical compact,
Hausdorff, totally disconnected recognition criterion. -/
@[stacks 08ZY "profinite recognition"]
#check Profinite.exists_homeomorph_iff_t2Space_compactSpace_totallyDisconnectedSpace

/- Lemma 5.22.2: every bundled profinite space has Mathlib's canonical
cofiltered finite-discrete limit presentation. -/
@[stacks 08ZY "finite-discrete limit presentation"]
#check Profinite.lim
