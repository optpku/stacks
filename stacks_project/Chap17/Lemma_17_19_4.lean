/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaf.Constructible.FinitePresentation
import StacksCheckRecall

@[expose] public section

/- Lemma 17.19.4 (0CAL): a sheaf with a finite compact-open presentation embeds into a finite
product of constructible closed pushforwards of finite constant sheaves. -/
@[stacks 0CAL]
#check @TopCat.Sheaf.CompactOpenPresentation.IsFinite.existsConstructibleEmbedding
