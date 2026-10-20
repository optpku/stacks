/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaf.InverseLimit.FinitePresentation
import StacksCheckRecall

@[expose] public section

/- Lemma 17.19.3 (0CAK): a sheaf with a finite compact-open presentation on a spectral space
descends to a finite-stalk sheaf on a finite sober space along a spectral map. -/
@[stacks 0CAK]
#check @TopCat.Sheaf.CompactOpenPresentation.IsFinite.existsFiniteSoberModel
