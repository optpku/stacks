/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent.Pullback
import StacksCheckRecall

@[expose] public section

/- Lemma 21.45.3 (08H4): derived pullback preserves `m`-pseudo-coherence. -/
@[stacks 08H4]
#check @RingedSite.Hom.ModuleDerived.IsMPseudoCoherent.pullback
