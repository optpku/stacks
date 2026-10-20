/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
import StacksCheckRecall

/-!
# Definition 15.65.1

The reusable pseudo-coherence API is owned by
`ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent`.

@stack 064Q
-/

@[expose] public section

/- Definition 15.65.1 (1), tag `064Q`: `m`-pseudo-coherent derived objects. -/
@[stacks 064Q "(1), m-pseudo-coherent derived object"]
#check @CategoryTheory.DerivedCategory.IsMPseudoCoherent

/- Definition 15.65.1 (2), tag `064Q`: pseudo-coherent derived objects. -/
@[stacks 064Q "(2), pseudo-coherent derived object"]
#check @CategoryTheory.DerivedCategory.IsPseudoCoherent

/- Definition 15.65.1 (3), tag `064Q`: `m`-pseudo-coherent modules. -/
@[stacks 064Q "(3), m-pseudo-coherent module"]
#check @CategoryTheory.ModuleCat.IsMPseudoCoherent

/- Definition 15.65.1 (4), tag `064Q`: pseudo-coherent modules. -/
@[stacks 064Q "(4), pseudo-coherent module"]
#check @CategoryTheory.ModuleCat.IsPseudoCoherent
