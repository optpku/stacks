/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Localization
import StacksCheckRecall

/-!
# Lemma 15.82.16 (067E)

@stack 067E
-/

@[expose] public section

/- Lemma 15.82.16 (1): relative `m`-pseudo-coherence is detected on a finite principal-open
cover. -/
@[stacks 067E "(1), relative m-pseudo-coherence on a principal-open cover"]
#check @CategoryTheory.DerivedCategory.IsMPseudoCoherentRelativeTo.localizationAway_unitIdeal_iff

/- Lemma 15.82.16 (2): relative pseudo-coherence is detected on a finite principal-open cover. -/
@[stacks 067E "(2), relative pseudo-coherence on a principal-open cover"]
#check @CategoryTheory.DerivedCategory.IsPseudoCoherentRelativeTo.localizationAway_unitIdeal_iff
