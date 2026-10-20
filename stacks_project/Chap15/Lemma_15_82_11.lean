/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Localization
import StacksCheckRecall

/-!
# Lemma 15.82.11 (0679)

@stack 0679
-/

@[expose] public section

/- Lemma 15.82.11 (1): localization from a localized finite-type base preserves relative
`m`-pseudo-coherence over the original base. -/
@[stacks 0679 "(1), localization from a localized base"]
#check @CategoryTheory.DerivedCategory.IsMPseudoCoherentRelativeTo.localizationAway_from_localizedBase

/- Lemma 15.82.11 (2): localization from a localized finite-type base preserves relative
pseudo-coherence over the original base. -/
@[stacks 0679 "(2), localization from a localized base"]
#check @CategoryTheory.DerivedCategory.IsPseudoCoherentRelativeTo.localizationAway_from_localizedBase
