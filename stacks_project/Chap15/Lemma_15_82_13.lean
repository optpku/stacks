/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Tensor
import StacksCheckRecall

/-!
# Lemma 15.82.13 (067B)

@stack 067B
-/

@[expose] public section

/- Lemma 15.82.13 (1): derived extension along a pseudo-coherent ring map preserves relative
`m`-pseudo-coherence over the base. -/
@[stacks 067B "(1), derived extension preserves relative m-pseudo-coherence"]
#check @CategoryTheory.DerivedCategory.IsMPseudoCoherentRelativeTo.extension_of_isPseudoCoherentRingMap

/- Lemma 15.82.13 (2): derived extension along a pseudo-coherent ring map preserves relative
pseudo-coherence over the base. -/
@[stacks 067B "(2), derived extension preserves relative pseudo-coherence"]
#check @CategoryTheory.DerivedCategory.IsPseudoCoherentRelativeTo.extension_of_isPseudoCoherentRingMap
