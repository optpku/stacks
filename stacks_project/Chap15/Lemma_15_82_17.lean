/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Noetherian
import StacksCheckRecall

/-!
# Lemma 15.82.17

@stack 067F
-/

@[expose] public section

/-!
# Lemma 15.82.17 compatibility entry point

The Noetherian bounded-above, finite-cohomology, and finite-module criteria
for relative pseudo-coherence are owned by
`ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Noetherian`.
-/

/- Lemma 15.82.17 (1), tag `067F`: the Noetherian relative `m`-pseudo-coherence criterion. -/
@[stacks 067F "(1), Noetherian relative m-pseudo-coherence"]
#check @CategoryTheory.DerivedCategory.isMPseudoCoherentRelativeTo_iff_boundedAbove_and_homology_finite_ge

/- Lemma 15.82.17 (2), tag `067F`: the Noetherian relative pseudo-coherence criterion. -/
@[stacks 067F "(2), Noetherian relative pseudo-coherence"]
#check @CategoryTheory.DerivedCategory.isPseudoCoherentRelativeTo_iff_boundedAbove_and_homology_finite

/- Lemma 15.82.17 (3), tag `067F`: the finite-module specialization. -/
@[stacks 067F "(3), Noetherian relative pseudo-coherent module"]
#check @Module.isPseudoCoherentRelativeTo_iff_finite
