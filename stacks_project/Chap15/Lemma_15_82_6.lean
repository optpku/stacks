/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Triangulated
import StacksCheckRecall

/-!
# Lemma 15.82.6 (0674)

@stack 0674
-/

@[expose] public section

/- Lemma 15.82.6 (1): relative `m`-pseudo-coherence at the third vertex. -/
@[stacks 0674 "(1), third vertex"]
#check @CategoryTheory.DerivedCategory.IsMPseudoCoherentRelativeTo.obj₃

/- Lemma 15.82.6 (2): relative `m`-pseudo-coherence at the middle vertex. -/
@[stacks 0674 "(2), middle vertex"]
#check @CategoryTheory.DerivedCategory.IsMPseudoCoherentRelativeTo.obj₂

/- Lemma 15.82.6 (3): relative `m`-pseudo-coherence at the first vertex. -/
@[stacks 0674 "(3), first vertex"]
#check @CategoryTheory.DerivedCategory.IsMPseudoCoherentRelativeTo.obj₁

/- Lemma 15.82.6 (4): relative pseudo-coherence at the third vertex. -/
@[stacks 0674 "(4), third vertex"]
#check @CategoryTheory.DerivedCategory.IsPseudoCoherentRelativeTo.obj₃

/- Lemma 15.82.6 (5): relative pseudo-coherence at the middle vertex. -/
@[stacks 0674 "(5), middle vertex"]
#check @CategoryTheory.DerivedCategory.IsPseudoCoherentRelativeTo.obj₂

/- Lemma 15.82.6 (6): relative pseudo-coherence at the first vertex. -/
@[stacks 0674 "(6), first vertex"]
#check @CategoryTheory.DerivedCategory.IsPseudoCoherentRelativeTo.obj₁
