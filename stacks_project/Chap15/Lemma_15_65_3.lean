/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Cohomology
import StacksCheckRecall

/-!
# Finiteness of homology of pseudo-coherent complexes

Lemma 15.65.3 is exposed by the canonical cochain-complex API in ReasLib; the corresponding
derived-object statements remain available as companions.

@stack 064S
-/

@[expose] public section

/- Lemma 15.65.3 (1): the top surviving homology is finite. -/
@[stacks 064S "(1)"]
#check @CategoryTheory.CochainComplex.IsMPseudoCoherent.topHomology_finite

/- Lemma 15.65.3 (2): the next homology is finitely presented. -/
@[stacks 064S "(2)"]
#check @CategoryTheory.CochainComplex.IsMPseudoCoherent.nextHomology_finitePresentation

#check @CategoryTheory.DerivedCategory.IsMPseudoCoherent.topHomology_finite
#check @CategoryTheory.DerivedCategory.IsMPseudoCoherent.nextHomology_finitePresentation
