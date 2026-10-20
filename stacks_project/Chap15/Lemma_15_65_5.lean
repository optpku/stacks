/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Models
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.65.5

Pseudo-coherent cochain complexes are characterized by all integer pseudo-coherence bounds and
by bounded-above finite-projective models.  The same owner supplies the finite-free refinement
with a prescribed homology cutoff.

@stack 064U
-/

/- Lemma 15.65.5: the three equivalent pseudo-coherence conditions. -/
@[stacks 064U "Lemma 15.65.5: pseudo-coherent complex criterion"]
#check @CategoryTheory.CochainComplex.IsPseudoCoherent.tfae

#check @CategoryTheory.CochainComplex.IsPseudoCoherent

/- Lemma 15.65.5: bounded-above finite-free refinement under a homology cutoff. -/
@[stacks 064U "Lemma 15.65.5: bounded-above finite-free model"]
#check @CategoryTheory.CochainComplex.IsPseudoCoherent.exists_boundedAbove_finiteFree

end
