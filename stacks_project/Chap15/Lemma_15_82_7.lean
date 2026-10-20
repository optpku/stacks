module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Module
import StacksCheckRecall

/-!
# Lemma 15.82.7 (0675)

@stack 0675
-/

@[expose] public section

/- Lemma 15.82.7 (1): relative `0`-pseudo-coherence is finite generation. -/
@[stacks 0675 "(1), finite module criterion"]
#check @CategoryTheory.Module.IsMPseudoCoherentRelativeTo.zero_iff_finite

/- Lemma 15.82.7 (2): relative `(-1)`-pseudo-coherence is relative finite presentation. -/
@[stacks 0675 "(2), finite presentation criterion"]
#check @CategoryTheory.Module.IsMPseudoCoherentRelativeTo.minusOne_iff_finitePresentationRelativeTo

/- Lemma 15.82.7 (3): relative `(-d)`-pseudo-coherence is the finite-length resolution
criterion. -/
@[stacks 0675 "(3), finite free resolution criterion"]
#check @CategoryTheory.Module.IsMPseudoCoherentRelativeTo.neg_iff_hasLengthFiniteFreeResolutionRelativeTo

/- Lemma 15.82.7 (4): relative pseudo-coherence is the infinite finite-free resolution
criterion. -/
@[stacks 0675 "(4), infinite finite free resolution criterion"]
#check @CategoryTheory.Module.IsPseudoCoherentRelativeTo.iff_hasFiniteFreeResolutionRelativeTo
