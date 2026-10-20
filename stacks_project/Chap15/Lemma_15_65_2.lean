module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Triangulated
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.65.2

Pseudo-coherence bounds in a distinguished triangle are owned by the canonical
`DerivedCategory.IsMPseudoCoherent` API.

@stack 064R
-/

/- Lemma 15.65.2 (1): the third vertex has the indicated pseudo-coherence bound. -/
@[stacks 064R "Lemma 15.65.2 (1)"]
#check @CategoryTheory.DerivedCategory.IsMPseudoCoherent.obj₃

/- Lemma 15.65.2 (2): the middle vertex has the common pseudo-coherence bound. -/
@[stacks 064R "Lemma 15.65.2 (2)"]
#check @CategoryTheory.DerivedCategory.IsMPseudoCoherent.obj₂

/- Lemma 15.65.2 (3): the first vertex has the shifted pseudo-coherence bound. -/
@[stacks 064R "Lemma 15.65.2 (3)"]
#check @CategoryTheory.DerivedCategory.IsMPseudoCoherent.obj₁

#check @CategoryTheory.DerivedCategory.IsMPseudoCoherent.shift_iff
#check @CategoryTheory.DerivedCategory.IsMPseudoCoherent.isTriangulatedClosed₂
#check @CategoryTheory.DerivedCategory.IsMPseudoCoherent.ofIso

end
