module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.BoundedHomology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.65.10

For a bounded-above derived object, degreewise pseudo-coherence bounds on homology imply the
corresponding bound on the object; degreewise pseudo-coherent homology implies pseudo-coherence.

@stack 066B
-/

/- Lemma 15.65.10 (1): the bounded-above `m`-pseudo-coherence criterion. -/
@[stacks 066B "Lemma 15.65.10 (1)"]
#check @CategoryTheory.DerivedCategory.IsMPseudoCoherent.of_boundedAbove_homology

/- Lemma 15.65.10 (2): the bounded-above pseudo-coherence criterion. -/
@[stacks 066B "Lemma 15.65.10 (2)"]
#check @CategoryTheory.DerivedCategory.IsPseudoCoherent.of_boundedAbove_homology

end
