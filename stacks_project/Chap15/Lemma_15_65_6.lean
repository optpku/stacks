module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Triangulated
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.65.6

Pseudo-coherence is detected by all integer pseudo-coherence bounds and satisfies the
two-out-of-three property in distinguished triangles.

@stack 064V
-/

/- Lemma 15.65.6: pseudo-coherence is detected degreewise. -/
@[stacks 064V "Lemma 15.65.6: degreewise criterion"]
#check @CategoryTheory.DerivedCategory.IsPseudoCoherent.iff_forall_isMPseudoCoherent

/- Lemma 15.65.6 (1): the third vertex is pseudo-coherent when the first two are. -/
@[stacks 064V "Lemma 15.65.6 (1)"]
#check @CategoryTheory.DerivedCategory.IsPseudoCoherent.obj₃

/- Lemma 15.65.6 (2): the middle vertex is pseudo-coherent when the first and third are. -/
@[stacks 064V "Lemma 15.65.6 (2)"]
#check @CategoryTheory.DerivedCategory.IsPseudoCoherent.obj₂

/- Lemma 15.65.6 (3): the first vertex is pseudo-coherent when the middle and third are. -/
@[stacks 064V "Lemma 15.65.6 (3)"]
#check @CategoryTheory.DerivedCategory.IsPseudoCoherent.obj₁

end
