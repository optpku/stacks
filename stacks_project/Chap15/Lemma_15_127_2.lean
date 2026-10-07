module

public import ReasLib.Algebra.Homology.CochainComplex.Subobject.FiniteFree
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.127.2 (0FNR)

@stack 0FNR

The finite-free subcomplex existence theorem is owned by ReasLib on the canonical `Subobject F`
surface.
-/

/- Lemma 15.127.2: a bounded-above free complex contains a finite family of specified elements in
a bounded finite-free subcomplex. -/
@[stacks 0FNR "Lemma 15.127.2 finite free subcomplex"]
#check @CochainComplex.exists_boundedFiniteFree_subobject_containing

#check @HomologicalComplex.IsTermwiseFiniteFree
