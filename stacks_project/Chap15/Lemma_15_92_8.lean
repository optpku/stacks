module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.PseudoCoherent
import StacksCheckRecall

/-!
# Lemma 15.92.8: pseudo-coherent objects are derived complete

@stack 0A05

The proof uses the weak-Serre/cohomology-in infrastructure from the 091U owner.  Chap15 exposes
only the source-facing implication; the reusable statement lives in ReasLib.
-/

@[expose] public section

/- Lemma 15.92.8 (Stacks `0A05`): derived completeness of `A[0]` implies derived completeness of
every pseudo-coherent object of `D(A)`. -/
@[stacks 0A05 "pseudo-coherent objects inherit derived completeness"]
#check @CategoryTheory.DerivedCategory.IsPseudoCoherent.isDerivedComplete

end
