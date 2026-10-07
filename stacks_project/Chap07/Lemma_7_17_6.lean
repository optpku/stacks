module

public import ReasLib.CategoryTheory.Sites.QuasiCompact.Sheaf.Coproduct
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.17.6

The finite-coproduct closure API for quasi-compact sheaves is owned by
ReasLib; this Chapter 7 file preserves the source-facing recall.
-/

@[expose] public section

/- Lemma 7.17.6 (0GMQ): quasi-compact sheaf objects are closed under finite
coproducts. -/
@[stacks 0GMQ] #check @CategoryTheory.Sheaf.IsQuasiCompactObject.isClosedUnderFiniteCoproducts

#check @CategoryTheory.Sheaf.IsQuasiCompactObject.finiteCoproduct
#check @CategoryTheory.Sheaf.LocalSurjectivity.sigmaDesc_of_componentwise
#check @CategoryTheory.Sheaf.LocalSurjectivity.sigmaDesc_iff_presheaf
#check @CategoryTheory.Sheaf.LocalSurjectivity.sigmaDesc_pullbackSnd
#check @CategoryTheory.Sheaf.LocalSurjectivity.sigmaDesc_iff_presheaf_of_small
