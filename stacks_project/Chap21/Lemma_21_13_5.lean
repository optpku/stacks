module

public import ReasLib.CategoryTheory.Sites.Cech.TotalAcyclic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.13.5

The reusable criterion and all constructions of its extended Cech complex live in ReasLib.
This chapter entry only recalls the source-facing theorem and its generic infrastructure.
-/

open CategoryTheory CategoryTheory.Limits

/- Lemma 21.13.5 (07A1): an abelian sheaf is totally acyclic exactly when its positive
objectwise cohomology vanishes and every locally surjective arrow gives an acyclic extended
Cech complex on represented degree-zero sections. -/
@[stacks 07A1 "total acyclicity and extended Cech exactness"]
#check @CategoryTheory.Sheaf.IsTotallyAcyclic.iff_objectwise_and_cech

#check @CategoryTheory.Sheaf.IsTotallyAcyclic
#check @CategoryTheory.Sheaf.Cech.sectionsFunctor
#check @CategoryTheory.Sheaf.Cech.sectionsEquivH0
#check @CategoryTheory.Sheaf.Cech.sectionsIsoH0
#check @CategoryTheory.Sheaf.Cech.complex
#check @CategoryTheory.Sheaf.Cech.extended

#check @CategoryTheory.Arrow.Cech.augmented
#check @CategoryTheory.Arrow.Cech.complex
#check @CategoryTheory.Arrow.Cech.extended

#check @AlgebraicTopology.AlternatingCofaceMapComplex.coaugmentationApp
#check @AlgebraicTopology.AlternatingCofaceMapComplex.extended
#check @HomologicalComplex.acyclic_iff_forall_isZero_homology
