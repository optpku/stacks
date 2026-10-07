module

public import ReasLib.Algebra.Homology.DerivedCategory.ProjectiveAmplitude.Splitting
import StacksCheckRecall

/-!
# Lemma 15.77.1 (0BCG)

@stack 0BCG

The three projective-amplitude splitting clauses are owned by ReasLib.  This Chapter file is the
official source-label recall.
-/

@[expose] public section

@[stacks 0BCG "Lemma 15.77.1 (1), projective-amplitude Hom vanishing"]
#check @CategoryTheory.hom_eq_zero_of_projectiveAmplitude_of_homology_vanishing_ge

@[stacks 0BCG "Lemma 15.77.1 (2), distinguished-triangle splitting"]
#check
  @CategoryTheory.exists_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge_succ

@[stacks 0BCG "Lemma 15.77.1 (3), unique distinguished-triangle splitting"]
#check
  @CategoryTheory.existsUnique_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge

#print axioms CategoryTheory.hom_eq_zero_of_projectiveAmplitude_of_homology_vanishing_ge
#print axioms
  CategoryTheory.existsUnique_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge
