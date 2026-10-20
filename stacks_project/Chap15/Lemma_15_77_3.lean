module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.LocalizationAwayThreeTermSplit
import StacksCheckRecall

/-!
# Lemma 15.77.3 (0A1V)

@stack 0A1V

The adjacent-degree three-term localization theorem is owned by the pseudo-coherent
derived-category leaf.  This Chapter file is its direct official-label recall.
-/

@[expose] public section

/- Lemma 15.77.3 (0A1V): two adjacent surjective residue-field homology comparisons give a
localized finite-free middle term and a three-term splitting with perfect upper tail. -/
@[stacks 0A1V "Lemma 15.77.3, three-term local splitting"]
#check @CategoryTheory.exists_localizationAway_threeTermSplit_of_residueField_homology_surjective

#check @CategoryTheory.exists_localizationAway_split_of_residueField_homology_surjective
#check @CategoryTheory.ModuleCat.derivedExtensionHomologyComparison

#print axioms
  CategoryTheory.exists_localizationAway_threeTermSplit_of_residueField_homology_surjective
