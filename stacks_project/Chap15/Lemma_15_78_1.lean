module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.ResidueField
import StacksCheckRecall

/-!
# Lemma 15.78.1 (0BYP)

@stack 0BYP

The prime-residue-field free-model theorem is owned by the derived-category perfectness leaf.
This Chapter file is its direct official-label recall.
-/

@[expose] public section

/- Lemma 15.78.1 (1) (0BYP): the localized finite-free model with prescribed fiber ranks. -/
@[stacks 0BYP "Lemma 15.78.1 (1)"]
#check @CategoryTheory.exists_away_termwiseFree_representative_of_primeResidueFieldDerivedHomology_of_isPseudoCoherent_of_isGE

/- Lemma 15.78.1 (2) (0BYP): the resulting localized perfectness. -/
@[stacks 0BYP "Lemma 15.78.1 (2)"]
#check @CategoryTheory.exists_away_isPerfect_of_primeResidueFieldDerivedHomology_vanishing_below

#check @CategoryTheory.DerivedCategory.PrimeResidueField.homology
#check @CategoryTheory.DerivedCategory.PrimeResidueField.AwayBoundedFiniteFree

#print axioms CategoryTheory.exists_away_termwiseFree_representative_of_primeResidueFieldDerivedHomology_of_isPseudoCoherent_of_isGE
