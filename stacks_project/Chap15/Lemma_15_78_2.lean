module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.ResidueField
import StacksCheckRecall

/-!
# Lemma 15.78.2 (068V)

@stack 068V

The residue-field Tor-amplitude criterion is owned by the derived-category perfectness leaf.
This Chapter file is its direct official-label recall.
-/

@[expose] public section

/- Lemma 15.78.2 (068V): perfect Tor-amplitude is detected on prime and maximal residue fields. -/
@[stacks 068V "Lemma 15.78.2"]
#check @CategoryTheory.perfect_torAmplitude_tfae_prime_and_maximal_residueField_homology_vanishing_of_isPseudoCoherent

#check @CategoryTheory.DerivedCategory.PrimeResidueField.homology

#print axioms CategoryTheory.perfect_torAmplitude_tfae_prime_and_maximal_residueField_homology_vanishing_of_isPseudoCoherent
