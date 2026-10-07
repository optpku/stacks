module

public import ReasLib.Algebra.Homology.DerivedCategory.ResidueField.MinimalFreeModel
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.76.6 (0BCC)

@stack 0BCC

The reusable residue-field homology and minimal-free-model API lives in
`CategoryTheory.DerivedCategory.ResidueField`.
-/

@[stacks 0BCC "Derived residue-field homology"]
#check @CategoryTheory.DerivedCategory.ResidueField.homology

@[stacks 0BCC "Lemma 15.76.6 (1)"]
#check @CategoryTheory.DerivedCategory.ResidueField.finiteDimensional_and_eventually_isZero

@[stacks 0BCC "Lemma 15.76.6 (2)"]
#check @CategoryTheory.DerivedCategory.ResidueField.existsBoundedAboveFreeModel

@[stacks 0BCC "Lemma 15.76.6 (3)"]
#check @CategoryTheory.DerivedCategory.ResidueField.boundedAboveFreeModel_unique

#print axioms CategoryTheory.DerivedCategory.ResidueField.homology
