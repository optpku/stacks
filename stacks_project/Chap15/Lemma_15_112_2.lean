module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Finite
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.112.2

The repository path retains the legacy `15.112.2` name.  The source entry is the current Stacks
Lemma 15.113.2, tag `09E5`; its finite-residue and `e * f` statements are owned by the reusable
DVR-extension finite leaf.

@stack 09E5
-/

/- Lemma 15.112.2 (current Stacks Lemma 15.113.2), clause (1): a finite fraction-field extension
induces a finite residue-field extension. -/
@[stacks 09E5 "Lemma 15.112.2 (1): finite residue-field extension"]
#check @IsExtensionOfDiscreteValuationRings.finiteDimensional_residueField_of_finiteDimensional_fractionField_extension

/- Lemma 15.112.2 (current Stacks Lemma 15.113.2), clause (2): the ramification index times the
residue degree is bounded by the fraction-field degree. -/
@[stacks 09E5 "Lemma 15.112.2 (2): ramification index times residue degree"]
#check @IsExtensionOfDiscreteValuationRings.ramificationIndex_mul_residueDegree_le_finrank_of_finiteDimensional_fractionField_extension
