module

public import ReasLib.RingTheory.Valuation.Extension.Finite
import StacksCheckRecall

/-!
# Lemma 15.124.2

@stack 0ASH

The residue-field finiteness, value-group index finiteness, and degree inequality are owned by
the shared valuation-extension leaf.
-/

@[expose] public section

/- Lemma 15.124.2 (1): the residue-field extension is finite. -/
@[stacks 0ASH "Lemma 15.124.2 (1)"]
#check @IsExtensionOfValuationRings.finiteDimensional_residueField

/- Lemma 15.124.2 (2): the value-group index is finite. -/
@[stacks 0ASH "Lemma 15.124.2 (2)"]
#check @IsExtensionOfValuationRings.ramificationIndex_ne_top

/- Lemma 15.124.2 (3): the value-group index times residue degree is at most the fraction-field
degree. -/
@[stacks 0ASH "Lemma 15.124.2 (3)"]
#check @IsExtensionOfValuationRings.ramificationIndex_mul_residueDegree_le_finrank
