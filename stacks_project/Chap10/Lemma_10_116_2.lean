module

public import ReasLib.RingTheory.KrullDimension.FiniteType.ResidueField.Order
import StacksCheckRecall

@[expose] public section

/-!
# Residue-Field Transcendence Degree Along Prime Inclusions

@stack 06RP
-/

/- Lemma 10.116.2 (Stacks tag `06RP`): strict inclusion of prime ideals in a
finite-type algebra over a field strictly lowers the transcendence degree of
the residue field. -/
@[stacks 06RP "cardinal form"]
#check @Algebra.FiniteType.trdeg_residueField_lt_of_lt_cardinal

@[stacks 06RP "natural-number form"]
#check @Algebra.FiniteType.trdeg_residueField_lt_of_lt

@[stacks 06RP "prime-spectrum order form"]
#check @PrimeSpectrum.trdeg_residueField_strictAnti
