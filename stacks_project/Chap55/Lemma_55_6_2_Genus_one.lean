module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.GenusOneClassification

/- Lemma 55.6.2 (Genus one) -/
@[stacks 0C8T] #check (NumericalType.genusOneClassification :
  ∀ T : NumericalType, T.IsMinimal ∧ T.genus = 1 ↔ T.IsGenusOneConfiguration)
