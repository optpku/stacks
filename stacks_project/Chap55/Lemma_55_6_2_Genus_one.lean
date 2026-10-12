/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.GenusOneClassification

/- Lemma 55.6.2 (Genus one) -/
@[stacks 0C8T] #check (NumericalType.genusOneClassification :
  ∀ T : NumericalType, T.IsMinimal ∧ T.genus = 1 ↔ T.IsGenusOneConfiguration)
