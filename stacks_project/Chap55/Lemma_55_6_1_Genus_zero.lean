/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.GenusZeroClassification

/- Lemma 55.6.1 (Genus zero) -/
@[stacks 0C8S] #check (NumericalType.genusZeroClassification :
  ∀ (T : NumericalType), T.IsMinimal → T.genus = 0 →
    T.n = 1 ∧ ∀ i : Fin T.n,
      T.multiplicity i = 1 ∧ T.intersection i i = 0 ∧ T.weight i = 1 ∧
        T.componentGenus i = 0)
