/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.NumericalType.GenusEquality
public import stacks_project.Chap55.Lemma_55_3_14

namespace NumericalType

/- Remark 55.3.17: a minimal numerical type with more than one index has genus equal
to its topological genus when all multiplicities and weights are one, all component
genera vanish, and every upper off-diagonal intersection is zero or one. -/
@[stacks 0C7F] #check (NumericalType.genus_eq_topologicalGenus :
  (T : NumericalType) → T.IsMinimal → 1 < T.n →
    (∀ i, T.multiplicity i = 1) → (∀ i, T.weight i = 1) →
    (∀ i, T.componentGenus i = 0) →
    (∀ i j, i < j → T.intersection i j ∈ ({0, 1} : Set ℤ)) →
    T.genus = (T.topologicalGenus : ℤ))

end NumericalType
