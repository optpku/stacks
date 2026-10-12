/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.NumericalType.Diagonal

/- Lemma 55.3.6: if a numerical type has more than one index, then every
diagonal entry of its intersection matrix is strictly negative. -/
@[stacks 0C74] #check (NumericalType.diagonal_neg : ∀ (T : NumericalType)
  (hn : 1 < T.n) (i : Fin T.n), T.intersection i i < 0)
