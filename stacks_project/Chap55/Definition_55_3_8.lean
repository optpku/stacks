/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.NumericalType.MinusOneIndex

/- Definition 55.3.8: For a numerical type `T`, an index `i` is a `(-1)`-index when
`T.componentGenus i = 0` and `T.intersection i i = -(T.weight i : ℤ)`. -/
@[stacks 0C76] #check (NumericalType.IsMinusOneIndex :
  ∀ {n : ℕ}, (Fin n → ℕ) → (Fin n → ℕ) → Matrix (Fin n) (Fin n) ℤ → Fin n → Prop)
