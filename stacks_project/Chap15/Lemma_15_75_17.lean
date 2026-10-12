/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Duality.HomotopyColimit
import StacksCheckRecall

/-!
# Lemma 15.75.17 (0BKB)

For a sequential homotopy colimit of perfect derived modules, `RHom` is represented by the
homotopy limit of the inverse system formed by tensoring with the stagewise derived duals.
The explicit tower and its source-facing homotopy-limit statement are owned by
`CategoryTheory.DerivedCategory.Perfect.Duality`.

@stack 0BKB
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.DerivedCategory.Perfect

namespace CategoryTheory.DerivedCategory.Perfect.Duality

@[stacks 0BKB "Lemma 15.75.17: tensor-dual inverse system"]
#check @dualTensorInverseSystem

@[stacks 0BKB "Lemma 15.75.17: RHom of a homotopy colimit"]
#check @rhom_isHomotopyLimit_of_homotopyColimit

end CategoryTheory.DerivedCategory.Perfect.Duality

end
