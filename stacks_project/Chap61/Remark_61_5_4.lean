/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap61.Remark_61_5_4_Cardinality
import StacksCheckRecall

@[expose] public section

open Algebra.WLocalHull

/- Remark 61.5.4: if `A` is a ring and `κ` is an infinite cardinal with `#A ≤ κ`,
then `#(wLocalization A) ≤ κ`. Namely each `stage A E` has cardinality at most
`κ` and `#(Finset A) ≤ κ` as well, using `κ * κ = κ`. -/
@[stacks 0976] #check cardinalMk_le
