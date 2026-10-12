/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Lemma_94_12_4_Equivalence
import StacksCheckRecall

@[expose] public section

/- Lemma 94.12.4 (1): let `S` be a scheme contained in `Sch_fppf`, and let `X`,
`Y` be categories over `(Sch/S)_fppf`, formalized as objects of
`GroupoidsOver S` (via `FiberedCategoryOver.Groupoids.toBased`). If `X` and `Y`
are equivalent as categories over `(Sch/S)_fppf`, then `X` is an algebraic
stack if and only if `Y` is an algebraic stack. -/
@[stacks 03YQ]
#check @AlgebraicGeometry.AlgebraicStack.iff_of_equivalence

/- Lemma 94.12.4 (2): let `S` be a scheme contained in `Sch_fppf`, and let `X`,
`Y` be categories over `(Sch/S)_fppf`, formalized as objects of
`GroupoidsOver S` (via `FiberedCategoryOver.Groupoids.toBased`). If `X` and `Y`
are equivalent as categories over `(Sch/S)_fppf`, then `X` is a Deligne-Mumford
stack if and only if `Y` is a Deligne-Mumford stack. -/
@[stacks 03YQ]
#check @AlgebraicGeometry.DeligneMumfordStack.iff_of_equivalence
