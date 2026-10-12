/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Presentable.Finite
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
variable (X : C)

/- Stacks asks that `Hom(X, -)` preserve every existing filtered colimit. This is exactly
`IsFinitelyPresentable X`: at the source category's morphism universe,
`isFinitelyPresentable_iff_preservesFilteredColimits` identifies the owner with
`PreservesFilteredColimits (coyoneda.obj (op X))`. The latter quantifies over filtered diagrams
without assuming that their colimits all exist; it only sends a colimit cocone to a colimit
cocone when one is supplied. Hence no local `CategoricallyCompact` alias or stronger ambient
`HasFilteredColimits` hypothesis is appropriate. -/

/- Definition 4.26.1: categorical compactness is the canonical owner predicate
`IsFinitelyPresentable`. -/
@[stacks 0FWX "categorically compact objects as finitely presentable objects"]
#check (IsFinitelyPresentable X : Prop)

/- Companion recall: the textbook formulation via preservation of filtered colimits by `Hom(X, -)`
is the canonical theorem `isFinitelyPresentable_iff_preservesFilteredColimits`. -/
#check isFinitelyPresentable_iff_preservesFilteredColimits

end CategoryTheory
