/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.EventualZero
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.Pro.Representative
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Zero values of sequential pro-presentations

For a sequential presentation, having pro-value the zero object is equivalent to eventual
vanishing of the transition maps.  The statement is presentation-level, so it belongs beside
`Pro.HasValue` and does not require additive or abelian structure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

universe v u

namespace CategoryTheory.Pro.HasValue

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]

/-- A sequential pro-presentation has value zero exactly when each stage is eventually killed by a
later transition map. -/
theorem zero_iff_eventuallyZeroTransitions (F : SequentialInverseSystem C) :
    Pro.HasValue F (0 : C) ↔ PreorderInverseSystem.Transition.EventuallyZero F := sorry

end CategoryTheory.Pro.HasValue
