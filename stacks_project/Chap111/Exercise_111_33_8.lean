/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap111.Exercise_111_33_8_AwayTwo
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.AwayTwo

/- Exercise 111.33.8: the morphism from the open subscheme `D(2) ⊆ Spec ℤ` to
`Spec (Localization.Away (2 : ℤ))` does not extend along the open-subscheme
inclusion to a morphism `Spec ℤ ⟶ Spec (Localization.Away (2 : ℤ))`. -/
@[stacks 028U] #check morphism_not_extends
