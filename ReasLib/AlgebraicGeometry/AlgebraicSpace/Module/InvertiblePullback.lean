/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import ReasLib.CategoryTheory.Monoidal.Invertible

@[expose] public section
open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The explicit geometric inverse image followed by tensor extension preserves
invertible modules: pull back the local rank-one trivializations. This is a
property of the specified functor, not a producer of a chosen module. -/
theorem isInvertibleObject_pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (i : X ⟶ Y) (M : Y.Modules) [isInvertibleObject M] :
    isInvertibleObject ((pullback i).obj M) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
