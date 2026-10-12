/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Covering arrows of a Grothendieck topology

An arrow is covering when its singleton family generates a covering sieve.  Packaging this as a
`MorphismProperty` lets relative hypercovering and descent APIs use the ordinary Mathlib closure
interfaces.
-/

@[expose] public section

universe v u

namespace CategoryTheory.GrothendieckTopology

open Limits
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

/-- The morphism property of arrows whose singleton families cover for `J`. -/
@[stacks 0GM9 "singleton covering arrows"]
def coveringArrows (J : GrothendieckTopology C) : MorphismProperty C :=
  fun {_ Y} f ↦
    (SemiRepresentableFamily.OverFamily.singleton.{v, u, 0} f).toSieve ∈ J Y

/-- Membership in `J.coveringArrows` is the covering condition on the corresponding singleton
family. -/
@[simp] theorem mem_coveringArrows_iff (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y) :
    J.coveringArrows f ↔
      (SemiRepresentableFamily.OverFamily.singleton.{v, u, 0} f).toSieve ∈ J Y := sorry

/-- Covering arrows contain identities and are stable under composition. -/
instance instCoveringArrowsIsMultiplicative (J : GrothendieckTopology C) :
    J.coveringArrows.IsMultiplicative := sorry

/-- Covering arrows are stable under base change. -/
instance instCoveringArrowsIsStableUnderBaseChange (J : GrothendieckTopology C) :
    J.coveringArrows.IsStableUnderBaseChange := sorry

end CategoryTheory.GrothendieckTopology
