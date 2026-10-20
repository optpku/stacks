/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.LiftingProperty.ChosenLift
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Splittings selected by lifting properties

Lifting against an initial morphism selects a section, while lifting against a terminal
morphism selects a retraction. The resulting `SplitEpi` and `SplitMono` retain the chosen map
instead of discarding it behind the proposition-valued `IsSplitEpi` and `IsSplitMono` classes.
-/

@[expose] public section

universe v u

namespace CategoryTheory.HasLiftingProperty

open Limits

variable {C : Type u} [Category.{v} C]
variable {A B X Y : C} {i : A ⟶ B} {p : X ⟶ Y}

set_option linter.defProp false in
/-- The canonical lifting square from the initial morphism to `Y` against `p`. Its diagonal is
a section of `p`. It is deliberately a definition so dependent chosen-lift data does not acquire
an opaque theorem dependency. -/
@[stacks 08NL "initial lifting square"]
def initialSq [HasInitial C] (p : X ⟶ Y) :
    CommSq (initial.to X) (initial.to Y) p (𝟙 Y) := {}

set_option linter.defProp false in
/-- The canonical lifting square from `i` against the terminal morphism from `A`. Its diagonal
is a retraction of `i`. It is deliberately a definition so dependent chosen-lift data does not
acquire an opaque theorem dependency. -/
@[stacks 08NL "terminal lifting square"]
def terminalSq [HasTerminal C] (i : A ⟶ B) :
    CommSq (𝟙 A) i (terminal.from A) (terminal.from B) := {}

/-- A lifting property against the initial morphism to the target selects a split-epimorphism
structure whose section is the chosen diagonal. -/
@[stacks 08NL "split epimorphism selected by an initial lifting property"]
noncomputable def splitEpi [HasInitial C]
    (h : HasLiftingProperty (initial.to Y) p) : SplitEpi p where
  section_ := (h.liftStruct (initialSq p)).l
  id := (h.liftStruct (initialSq p)).fac_right

/-- A lifting property against the terminal morphism from the source selects a split-monomorphism
structure whose retraction is the chosen diagonal. -/
@[stacks 08NL "split monomorphism selected by a terminal lifting property"]
noncomputable def splitMono [HasTerminal C]
    (h : HasLiftingProperty i (terminal.from A)) : SplitMono i where
  retraction := (h.liftStruct (terminalSq i)).l
  id := (h.liftStruct (terminalSq i)).fac_left

end CategoryTheory.HasLiftingProperty
