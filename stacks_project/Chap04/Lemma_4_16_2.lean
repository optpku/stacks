/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import StacksCheckRecall

@[expose] public section


namespace CategoryTheory

open Limits

universe vJ uJ vC uC

variable {J : Type uJ} [Category.{vJ} J] [IsConnected J]
variable {C : Type uC} [Category.{vC} C]
variable (X : C)

/- The source quantifies over every `M : J ⥤ Over X`, so
`PreservesLimitsOfShape J (Over.forget X)` is the exact canonical owner.
`PreservesLimit` is only its per-diagram projection, while `CreatesLimitsOfShape` concerns lifting
base-category limits into `Over X`. Recalling the shape-level owner introduces no generalization
and exposes both mapped limiting cones and the induced `HasLimit` instance downstream. -/

/- Lemma 4.16.2: for a connected category `J`, the forgetful functor `Over.forget X` preserves
every `J`-shaped limit, so the underlying cone of any limit of `M : J ⥤ Over X` is a limit of
`M ⋙ Over.forget X` in the base category. -/
@[stacks 002T "connected limits in an over category are preserved by the forgetful functor"]
#check (Over.preservesLimitsOfShape_forget_of_isConnected (J := J) (B := X) :
  PreservesLimitsOfShape J (Over.forget X))

end CategoryTheory
