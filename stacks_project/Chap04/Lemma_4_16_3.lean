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

/- The source asks for preservation of the colimit of every connected diagram in `Under X`.
`Under.preservesColimitsOfShape_forget_of_isConnected` is the exact shape-level owner: unlike
`Under.createsColimitsOfShapeForgetOfIsConnected`, it has the source's direction, and unlike the
dual `Over.preservesLimitsOfShape_forget_of_isConnected`, it needs no opposites bridge. Its
per-diagram instance exposes the mapped colimit cocone directly for downstream use. -/

/- Lemma 4.16.3: for a connected category `J`, the forgetful functor `Under.forget X` preserves
every `J`-shaped colimit, so whenever `M : J ⥤ Under X` has a colimit, its underlying diagram in
the base category has the same colimit. -/
@[stacks 04AR "connected colimits in an under category are preserved by the forgetful functor"]
#check (Under.preservesColimitsOfShape_forget_of_isConnected (J := J) (B := X) :
  PreservesColimitsOfShape J (Under.forget X))

end CategoryTheory
