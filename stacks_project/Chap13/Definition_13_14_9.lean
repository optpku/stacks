/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Definition 13.14.9 (05SV)

The source's everywhere-defined condition requires source-definedness at every
object. Its weak pointwise Kan-extension consequences are recalled separately.
-/

open CategoryTheory

universe v₁ v₂ u₁ u₂

section

variable {D : Type u₁} {D' : Type u₂} [Category.{v₁} D] [Category.{v₂} D']

/- Definition 13.14.9 (1). In Situation 13.14.1, F is right derivable, or RF is
everywhere defined, if RightDerived.DefinedAt F S X holds for every X : D. -/
@[stacks 05SV]
#check (CategoryTheory.Functor.RightDerived.EverywhereDefined :
  (D ⥤ D') → MorphismProperty D → Prop)

/- Definition 13.14.9 (2). In Situation 13.14.1, F is left derivable, or LF is
everywhere defined, if LeftDerived.DefinedAt F S X holds for every X : D. -/
@[stacks 05SV]
#check (CategoryTheory.Functor.LeftDerived.EverywhereDefined :
  (D ⥤ D') → MorphismProperty D → Prop)

/- Pointwise Kan-extension existence follows from the source-definedness conditions. -/
#check @CategoryTheory.Functor.RightDerived.EverywhereDefined.hasPointwise
#check @CategoryTheory.Functor.LeftDerived.EverywhereDefined.hasPointwise

end
