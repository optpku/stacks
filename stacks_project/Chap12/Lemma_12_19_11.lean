/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Strict.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory.FilteredObject.Hom

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A B D : FilteredObject C} (f : B ⟶ A) (g : D ⟶ A)

/- Lemma 12.19.11 [05SN]: the standard filtered pullback exists. -/
@[stacks 05SN]
#check (inferInstance : HasPullback f g)

/- Lemma 12.19.11 [05SN]: its canonical second projection preserves strictness. -/
@[stacks 05SN]
#check (strict_pullback_snd_of_strict f g : Strict f → Strict (pullback.snd f g))

end CategoryTheory.FilteredObject.Hom
