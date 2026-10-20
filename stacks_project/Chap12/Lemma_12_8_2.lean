/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.Localization.Preadditive
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

open MorphismProperty

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteProducts C]
variable (W : MorphismProperty C)

/- Lemma 12.8.2: localization by either calculus of fractions is additive; finite products are the
canonical structure-level owner for the additive-category clause. -/
@[stacks 05QE]
#check MorphismProperty.Localization.hasFiniteProducts W

section Left

variable [W.HasLeftCalculusOfFractions]

#check (inferInstance : Preadditive W.Localization)
#check (inferInstance : W.Q.Additive)
#check (inferInstance : HasFiniteProducts W.Localization)

end Left

section Right

variable [W.HasRightCalculusOfFractions]

#check (inferInstance : Preadditive W.Localization)
#check (inferInstance : W.Q.Additive)
#check (inferInstance : HasFiniteProducts W.Localization)

end Right

end CategoryTheory
