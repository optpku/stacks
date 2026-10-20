/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Equivalence.Fiberedness
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory
namespace BasedCategory

universe v u vS uS

variable {C : Type u} [Category.{v} C]
variable {X Y : BasedCategory.{vS, uS} C}
variable (e : CategoryTheory.Bicategory.Equivalence X Y)

/- Lemma 4.33.8: equivalent objects of the fixed `2`-category `BasedCategory C` are simultaneously
fibred over `C`. The statement retains the canonical bicategorical equivalence object `X ≌ Y`;
`BasedFunctor.IsEquivalence` and `BasedFunctor.asEquivalence` provide the corresponding
property/choice API when a particular based functor is fixed. -/
@[stacks 042G]
#check (Equivalence.isFibered_iff e : X.p.IsFibered ↔ Y.p.IsFibered)

end BasedCategory
end CategoryTheory
