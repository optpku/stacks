/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

-- (no extra Mathlib imports needed)
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Bilimit

import StacksCheckRecall

@[expose] public section


open CategoryTheory
open scoped Bicategory

universe u v

namespace CategoryTheory
namespace BasedCategory

variable {C : Type u} [Category.{v} C]
variable {X Y S : BasedCategory C}
variable (F : X ⟶ S) (G : Y ⟶ S)

namespace PseudoPullback

/- Lemma 4.32.3: for morphisms `F : X ⟶ S` and `G : Y ⟶ S` in `Cat/C`, the square
`PseudoPullback.cone F G` is a `2`-fibre product. Its apex has objects
`(U, x, y, f)` over a common `U : C`; its morphisms are pairs over one map in `C` satisfying the
comparison square; its two legs forget to `x` and `y`; and its comparison is the stored `f`.
Consequently, the bicategory of categories over `C` has these `2`-fibre products. -/
@[stacks 0040]
#check (cone.isBilimit F G : (cone F G).IsBilimit)

end PseudoPullback

end BasedCategory
end CategoryTheory
