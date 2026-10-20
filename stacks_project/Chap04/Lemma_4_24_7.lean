/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe vC uC vD uD

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
variable (X : C) (Y : D)

/- The source's two objectwise composites are exactly the defining triangle fields of
`Adjunction`: for `adj : u ⊣ v` they state
`u.map (adj.unit.app X) ≫ adj.counit.app (u.obj X) = 𝟙 (u.obj X)` and
`adj.unit.app (v.obj Y) ≫ v.map (adj.counit.app Y) = 𝟙 (v.obj Y)`.
Thus no local wrapper is needed. The derived natural-transformation theorems
`Adjunction.left_triangle` and `Adjunction.right_triangle` encode the same identities at the
bundled level, where associators and unitors must be displayed; the component fields are the
more faithful and lighter source-facing API. `Adjunction.Basic` is public because these recalled
fields are this item's exported mathematics, whereas `StacksCheckRecall` is a plain import used
only by the recall command. -/

/- Lemma 4.24.7 (1): for `X` in the source category, applying the left adjoint to the unit at
`X` and then the counit at its image is the identity. -/
@[stacks 0GLL "left triangle identity on an object of the source category"]
#check (adj.left_triangle_components X :
  L.map (adj.unit.app X) ≫ adj.counit.app (L.obj X) = 𝟙 (L.obj X))

/- Lemma 4.24.7 (2): for `Y` in the target category, the unit at its image under the right
adjoint followed by the right adjoint applied to the counit at `Y` is the identity. -/
@[stacks 0GLL "right triangle identity on an object of the target category"]
#check (adj.right_triangle_components Y :
  adj.unit.app (R.obj Y) ≫ R.map (adj.counit.app Y) = 𝟙 (R.obj Y))

end CategoryTheory
