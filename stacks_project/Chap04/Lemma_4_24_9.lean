/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
import StacksCheckRecall

@[expose] public section

universe vC uC vD uD vE uE

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {E : Type uE} [Category.{vE} E]
variable {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D}
variable (adj₁ : F ⊣ G) (adj₂ : H ⊣ I)

/- `CategoryTheory.Adjunction.comp` is the exact canonical owner. Given
`adj' : u' ⊣ v'` and `adj : u ⊣ v`, the term `adj'.comp adj` has type
`u' ⋙ u ⊣ v ⋙ v'`, exactly the source adjunction in Lean's arrows-order notation.
The explicit counit component formula is recalled separately in
`4_24_9_1.lean`, so no local wrapper or ambient universe/category parameters belong here. -/

/- Lemma 4.24.9 (1): if `v : A ⥤ B` and `v' : B ⥤ C` have left adjoints `u` and `u'`
respectively, then the composite `v ⋙ v'` has left adjoint `u' ⋙ u`. This is exactly the canonical
mathlib construction `Adjunction.comp`. The counit formula in part (2) is the separate item
`4.24.9.1`. -/
@[stacks 0DV0 "composite adjunction from composable adjunctions"]
#check (adj₁.comp adj₂ : F ⋙ H ⊣ I ⋙ G)

end CategoryTheory
