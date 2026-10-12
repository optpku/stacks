/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe vC uC vD uD vE uE

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {E : Type uE} [Category.{vE} E]
variable {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D}
variable (adj₁ : F ⊣ G) (adj₂ : H ⊣ I) (X : E)

/- 4.24.9.1: for `adj : u ⊣ v` and `adj' : u' ⊣ v'`, the counit of
`adj'.comp adj : u' ⋙ u ⊣ v ⋙ v'` satisfies, in Lean's arrows-order notation,
`u.map (adj'.counit.app (v.obj X)) ≫ adj.counit.app X = (adj'.comp adj).counit.app X`.
Mathlib's component-level owner `Adjunction.comp_counit_app` records this same equality in the
reverse, simp-oriented direction. Keeping the composite data in `Adjunction.comp` also makes its
canonical simp/reassociation API available without a parallel equation wrapper. -/
@[stacks 0DV1 "counit component formula for a composite adjunction"]
#check (Adjunction.comp_counit_app adj₁ adj₂ X :
  (adj₁.comp adj₂).counit.app X =
    H.map (adj₁.counit.app (I.obj X)) ≫ adj₂.counit.app X)

end CategoryTheory
