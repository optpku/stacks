/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Fiber.Equivalence
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoricalPullback

universe u v uX uY uS vX vY vS

namespace CategoryTheory.BasedCategory.PseudoPullback.Fiber

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}
variable (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (U : C)

/- Lemma 4.32.5: for morphisms of categories over `C`, the fibre over `U` of the bundled
`2`-fibre-product category over `C` is canonically equivalent to the pullback of the fibre
categories. The reusable owner is `BasedCategory.PseudoPullback.Fiber.comparison.equivalence`. -/
@[stacks 02XI]
#check (CategoryTheory.BasedCategory.PseudoPullback.Fiber.comparison.equivalence F G U :
  Functor.Fiber (PseudoPullback F G).p U ≌
    ((F.fiberFunctor U) ⊡ (G.fiberFunctor U)))

end CategoryTheory.BasedCategory.PseudoPullback.Fiber
