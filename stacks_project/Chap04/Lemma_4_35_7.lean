/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
import StacksCheckRecall

@[expose] public section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X₀ Y₀ S₀ : BasedCategory.{v, max w (max u v)} C}
variable (F₀ : X₀ ⥤ᵇ S₀) (G₀ : Y₀ ⥤ᵇ S₀)
variable [Functor.IsFibered.InGroupoids X₀.p]
variable [Functor.IsFibered.InGroupoids Y₀.p]
variable [Functor.IsFibered.InGroupoids S₀.p]

/- Lemma 4.35.7 (1): the pseudo-pullback projection of categories fibred in groupoids is again
fibred in groupoids. The reusable instance is
`BasedCategory.PseudoPullback.Projection.inGroupoids`. -/
@[stacks 0041 "(1)"]
#check (BasedCategory.PseudoPullback.Projection.inGroupoids F₀ G₀ :
  Functor.IsFibered.InGroupoids (BasedCategory.PseudoPullback F₀ G₀).p)

namespace FiberedCategoryOver.Groupoids

variable {X Y S : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
variable (F : X ⟶ S) (G : Y ⟶ S)

/- Lemma 4.35.7 (2): the shared cone on the explicit two-fibre product is a bicategorical
two-fibre product in categories fibred in groupoids over `C`. -/
@[stacks 0041 "(2)"]
#check (CategoryTheory.TwoFibreProduct.cone.isBilimit F G :
  (CategoryTheory.TwoFibreProduct.cone F G).IsBilimit)

end FiberedCategoryOver.Groupoids

end CategoryTheory
