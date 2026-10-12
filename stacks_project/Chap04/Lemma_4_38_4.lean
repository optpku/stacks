/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Fibered.Sets.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit

@[expose] public section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace BasedCategory.PseudoPullback

variable {X Y S : BasedCategory.{v, max w (max u v)} C}
variable (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
variable [Functor.IsDiscreteFibration X.p]
variable [Functor.IsDiscreteFibration Y.p]
variable [Functor.IsDiscreteFibration S.p]

/- Lemma 4.38.4 (1): the explicit pseudo-pullback projection of categories fibred in sets is
again fibred in sets. -/
@[stacks 0047 "(1)"]
#check (BasedCategory.PseudoPullback.Projection.inSets F G :
  Functor.IsDiscreteFibration (BasedCategory.PseudoPullback F G).p)

end BasedCategory.PseudoPullback

namespace FiberedCategoryOver.Sets

variable {X Y S : Sets.{u, v, max w (max u v), v} C}
variable (F : X ⟶ S) (G : Y ⟶ S)

/- Lemma 4.38.4 (2): the common cone on the explicit two-fibre product is a bicategorical
two-fibre product in categories fibred in sets. -/
@[stacks 0047 "(2)"]
#check (CategoryTheory.TwoFibreProduct.cone.isBilimit F G :
  (CategoryTheory.TwoFibreProduct.cone F G).IsBilimit)

end FiberedCategoryOver.Sets

end CategoryTheory
