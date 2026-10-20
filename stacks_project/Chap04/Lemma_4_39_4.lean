/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Fibered.Setoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit

@[expose] public section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X₀ Y₀ S₀ : BasedCategory.{v, max w (max u v)} C}
variable (F₀ : X₀ ⥤ᵇ S₀) (G₀ : Y₀ ⥤ᵇ S₀)
variable [Functor.IsFibered.InSetoids X₀.p]
variable [Functor.IsFibered.InSetoids Y₀.p]
variable [Functor.IsFibered.InGroupoids S₀.p]

namespace FiberedCategoryOver.Setoids

variable {X Y S : Setoids.{u, v, max w (max u v), v} C}
variable (F : X ⟶ S) (G : Y ⟶ S)

/- Lemma 4.39.4 (1): the projection from the explicit two-fibre product of categories fibred in
setoids is again fibred in setoids. -/
@[stacks 04SB "(1)"]
#check (BasedCategory.PseudoPullback.Projection.InSetoids.ofGroupoidTarget F₀ G₀ :
  Functor.IsFibered.InSetoids (BasedCategory.PseudoPullback F₀ G₀).p)

/- Lemma 4.39.4 (2): the common cone on that explicit two-fibre product is a bicategorical
two-fibre product in categories fibred in setoids. -/
@[stacks 04SB "(2)"]
#check (CategoryTheory.TwoFibreProduct.cone.isBilimit F G :
  (CategoryTheory.TwoFibreProduct.cone F G).IsBilimit)

end FiberedCategoryOver.Setoids

end CategoryTheory
