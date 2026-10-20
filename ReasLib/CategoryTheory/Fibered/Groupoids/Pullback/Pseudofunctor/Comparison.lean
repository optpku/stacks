/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Pullback.Pseudofunctor.Action
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison computations for fixed-base pullback in groupoids

This leaf gives stable names to the identity and composition comparisons and records both their
ambient based-natural-transformation projections and the factorization through the based-category
valued pseudofunctor.
-/

@[expose] public section

noncomputable section

universe uC uD uS vC vD vS

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

namespace FiberedCategoryOver.Groupoids.Pullback

variable (u : C ⥤ D)

/-- The forward identity comparison forgets to the forward comparison of the ambient
based-category-valued pseudofunctor. -/
@[simp]
theorem pseudofunctor.mapId.hom.toBasedNatTrans
    (X : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D) :
    ((pseudofunctor u).mapId X).hom.hom =
      ((ambient u).mapId X).hom := sorry

/-- The inverse identity comparison forgets to the inverse comparison of the ambient
based-category-valued pseudofunctor. -/
@[simp]
theorem pseudofunctor.mapId.inv.toBasedNatTrans
    (X : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D) :
    ((pseudofunctor u).mapId X).inv.hom =
      ((ambient u).mapId X).inv := sorry

/-- The forward composition comparison forgets to the forward comparison of the ambient
based-category-valued pseudofunctor. -/
@[simp]
theorem pseudofunctor.mapComp.hom.toBasedNatTrans
    {X Y Z : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    ((pseudofunctor u).mapComp F G).hom.hom =
      ((ambient u).mapComp F G).hom := sorry

/-- The inverse composition comparison forgets to the inverse comparison of the ambient
based-category-valued pseudofunctor. -/
@[simp]
theorem pseudofunctor.mapComp.inv.toBasedNatTrans
    {X Y Z : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    ((pseudofunctor u).mapComp F G).inv.hom =
      ((ambient u).mapComp F G).inv := sorry

/-- Forgetting the groupoid-fibre membership after fixed-base pullback recovers the ambient
based-category-valued pullback pseudofunctor, including all comparison data. -/
theorem pseudofunctor.comp_toBased :
    (pseudofunctor u).comp
        (FiberedCategoryOver.Groupoids.toBased C).toPseudofunctor =
      ambient u := sorry

end FiberedCategoryOver.Groupoids.Pullback

end CategoryTheory
