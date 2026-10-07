module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Pullback.Pseudofunctor.Action
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison computations for fixed-base pullback on stacks in groupoids

This leaf gives stable names to the identity and composition comparisons and records their
projections to groupoid-fibred natural transformations and the ambient factorization law.
-/

@[expose] public section

noncomputable section

universe uC uD uS vC vD vS

namespace CategoryTheory

open Bicategory Limits
open scoped Bicategory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace StackOver.Groupoids.Pullback

variable (u : C ⥤ D)
variable [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] [u.IsContinuous J K]

/-- The forward identity comparison forgets to the forward identity comparison of the ambient
groupoid-fibred-valued pseudofunctor. -/
@[simp, stacks 04WD "groupoid-stack pullback identity comparison forward map"]
theorem pseudofunctor.mapId.hom.toAmbient
    (X : StackOver.Groupoids.{uD, vD, uS, vS} K) :
    ((pseudofunctor J K u).mapId X).hom.hom =
      ((ambient K u).mapId X).hom := sorry

/-- The inverse identity comparison forgets to the inverse identity comparison of the ambient
groupoid-fibred-valued pseudofunctor. -/
@[simp, stacks 04WD "groupoid-stack pullback identity comparison inverse map"]
theorem pseudofunctor.mapId.inv.toAmbient
    (X : StackOver.Groupoids.{uD, vD, uS, vS} K) :
    ((pseudofunctor J K u).mapId X).inv.hom =
      ((ambient K u).mapId X).inv := sorry

/-- The forward composition comparison forgets to the forward composition comparison of the
ambient groupoid-fibred-valued pseudofunctor. -/
@[simp, stacks 04WD "groupoid-stack pullback composition comparison forward map"]
theorem pseudofunctor.mapComp.hom.toAmbient
    {X Y Z : StackOver.Groupoids.{uD, vD, uS, vS} K}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    ((pseudofunctor J K u).mapComp F G).hom.hom =
      ((ambient K u).mapComp F G).hom := sorry

/-- The inverse composition comparison forgets to the inverse composition comparison of the
ambient groupoid-fibred-valued pseudofunctor. -/
@[simp, stacks 04WD "groupoid-stack pullback composition comparison inverse map"]
theorem pseudofunctor.mapComp.inv.toAmbient
    {X Y Z : StackOver.Groupoids.{uD, vD, uS, vS} K}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    ((pseudofunctor J K u).mapComp F G).inv.hom =
      ((ambient K u).mapComp F G).inv := sorry

/-- Forgetting the stack condition after fixed-base pullback recovers the ambient
groupoid-fibred-valued pullback pseudofunctor, including all comparison data. -/
@[stacks 04WD "groupoid-stack pullback ambient factorization"]
theorem pseudofunctor.comp_forget :
    (pseudofunctor J K u).comp
        (StackOver.Groupoids.forget J).toPseudofunctor =
      ambient K u := sorry

end StackOver.Groupoids.Pullback

end CategoryTheory
