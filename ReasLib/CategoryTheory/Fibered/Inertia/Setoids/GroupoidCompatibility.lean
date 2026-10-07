module

public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.AbsoluteTransformations.Maps
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Maps

/-!
# Compatibility of setoid-fibred and groupoid-fibred inertia

The forgetful strict pseudofunctor from setoid-fibred to groupoid-fibred
categories preserves the absolute and relative inertia constructions.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.Setoids

open scoped Bicategory Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

variable {X Y :
  FiberedCategoryOver.Setoids.{u, v, w, vS} C}

/-- Forgetting the thin-fibre refinement from setoid-fibred relative inertia recovers the
canonical groupoid-fibred relative-inertia owner. -/
@[simp]
theorem relativeInertia.toGroupoids (F : X ⟶ Y) :
    (FiberedCategoryOver.Setoids.toGroupoids C).obj
        (relativeInertia F) =
      FiberedCategoryOver.Groupoids.relativeInertia
        ((FiberedCategoryOver.Setoids.toGroupoids C).map F) := sorry

/-- Forgetting the thin-fibre refinement from setoid-fibred absolute inertia recovers the
canonical groupoid-fibred absolute-inertia owner. -/
@[simp]
theorem inertia.toGroupoids
    (X : FiberedCategoryOver.Setoids.{u, v, w, vS} C) :
    (FiberedCategoryOver.Setoids.toGroupoids C).obj (inertia X) =
      FiberedCategoryOver.Groupoids.inertia
        ((FiberedCategoryOver.Setoids.toGroupoids C).obj X) := sorry

/-- Setoid-fibred strict inertia is compatible with forgetting thinness to the groupoid-fibred
owner. -/
@[simp]
theorem Inertia.strictPseudofunctor.comp_toGroupoids :
    (Inertia.strictPseudofunctor.{u, v, vS, w} C).comp
        (FiberedCategoryOver.Setoids.toGroupoids C :
          StrictPseudofunctor
            (FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C)
            (FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C)) =
      (FiberedCategoryOver.Setoids.toGroupoids C :
          StrictPseudofunctor
            (FiberedCategoryOver.Setoids.{u, v, w, vS} C)
            (FiberedCategoryOver.Groupoids.{u, v, w, vS} C)).comp
        (FiberedCategoryOver.Groupoids.Inertia.strictPseudofunctor.{u, v, vS, w}
          C) := sorry

/-- Setoid-fibred inertia is compatible with forgetting thinness to the ordinary
groupoid-fibred inertia pseudofunctor. -/
@[simp]
theorem Inertia.pseudofunctor.comp_toGroupoids :
    (Inertia.pseudofunctor.{u, v, vS, w} C).comp
        ((FiberedCategoryOver.Setoids.toGroupoids C :
          StrictPseudofunctor
            (FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C)
            (FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C)).toPseudofunctor) =
      ((FiberedCategoryOver.Setoids.toGroupoids C :
          StrictPseudofunctor
            (FiberedCategoryOver.Setoids.{u, v, w, vS} C)
            (FiberedCategoryOver.Groupoids.{u, v, w, vS} C)).toPseudofunctor).comp
        (FiberedCategoryOver.Groupoids.Inertia.pseudofunctor.{u, v, vS, w}
          C) := sorry

/-- Forgetting thinness from the setoid-fibred inertia forgetful morphism recovers the
groupoid-fibred forgetful morphism. -/
@[simp]
theorem Inertia.forget.toGroupoids
    (X : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C) :
    (FiberedCategoryOver.Setoids.toGroupoids C :
        StrictPseudofunctor
          (FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C)
          (FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C)).map
        (Inertia.forget.{u, v, vS, w} X) =
      FiberedCategoryOver.Groupoids.Inertia.forget.{u, v, vS, w}
        ((FiberedCategoryOver.Setoids.toGroupoids C).obj X) := sorry

/-- Forgetting thinness from the setoid-fibred identity section recovers the groupoid-fibred
identity section. -/
@[simp]
theorem Inertia.identitySection.toGroupoids
    (X : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C) :
    (FiberedCategoryOver.Setoids.toGroupoids C :
        StrictPseudofunctor
          (FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C)
          (FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C)).map
        (Inertia.identitySection.{u, v, vS, w} X) =
      FiberedCategoryOver.Groupoids.Inertia.identitySection.{u, v, vS, w}
        ((FiberedCategoryOver.Setoids.toGroupoids C).obj X) := sorry

end FiberedCategoryOver.Setoids

end CategoryTheory
