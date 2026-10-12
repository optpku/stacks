/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.Computations.Groupoids.Action

/-!
# Strict coherence computations for groupoid-stack inertia

This file records the fields and comparison cells of the strict inertia pseudofunctor.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open BasedCategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Groupoids.Inertia.strictPseudofunctor

variable {X Y : StackOver.Groupoids.{u, v, w, vS} J}

/-- The strict groupoid-stack inertia pseudofunctor sends an object to its inertia. -/
@[simp]
theorem obj (X : StackOver.Groupoids.{u, v, w, vS} J) :
    (StackOver.Groupoids.Inertia.strictPseudofunctor J).obj X =
      StackOver.Groupoids.inertia X := sorry

/-- Its `1`-cell field is the public groupoid-stack inertia map. -/
@[simp]
theorem map (F : X ⟶ Y) :
    (StackOver.Groupoids.Inertia.strictPseudofunctor J).map F =
      StackOver.Groupoids.inertia.map F := sorry

/-- Its `2`-cell field is the public groupoid-stack inertia action. -/
@[simp]
theorem map₂ {F G : X ⟶ Y} (eta : F ⟶ G) :
    (StackOver.Groupoids.Inertia.strictPseudofunctor J).map₂ eta =
      StackOver.Groupoids.inertia.map₂ eta := sorry

/-- Its local action is the public groupoid-stack inertia Hom functor. -/
@[simp]
theorem mapFunctor (X Y : StackOver.Groupoids.{u, v, w, vS} J) :
    (StackOver.Groupoids.Inertia.strictPseudofunctor J).mapFunctor X Y =
      StackOver.Groupoids.inertia.mapFunctor X Y := sorry

/-- The forward strict identity comparison forgets to the groupoid-fibred comparison. -/
@[simp]
theorem mapId.hom (X : StackOver.Groupoids.{u, v, w, vS} J) :
    ((StackOver.Groupoids.Inertia.strictPseudofunctor J).mapId X).hom.hom =
      ((FiberedCategoryOver.Groupoids.Inertia.strictPseudofunctor C).mapId
        X.toGroupoids).hom := sorry

/-- The inverse strict identity comparison forgets to the groupoid-fibred comparison. -/
@[simp]
theorem mapId.inv (X : StackOver.Groupoids.{u, v, w, vS} J) :
    ((StackOver.Groupoids.Inertia.strictPseudofunctor J).mapId X).inv.hom =
      ((FiberedCategoryOver.Groupoids.Inertia.strictPseudofunctor C).mapId
        X.toGroupoids).inv := sorry

/-- The forward strict composition comparison forgets to the groupoid-fibred comparison. -/
@[simp]
theorem mapComp.hom
    {Z : StackOver.Groupoids.{u, v, w, vS} J} (F : X ⟶ Y) (G : Y ⟶ Z) :
    ((StackOver.Groupoids.Inertia.strictPseudofunctor J).mapComp F G).hom.hom =
      ((FiberedCategoryOver.Groupoids.Inertia.strictPseudofunctor C).mapComp
        (Hom.toGroupoidsMor F) (Hom.toGroupoidsMor G)).hom := sorry

/-- The inverse strict composition comparison forgets to the groupoid-fibred comparison. -/
@[simp]
theorem mapComp.inv
    {Z : StackOver.Groupoids.{u, v, w, vS} J} (F : X ⟶ Y) (G : Y ⟶ Z) :
    ((StackOver.Groupoids.Inertia.strictPseudofunctor J).mapComp F G).inv.hom =
      ((FiberedCategoryOver.Groupoids.Inertia.strictPseudofunctor C).mapComp
        (Hom.toGroupoidsMor F) (Hom.toGroupoidsMor G)).inv := sorry

end StackOver.Groupoids.Inertia.strictPseudofunctor

end CategoryTheory
