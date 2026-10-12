/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.Computations.Setoids.Action

/-!
# Ordinary coherence computations for setoid-stack inertia

This file records the fields and comparison cells of the ordinary inertia pseudofunctor.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open BasedCategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Setoids.Inertia.pseudofunctor

variable {X Y : StackOver.Setoids.{u, v, w, vS} J}

/-- The ordinary setoid-stack inertia pseudofunctor sends an object to its inertia. -/
@[simp]
theorem obj (X : StackOver.Setoids.{u, v, w, vS} J) :
    (StackOver.Setoids.Inertia.pseudofunctor J).obj X =
      StackOver.Setoids.inertia X := sorry

/-- Its `1`-cell action is the public setoid-stack inertia map. -/
@[simp]
theorem map (F : X ⟶ Y) :
    (StackOver.Setoids.Inertia.pseudofunctor J).map F =
      StackOver.Setoids.inertia.map F := sorry

/-- Its `2`-cell action is the public setoid-stack inertia action. -/
@[simp]
theorem map₂ {F G : X ⟶ Y} (eta : F ⟶ G) :
    (StackOver.Setoids.Inertia.pseudofunctor J).map₂ eta =
      StackOver.Setoids.inertia.map₂ eta := sorry

/-- Its local action is the public setoid-stack inertia Hom functor. -/
@[simp]
theorem mapFunctor (X Y : StackOver.Setoids.{u, v, w, vS} J) :
    (StackOver.Setoids.Inertia.pseudofunctor J).mapFunctor X Y =
      StackOver.Setoids.inertia.mapFunctor X Y := sorry

/-- The forward ordinary identity comparison forgets to the groupoid-stack comparison. -/
@[simp]
theorem mapId.hom (X : StackOver.Setoids.{u, v, w, vS} J) :
    ((StackOver.Setoids.Inertia.pseudofunctor J).mapId X).hom.hom =
      ((StackOver.Groupoids.Inertia.pseudofunctor J).mapId X.toGroupoids).hom := sorry

/-- The inverse ordinary identity comparison forgets to the groupoid-stack comparison. -/
@[simp]
theorem mapId.inv (X : StackOver.Setoids.{u, v, w, vS} J) :
    ((StackOver.Setoids.Inertia.pseudofunctor J).mapId X).inv.hom =
      ((StackOver.Groupoids.Inertia.pseudofunctor J).mapId X.toGroupoids).inv := sorry

/-- The forward ordinary composition comparison forgets to the groupoid-stack comparison. -/
@[simp]
theorem mapComp.hom
    {Z : StackOver.Setoids.{u, v, w, vS} J} (F : X ⟶ Y) (G : Y ⟶ Z) :
    ((StackOver.Setoids.Inertia.pseudofunctor J).mapComp F G).hom.hom =
      ((StackOver.Groupoids.Inertia.pseudofunctor J).mapComp
        (Hom.toGroupoidsMor F) (Hom.toGroupoidsMor G)).hom := sorry

/-- The inverse ordinary composition comparison forgets to the groupoid-stack comparison. -/
@[simp]
theorem mapComp.inv
    {Z : StackOver.Setoids.{u, v, w, vS} J} (F : X ⟶ Y) (G : Y ⟶ Z) :
    ((StackOver.Setoids.Inertia.pseudofunctor J).mapComp F G).inv.hom =
      ((StackOver.Groupoids.Inertia.pseudofunctor J).mapComp
        (Hom.toGroupoidsMor F) (Hom.toGroupoidsMor G)).inv := sorry

end StackOver.Setoids.Inertia.pseudofunctor

end CategoryTheory
