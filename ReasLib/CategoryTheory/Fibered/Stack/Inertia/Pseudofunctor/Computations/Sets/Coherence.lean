/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.Computations.Sets.Action

/-!
# Coherence computations for set-stack inertia

Readouts for the strict and ordinary pseudofunctor fields, including identity and composition
comparison cells.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Sets.Inertia.strictPseudofunctor

variable {X Y : StackOver.Sets.{u, v, w, vS} J}

/-- The strict set-stack inertia pseudofunctor sends an object to its bundled inertia. -/
@[simp]
theorem obj (X : StackOver.Sets.{u, v, w, vS} J) :
    (StackOver.Sets.Inertia.strictPseudofunctor J).obj X =
      StackOver.Sets.inertia X := sorry

/-- Its `1`-cell field is the public set-stack inertia map. -/
@[simp]
theorem map (F : X ⟶ Y) :
    (StackOver.Sets.Inertia.strictPseudofunctor J).map F =
      StackOver.Sets.inertia.map F := sorry

/-- Its `2`-cell field is the public set-stack inertia action. -/
@[simp]
theorem map₂ {F G : X ⟶ Y} (eta : F ⟶ G) :
    (StackOver.Sets.Inertia.strictPseudofunctor J).map₂ eta =
      StackOver.Sets.inertia.map₂ eta := sorry

/-- Its local action is the public set-stack inertia Hom functor. -/
@[simp]
theorem mapFunctor (X Y : StackOver.Sets.{u, v, w, vS} J) :
    (StackOver.Sets.Inertia.strictPseudofunctor J).mapFunctor X Y =
      StackOver.Sets.inertia.mapFunctor X Y := sorry

/-- The forward strict identity comparison forgets to the setoid-stack comparison. -/
@[simp]
theorem mapId.hom (X : StackOver.Sets.{u, v, w, vS} J) :
    ((StackOver.Sets.Inertia.strictPseudofunctor J).mapId X).hom.hom =
      ((StackOver.Setoids.Inertia.strictPseudofunctor J).mapId X.toSetoids).hom := sorry

/-- The inverse strict identity comparison forgets to the setoid-stack comparison. -/
@[simp]
theorem mapId.inv (X : StackOver.Sets.{u, v, w, vS} J) :
    ((StackOver.Sets.Inertia.strictPseudofunctor J).mapId X).inv.hom =
      ((StackOver.Setoids.Inertia.strictPseudofunctor J).mapId X.toSetoids).inv := sorry

/-- The forward strict composition comparison forgets to the setoid-stack comparison. -/
@[simp]
theorem mapComp.hom
    {Z : StackOver.Sets.{u, v, w, vS} J} (F : X ⟶ Y) (G : Y ⟶ Z) :
    ((StackOver.Sets.Inertia.strictPseudofunctor J).mapComp F G).hom.hom =
      ((StackOver.Setoids.Inertia.strictPseudofunctor J).mapComp
        (StackOver.Sets.Hom.toSetoidsMor F)
        (StackOver.Sets.Hom.toSetoidsMor G)).hom := sorry

/-- The inverse strict composition comparison forgets to the setoid-stack comparison. -/
@[simp]
theorem mapComp.inv
    {Z : StackOver.Sets.{u, v, w, vS} J} (F : X ⟶ Y) (G : Y ⟶ Z) :
    ((StackOver.Sets.Inertia.strictPseudofunctor J).mapComp F G).inv.hom =
      ((StackOver.Setoids.Inertia.strictPseudofunctor J).mapComp
        (StackOver.Sets.Hom.toSetoidsMor F)
        (StackOver.Sets.Hom.toSetoidsMor G)).inv := sorry

end StackOver.Sets.Inertia.strictPseudofunctor

namespace StackOver.Sets.Inertia.pseudofunctor

variable {X Y : StackOver.Sets.{u, v, w, vS} J}

/-- The ordinary set-stack inertia pseudofunctor sends an object to its bundled inertia. -/
@[simp]
theorem obj (X : StackOver.Sets.{u, v, w, vS} J) :
    (StackOver.Sets.Inertia.pseudofunctor J).obj X =
      StackOver.Sets.inertia X := sorry

/-- Its `1`-cell action is the public set-stack inertia map. -/
@[simp]
theorem map (F : X ⟶ Y) :
    (StackOver.Sets.Inertia.pseudofunctor J).map F =
      StackOver.Sets.inertia.map F := sorry

/-- Its `2`-cell action is the public set-stack inertia action. -/
@[simp]
theorem map₂ {F G : X ⟶ Y} (eta : F ⟶ G) :
    (StackOver.Sets.Inertia.pseudofunctor J).map₂ eta =
      StackOver.Sets.inertia.map₂ eta := sorry

/-- Its local action is the public set-stack inertia Hom functor. -/
@[simp]
theorem mapFunctor (X Y : StackOver.Sets.{u, v, w, vS} J) :
    (StackOver.Sets.Inertia.pseudofunctor J).mapFunctor X Y =
      StackOver.Sets.inertia.mapFunctor X Y := sorry

/-- The forward ordinary identity comparison forgets to the setoid-stack comparison. -/
@[simp]
theorem mapId.hom (X : StackOver.Sets.{u, v, w, vS} J) :
    ((StackOver.Sets.Inertia.pseudofunctor J).mapId X).hom.hom =
      ((StackOver.Setoids.Inertia.pseudofunctor J).mapId X.toSetoids).hom := sorry

/-- The inverse ordinary identity comparison forgets to the setoid-stack comparison. -/
@[simp]
theorem mapId.inv (X : StackOver.Sets.{u, v, w, vS} J) :
    ((StackOver.Sets.Inertia.pseudofunctor J).mapId X).inv.hom =
      ((StackOver.Setoids.Inertia.pseudofunctor J).mapId X.toSetoids).inv := sorry

/-- The forward ordinary composition comparison forgets to the setoid-stack comparison. -/
@[simp]
theorem mapComp.hom
    {Z : StackOver.Sets.{u, v, w, vS} J} (F : X ⟶ Y) (G : Y ⟶ Z) :
    ((StackOver.Sets.Inertia.pseudofunctor J).mapComp F G).hom.hom =
      ((StackOver.Setoids.Inertia.pseudofunctor J).mapComp
        (StackOver.Sets.Hom.toSetoidsMor F)
        (StackOver.Sets.Hom.toSetoidsMor G)).hom := sorry

/-- The inverse ordinary composition comparison forgets to the setoid-stack comparison. -/
@[simp]
theorem mapComp.inv
    {Z : StackOver.Sets.{u, v, w, vS} J} (F : X ⟶ Y) (G : Y ⟶ Z) :
    ((StackOver.Sets.Inertia.pseudofunctor J).mapComp F G).inv.hom =
      ((StackOver.Setoids.Inertia.pseudofunctor J).mapComp
        (StackOver.Sets.Hom.toSetoidsMor F)
        (StackOver.Sets.Hom.toSetoidsMor G)).inv := sorry

end StackOver.Sets.Inertia.pseudofunctor

end CategoryTheory
